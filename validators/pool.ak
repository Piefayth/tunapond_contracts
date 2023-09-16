use aiken/bytearray
use aiken/transaction.{ScriptContext, OutputReference, Transaction, Mint, Spend, InlineDatum, find_input}
use aiken/hash.{Blake2b_224, Hash}
use aiken/transaction/credential.{VerificationKey, Script, ScriptCredential}
use aiken/transaction/value
use aiken/list
use aiken/dict

type VerificationKeyHash =
  Hash<Blake2b_224, VerificationKey>

type ScriptHash =
  Hash<Blake2b_224, Script>


type Bank {
  owners: List<(VerificationKeyHash, Int)>
}

type SpendAction {
  Mine
  Redeem
}

const pool_master_token_name: ByteArray = #"504f4f4c"
const pool_bank_token_name: ByteArray = #"42414e4b"
const tuna_master_token_name: ByteArray = #"6c6f72642074756e61"
const tuna_token_name: ByteArray = #"54554e41"

validator(registration_utxo_ref: OutputReference, tuna_policy: ScriptHash) {
  fn spend(_d: Bank, redeemer: SpendAction, ctx: ScriptContext) -> Bool {
    let ScriptContext { transaction, purpose } = ctx

    expect Spend(spent_utxo_ref) = purpose
    
    when redeemer is {
        Mine -> {
            // collect a block reward and distribute it to miner account balances
            mine(transaction, spent_utxo_ref, tuna_policy)
        }
        Redeem -> {
            // collect from a miner account balance
            redeem(transaction, spent_utxo_ref, tuna_policy)
        }
    }
  }

  fn mint(_redeemer: Data, ctx: ScriptContext) -> Bool {
    let ScriptContext { transaction, purpose } = ctx
    let Transaction { inputs, outputs, mint, .. } = transaction

    expect Mint(own_policy) = purpose

    // Must spend the contract's registration utxo to guarantee a one time mint
    // This is an artbirary utxo for now, but it could have data if we wanted.
    expect Some(_) = list.find(inputs, 
      fn(input) { 
        input.output_reference.transaction_id == registration_utxo_ref.transaction_id && 
        input.output_reference.output_index == registration_utxo_ref.output_index
      }
    )

    // Must only mint one NFT and one bank token
    expect 1 = mint
      |> value.from_minted_value
      |> value.quantity_of(own_policy, pool_master_token_name)
    
    expect 1 = mint
      |> value.from_minted_value
      |> value.quantity_of(own_policy, pool_bank_token_name)

    // The bank token must go to the contract address
    expect Some(bank_output) = list.find(outputs, fn (output) {
      let has_bank_token = value.quantity_of(output.value, own_policy, pool_bank_token_name) == 1
      
      let is_to_this_script = when output.address.payment_credential is {
        ScriptCredential(script_credential) -> {
          script_credential == own_policy
        }
        _ -> False
      } 

      is_to_this_script && has_bank_token
    })

    // Sanity check that the datum placed at the bank utxo is readable
    expect InlineDatum(output_bank_datum) = bank_output.datum
    expect _: Bank = output_bank_datum  

    True
  }

}

fn mine(transaction: Transaction, spent_utxo_ref: OutputReference, tuna_policy: ScriptHash) {
  let Transaction { inputs, outputs, .. } = transaction

  expect Some(spent_input) = inputs |> find_input(spent_utxo_ref)

  let own_address = spent_input.output.address

  expect ScriptCredential(own_validator_hash) = own_address.payment_credential

  // Verify this is a mining transaction (spends the tuna policy master NFT)
  expect list.any(inputs, fn (input) {
    value.quantity_of(input.output.value, tuna_policy, tuna_master_token_name) == 1
  })

  // Transaction must be spending this contract's master token
  expect Some(_) = list.find(inputs, fn (input) {
      value.quantity_of(input.output.value, own_validator_hash, pool_master_token_name) == 1
  })

  // Transaction must be spending the bank
  expect Some(bank_input) = list.find(inputs, fn (input) {
    value.quantity_of(input.output.value, own_validator_hash, pool_bank_token_name) == 1
  })

  // Identify the bank output by the pool bank token
  expect Some(bank_output) = list.find(outputs, fn (output) {
    value.quantity_of(output.value, own_validator_hash, pool_bank_token_name) == 1
  })

  // Bank must be being paid back into this contract
  expect bank_output.address == own_address

  // The input with the bank NFT must contain the bank datum...
  expect InlineDatum(input_bank_datum) = bank_input.output.datum
  expect input_bank_data: Bank = input_bank_datum  

  // ...as does the output.
  expect InlineDatum(output_bank_datum) = bank_output.datum
  expect output_bank_data: Bank = output_bank_datum  

  let old_bank = dict.from_ascending_list(input_bank_data.owners, bytearray.compare)
  let new_bank = dict.from_ascending_list(output_bank_data.owners, bytearray.compare)

  // All members of the input must be in the output
  // But there can be members of the output that were not in the input
  // So if we union the output (left) to the input (right), we should get exactly the output (with the output values in the result)
  let output_union = dict.union_with(
    new_bank, 
    old_bank, 
    fn (_vkh, new_amount, old_amount) {
      // Can only increase a miner's account balance
      expect new_amount >= old_amount

      Some(new_amount)
    }, 
    bytearray.compare
  )

  // The union of input members to output members did not add any members to the output.
  expect dict.size(output_union) == dict.size(new_bank)

  let bank_input_tuna = value.quantity_of(bank_input.output.value, tuna_policy, tuna_token_name)
  let bank_output_tuna = value.quantity_of(bank_output.value, tuna_policy, tuna_token_name)

  let input_amount = dict.foldr(old_bank, 0, fn (_vkh, amount, sum) {
    amount + sum
  })

  let output_amount = dict.foldr(new_bank, 0, fn (_vkh, amount, sum) {
    amount + sum
  })

  // Can't have modified the accounts by more tuna than was exchanged from the bank
  // Note for later - the difference between these amounts and the reward amount is the fee taken by the pool
  expect (bank_output_tuna - bank_input_tuna) == (output_amount - input_amount)

  True
}

fn redeem(transaction: Transaction, spent_utxo_ref: OutputReference, tuna_policy: ByteArray) {
  let redemption_fee = 2_000_000

  let Transaction { inputs, reference_inputs, outputs, .. } = transaction

  expect Some(spent_input) = inputs |> find_input(spent_utxo_ref)

  let own_address = spent_input.output.address
  expect ScriptCredential(own_validator_hash) = own_address.payment_credential

  // Must have a reference input to the pool's master token...
  expect Some(master_input_ref) = list.find(reference_inputs, fn (input) {
    1 == value.quantity_of(input.output.value, own_validator_hash, pool_master_token_name)
  })

  // ...so the contract can verify that the address that owns the token got paid the redemption fee
  expect list.any(outputs, fn (output) {
    output.address == master_input_ref.output.address && 
    value.lovelace_of(output.value) >= redemption_fee
  })

  // Transaction must be spending the bank
  expect Some(bank_input) = list.find(inputs, fn (input) {
    value.quantity_of(input.output.value, own_validator_hash, pool_bank_token_name) == 1
  })

  // Identify the bank output by the pool bank token
  expect Some(bank_output) = list.find(outputs, fn (output) {
    value.quantity_of(output.value, own_validator_hash, pool_bank_token_name) == 1
  })

  // Bank must be being paid back into this contract
  expect bank_output.address == own_address

  // The input with the pool NFT must contain the bank datum...
  expect InlineDatum(input_bank_datum) = bank_input.output.datum
  expect input_bank_data: Bank = input_bank_datum  

  // ...as does the output.
  expect InlineDatum(output_bank_datum) = bank_output.datum
  expect output_bank_data: Bank = output_bank_datum  

  let old_bank = dict.from_ascending_list(input_bank_data.owners, bytearray.compare)
  let new_bank = dict.from_ascending_list(output_bank_data.owners, bytearray.compare)

  let output_union = dict.union_with(
    new_bank, 
    old_bank, 
    fn (vkh, new_amount, old_amount) {
      // Can only change the balances of accounts that have signed this transaction
      if (!list.has(transaction.extra_signatories, vkh)) {
        expect new_amount == old_amount
        Some(new_amount)
      } else {
        Some(new_amount)
      }
    }, 
    bytearray.compare
  )

  // The union of input members to output members did not add any members to the output.
  expect dict.size(output_union) == dict.size(new_bank)

  let bank_input_tuna = value.quantity_of(bank_input.output.value, tuna_policy, tuna_token_name)
  let bank_output_tuna = value.quantity_of(bank_output.value, tuna_policy, tuna_token_name)

  let input_amount = dict.foldr(old_bank, 0, fn (_vkh, amount, sum) {
    amount + sum
  })

  let output_amount = dict.foldr(new_bank, 0, fn (_vkh, amount, sum) {
    amount + sum
  })

  // Can't have modified the accounts by more tuna than was exchanged from the bank
  expect (bank_output_tuna - bank_input_tuna) == (output_amount - input_amount)

  True
}
