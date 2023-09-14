use aiken/transaction.{ScriptContext, OutputReference, Transaction, Mint, Spend, InlineDatum, find_input, find_script_outputs}
use aiken/hash.{Blake2b_224, Hash}
use aiken/transaction/credential.{VerificationKey, Script, ScriptCredential}
use aiken/transaction/value
use aiken/list

type VerificationKeyHash =
  Hash<Blake2b_224, VerificationKey>

type ScriptHash =
  Hash<Blake2b_224, Script>

type OwnerData {
  owner_vkh: VerificationKeyHash
}

type SpendAction {
  Mine
  Redeem
}

const pool_master_token_name: ByteArray = #"504f4f4c"
const tuna_master_token_name: ByteArray = #"6c6f72642074756e61"
const tuna_token_name: ByteArray = #"54554e41"

validator(registration_utxo_ref: OutputReference, tuna_policy: ScriptHash) {
  fn spend(_d: Data, redeemer: SpendAction, ctx: ScriptContext) -> Bool {
    let ScriptContext { transaction, purpose } = ctx

    expect Spend(spent_utxo_ref) = purpose
    when redeemer is {
        Mine -> {
            // collect a block reward and distribute it to miner account balances
            mine(transaction, spent_utxo_ref, tuna_policy)
        }
        Redeem -> {
            // collect from a miner account balance
            redeem(transaction, spent_utxo_ref)
        }
    }
  }

  fn mint(_redeemer: Data, ctx: ScriptContext) -> Bool {
    let ScriptContext { transaction, purpose } = ctx
    let Transaction { inputs, mint, .. } = transaction

    expect Mint(own_policy) = purpose

    // Must spend the contract's registration utxo to guarantee a one time mint
    // This is an artbirary utxo for now, but it could have data if we wanted.
    expect Some(_) = list.find(inputs, 
      fn(input) { 
        input.output_reference.transaction_id == registration_utxo_ref.transaction_id && 
        input.output_reference.output_index == registration_utxo_ref.output_index
      }
    )

    // Must only mint one NFT
    expect 1 = mint
      |> value.from_minted_value
      |> value.quantity_of(own_policy, pool_master_token_name)
      
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
  expect list.any(inputs, fn (input) {
      value.quantity_of(input.output.value, own_validator_hash, pool_master_token_name) == 1
  })

  // Any spent utxo from this contract must be a miner's account
  expect InlineDatum(input_owner_datum) = spent_input.output.datum
  expect input_owner: OwnerData = input_owner_datum

  // All outputs to this script must have an owner datum
  expect Some(_) = outputs 
    |> find_script_outputs(own_validator_hash)
    |> list.find(fn (output) {
      // For the spent account, there must be an output owned by the same account
      expect InlineDatum(output_owner_datum) = output.datum
      expect output_owner: OwnerData = output_owner_datum

      // A mining transaction can ONLY increase the account balance.
      if (input_owner == output_owner) {
        let old_tuna = spent_input.output.value
          |> value.quantity_of(tuna_policy, tuna_token_name)
        
        let new_tuna = output.value
          |> value.quantity_of(tuna_policy, tuna_token_name)

        new_tuna > old_tuna
      } else {
        False
      }
    })
  
  True
}

fn redeem(transaction: Transaction, spent_utxo_ref: OutputReference) {
  let redemption_fee = 2_000_000

  let Transaction { inputs, reference_inputs, outputs, .. } = transaction

  expect Some(spent_input) = inputs |> find_input(spent_utxo_ref)

  let own_address = spent_input.output.address
  expect ScriptCredential(pool_validator_hash) = own_address.payment_credential

  // Must have a reference input to the pool's master token...
  expect Some(master_input_ref) = list.find(reference_inputs, fn (input) {
    1 == value.quantity_of(input.output.value, pool_validator_hash, pool_master_token_name)
  })

  // ...so the contract can verify that the address that owns the token got paid the redemption fee
  expect list.any(outputs, fn (output) {
    output.address == master_input_ref.output.address && 
    value.lovelace_of(output.value) >= redemption_fee
  })

  expect InlineDatum(owner_datum) = spent_input.output.datum
  expect owner_data: OwnerData = owner_datum 
  
  list.has(transaction.extra_signatories, owner_data.owner_vkh)
}
