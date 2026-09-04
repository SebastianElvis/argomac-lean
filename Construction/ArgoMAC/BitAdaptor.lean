/-
This file defines one bit adaptor.
-/

import BN254
import Cryptography.Primitives
import Mathlib.Tactic.FinCases

namespace Kriterion.ArgoMAC

def coordinateBitCount : Nat := 254

namespace BitAdaptor

open BN254 Cryptography

def fixedKeyMaxUsesPerBucket : Nat := 91
def fixedKeyWindowCount : Nat := 3
def fixedKeyPermutationsPerWindow : Nat := 5

/-- The adaptor uses fixed-key AES windows in a 91, 91, 72 schedule. -/
def fixedKeyWindowIndex (position : Nat) : Nat :=
  position / fixedKeyMaxUsesPerBucket

theorem fixedKeyWindowIndexValid {position : Nat}
    (valid : position < fixedKeyMaxUsesPerBucket * fixedKeyWindowCount) :
    fixedKeyWindowIndex position < fixedKeyWindowCount := by
  exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [mul_comm] using valid)

/-- This value counts coordinate positions in one fixed-key window. -/
def fixedKeyWindowLoad (window : Fin fixedKeyWindowCount) : Nat :=
  ((Finset.range coordinateBitCount).filter fun position =>
    fixedKeyWindowIndex position = window).card

set_option maxRecDepth 100000 in
/-- The three fixed-key windows have the 91, 91, and 72 schedule. -/
theorem fixedKeyWindowLoads :
    fixedKeyWindowLoad ⟨0, by decide⟩ = 91 ∧
      fixedKeyWindowLoad ⟨1, by decide⟩ = 91 ∧
        fixedKeyWindowLoad ⟨2, by decide⟩ = 72 := by
  decide

/-- Every fixed-key permutation receives at most 91 construction inputs. -/
theorem fixedKeyWindowLoadBound (window : Fin fixedKeyWindowCount) :
    fixedKeyWindowLoad window ≤ fixedKeyMaxUsesPerBucket := by
  change Fin 3 at window
  fin_cases window
  · simpa [fixedKeyMaxUsesPerBucket] using (fixedKeyWindowLoads).1.le
  · simpa [fixedKeyMaxUsesPerBucket] using (fixedKeyWindowLoads).2.1.le
  · simpa [fixedKeyMaxUsesPerBucket] using
      Nat.le_trans (fixedKeyWindowLoads).2.2.le (by decide : 72 ≤ 91)

/-- A byte MAC key stores the labels for zero and one. -/
structure Key where
  falseLabel : Block
  trueLabel : Block
deriving DecidableEq

def encode (key : Key) (value : Bool) : Block :=
  if value then key.trueLabel else key.falseLabel

/-- One field MAC uses two AES blocks. -/
abbrev Ciphertext := BitVec 256

/-- The pRPM boundary supplies the Davies--Meyer hash and encryption maps. -/
structure FixedKeyOracle where
  hashToField : Block → BaseField
  encrypt : Block → BaseField → Ciphertext
  decrypt : Block → Ciphertext → BaseField
  decryptEncrypt : ∀ label message, decrypt label (encrypt label message) = message

/-- Each window uses three hash permutations and two pad permutations. -/
structure FixedKeyPermutations where
  hash : Fin 3 → Equiv Block Block
  pad : Fin 2 → Equiv Block Block

def hashBytes (permutations : FixedKeyPermutations) (label : Block) : BitVec 384 :=
  daviesMeyer (permutations.hash 2) label ++
    daviesMeyer (permutations.hash 1) label ++
      daviesMeyer (permutations.hash 0) label

def padBytes (permutations : FixedKeyPermutations) (label : Block) : Ciphertext :=
  daviesMeyer (permutations.pad 1) label ++
    daviesMeyer (permutations.pad 0) label

def fieldBytes (value : BaseField) : Ciphertext :=
  BitVec.ofNat 256 value.val

/-- This oracle uses Davies--Meyer and a little-endian block layout. -/
def fixedKeyOracle (permutations : FixedKeyPermutations) : FixedKeyOracle where
  hashToField label := (hashBytes permutations label).toNat
  encrypt label message := padBytes permutations label ^^^ fieldBytes message
  decrypt label ciphertext := (padBytes permutations label ^^^ ciphertext).toNat
  decryptEncrypt label message := by
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    simp only [fieldBytes, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    · exact ZMod.natCast_zmod_val message
    · exact lt_trans message.val_lt (by decide)

/-- A group MAC key encodes `b` as `slope * b + offset`. -/
structure OutputKey where
  slope : BaseField
  offset : BaseField

def OutputKey.encode (key : OutputKey) (value : Bool) : BaseField :=
  if value then key.slope + key.offset else key.offset

/-- The table stores only the row for the input value `true`. -/
structure Table where
  trueRow : Ciphertext

def garble (oracle : FixedKeyOracle) (slope : BaseField) (key : Key) :
    Table × OutputKey :=
  let outputKey : OutputKey := { slope, offset := oracle.hashToField key.falseLabel }
  ({ trueRow := oracle.encrypt key.trueLabel (outputKey.encode true) }, outputKey)

def evaluate (oracle : FixedKeyOracle) (table : Table) (value : Bool)
    (input : Block) : BaseField :=
  if value then oracle.decrypt input table.trueRow else oracle.hashToField input

theorem evaluateEncode (oracle : FixedKeyOracle) (slope : BaseField)
    (key : Key) (value : Bool) :
    evaluate oracle (garble oracle slope key).1 value (encode key value) =
      (garble oracle slope key).2.encode value := by
  cases value <;> simp [evaluate, garble, encode, OutputKey.encode]
  exact oracle.decryptEncrypt key.trueLabel (slope + oracle.hashToField key.falseLabel)

end Kriterion.ArgoMAC.BitAdaptor
