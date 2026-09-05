/-
This file proves simulation correctness for one bit-adaptor row.
The paper gives the Davies--Meyer programming equation in `gc_rpm_proof.tex`.
The paper source is https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/gc_rpm_proof.tex.
-/

import Proof.Simulator

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

def fixedKeyIndex (location : Pipeline.FixedKeyLocation) (window : Nat)
    (slot : Pipeline.FixedKeySlot) : Pipeline.FixedKeyIndex :=
  ⟨location, ⟨window % BitAdaptor.fixedKeyWindowCount,
    Nat.mod_lt _ (by decide)⟩, slot⟩

def programFixedSlot (state : SimulatorState) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (slot : Pipeline.FixedKeySlot) (label block : Block) : SimulatorState :=
  tryProgramFixed state (fixedKeyIndex location window slot) label (block ^^^ label)

def fixedProgramRecord (location : Pipeline.FixedKeyLocation) (window : Nat)
    (slot : Pipeline.FixedKeySlot) (label block : Block) :
    PermutationRecord Pipeline.FixedKeyIndex Block :=
  { action := .program, origin := .simulator,
    index := fixedKeyIndex location window slot,
    domain := label, range := block ^^^ label }

def programHashGate (state : SimulatorState) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block) (blocks : Fin 3 → Block) : SimulatorState :=
  let first := programFixedSlot state location window (.hash 0) label (blocks 0)
  let second := programFixedSlot first location window (.hash 1) label (blocks 1)
  programFixedSlot second location window (.hash 2) label (blocks 2)

def programPadGate (state : SimulatorState) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block) (blocks : Fin 2 → Block) : SimulatorState :=
  let first := programFixedSlot state location window (.pad 0) label (blocks 0)
  programFixedSlot first location window (.pad 1) label (blocks 1)

def programGate (state : SimulatorState) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (bit : Bool) (label : Block) (hashBlocks : Fin 3 → Block)
    (padBlocks : Fin 2 → Block) : SimulatorState :=
  if bit then programPadGate state location window label padBlocks
  else programHashGate state location window label hashBlocks

def HashGateFresh (state : SimulatorState) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block) (blocks : Fin 3 → Block) : Prop :=
  let first := programFixedSlot state location window (.hash 0) label (blocks 0)
  let second := programFixedSlot first location window (.hash 1) label (blocks 1)
  FreshPermutationPair state.fixedTranscript (fixedKeyIndex location window (.hash 0))
      label (blocks 0 ^^^ label) ∧
    FreshPermutationPair first.fixedTranscript (fixedKeyIndex location window (.hash 1))
      label (blocks 1 ^^^ label) ∧
    FreshPermutationPair second.fixedTranscript (fixedKeyIndex location window (.hash 2))
      label (blocks 2 ^^^ label)

def PadGateFresh (state : SimulatorState) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block) (blocks : Fin 2 → Block) : Prop :=
  let first := programFixedSlot state location window (.pad 0) label (blocks 0)
  FreshPermutationPair state.fixedTranscript (fixedKeyIndex location window (.pad 0))
      label (blocks 0 ^^^ label) ∧
    FreshPermutationPair first.fixedTranscript (fixedKeyIndex location window (.pad 1))
      label (blocks 1 ^^^ label)

def GateFresh (state : SimulatorState) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (bit : Bool) (label : Block) (hashBlocks : Fin 3 → Block)
    (padBlocks : Fin 2 → Block) : Prop :=
  if bit then PadGateFresh state location window label padBlocks
  else HashGateFresh state location window label hashBlocks

/-- This condition connects one random lift to one field target. -/
def HashLiftRepresents (lift : BitVec 384) (target : BaseField) : Prop :=
  (lift.toNat : BaseField) = target

/-- This type contains one valid lift for one field target. -/
abbrev HashLift (target : BaseField) := { lift : BitVec 384 // HashLiftRepresents lift target }

/-- This is the number of complete base-field fibers in 384 bits. -/
def hashLiftQuotientCount : Nat :=
  2 ^ 384 / baseFieldModulus

/-- This type selects one complete lift fiber. -/
abbrev HashLiftQuotient := Fin hashLiftQuotientCount

/-- This type contains every value in the complete lift fibers. -/
abbrev GoodHashLift := Fin (hashLiftQuotientCount * baseFieldModulus)

set_option exponentiation.threshold 400 in
instance hashLiftQuotientNonempty : Nonempty HashLiftQuotient :=
  ⟨⟨0, by decide⟩⟩

set_option exponentiation.threshold 400 in
def defaultHashLiftQuotient : HashLiftQuotient :=
  ⟨0, by decide⟩

set_option exponentiation.threshold 400 in
instance goodHashLiftNonempty : Nonempty GoodHashLift :=
  ⟨⟨0, by decide⟩⟩

/-- This equivalence makes the field residue explicit. -/
def baseFieldFinEquiv : Fin baseFieldModulus ≃ BaseField where
  toFun value := value.val
  invFun value := ⟨value.val, value.val_lt⟩
  left_inv value := by
    apply Fin.ext
    simp only [ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt value.isLt]
  right_inv value := ZMod.natCast_zmod_val value

/-- A good value is one field residue and one independent quotient. -/
def goodHashLiftEquiv : GoodHashLift ≃ BaseField × HashLiftQuotient :=
  finProdFinEquiv.symm |>.trans (Equiv.prodComm _ _) |>.trans
    (Equiv.prodCongr baseFieldFinEquiv (Equiv.refl _))

/-- The good-value equivalence reads the actual residue modulo the field. -/
theorem goodHashLiftEquiv_fst (lift : GoodHashLift) :
    (goodHashLiftEquiv lift).1 = (lift.val : BaseField) := by
  simp [goodHashLiftEquiv, baseFieldFinEquiv]

theorem goodHashLiftValue_lt_goodCount
    (target : BaseField) (quotient : HashLiftQuotient) :
    target.val + baseFieldModulus * quotient.val <
      hashLiftQuotientCount * baseFieldModulus := by
  calc
    target.val + baseFieldModulus * quotient.val <
        baseFieldModulus + baseFieldModulus * quotient.val :=
      Nat.add_lt_add_right target.val_lt _
    _ = baseFieldModulus * (quotient.val + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      ac_rfl
    _ ≤ baseFieldModulus * hashLiftQuotientCount :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt quotient.isLt)
    _ = hashLiftQuotientCount * baseFieldModulus := Nat.mul_comm _ _

set_option exponentiation.threshold 400 in
/-- This lift uses one target residue and one complete-fiber quotient. -/
def goodHashLift (target : BaseField) (quotient : HashLiftQuotient) :
    HashLift target := by
  let value := target.val + baseFieldModulus * quotient.val
  have valueLt : value < 2 ^ 384 := by
    exact lt_of_lt_of_le (goodHashLiftValue_lt_goodCount target quotient) (by
      simpa [hashLiftQuotientCount] using
        Nat.mul_div_le (2 ^ 384) baseFieldModulus)
  refine ⟨BitVec.ofNat 384 value, ?_⟩
  simp only [HashLiftRepresents, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt valueLt]
  simp only [value]
  push_cast
  rw [ZMod.natCast_zmod_val]
  simp

set_option exponentiation.threshold 400 in
/-- The constructed lift is the inverse image of its residue and quotient. -/
theorem goodHashLift_toNat (target : BaseField) (quotient : HashLiftQuotient) :
    (goodHashLift target quotient).1.toNat =
      (goodHashLiftEquiv.symm (target, quotient)).val := by
  change (BitVec.ofNat 384
    (target.val + baseFieldModulus * quotient.val)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le
    (goodHashLiftValue_lt_goodCount target quotient) (by
      simpa [hashLiftQuotientCount] using
        Nat.mul_div_le (2 ^ 384) baseFieldModulus))]
  simp [goodHashLiftEquiv, baseFieldFinEquiv]

set_option exponentiation.threshold 400 in
def canonicalHashLift (target : BaseField) : HashLift target :=
  ⟨BitVec.ofNat 384 target.val, by
    simp only [HashLiftRepresents, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (lt_trans target.val_lt
      (by decide : baseFieldModulus < 2 ^ 384))]
    exact ZMod.natCast_zmod_val target⟩

instance hashLiftNonempty (target : BaseField) : Nonempty (HashLift target) :=
  ⟨canonicalHashLift target⟩

/-- These blocks store one random lift in little-endian order. -/
def liftHashBlocks (lift : BitVec 384) (index : Fin 3) : Block :=
  lift.extractLsb' (index.val * 128) 128

/-- These blocks store one encrypted field target in little-endian order. -/
def targetPadBlocks (table : BitAdaptor.Table) (target : BaseField)
    (index : Fin 2) : Block :=
  (table.trueRow ^^^ BitAdaptor.fieldBytes target).extractLsb' (index.val * 128) 128

theorem liftHashBlocks_value (lift : BitVec 384) :
    liftHashBlocks lift 2 ++ liftHashBlocks lift 1 ++ liftHashBlocks lift 0 = lift := by
    simp only [liftHashBlocks]
    change
      lift.extractLsb' 256 128 ++ lift.extractLsb' 128 128 ++
        lift.extractLsb' 0 128 = lift
    have high :
        lift.extractLsb' 256 128 ++ lift.extractLsb' 128 128 =
          lift.extractLsb' 128 256 := by
      simpa using BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (x := lift) (start₂ := 256) (len₂ := 128)
        (start₁ := 128) (len₁ := 128) (by decide)
    rw [high]
    simpa using BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
      (x := lift) (start₂ := 128) (len₂ := 256)
      (start₁ := 0) (len₁ := 128) (by decide)

theorem targetPadBlocks_value (table : BitAdaptor.Table) (target : BaseField) :
    targetPadBlocks table target 1 ++ targetPadBlocks table target 0 =
      table.trueRow ^^^ BitAdaptor.fieldBytes target := by
  simp only [targetPadBlocks]
  change
    (table.trueRow ^^^ BitAdaptor.fieldBytes target).extractLsb' 128 128 ++
      (table.trueRow ^^^ BitAdaptor.fieldBytes target).extractLsb' 0 128 =
        table.trueRow ^^^ BitAdaptor.fieldBytes target
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 128 = 0 + 128)]
  simp

/-- This operation programs one gate for one selected target. -/
def programGateForTarget (state : SimulatorState) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (bit : Bool) (label : Block) (table : BitAdaptor.Table)
    (target : BaseField) (lift : HashLift target) : SimulatorState :=
  programGate state location window bit label (liftHashBlocks lift.1)
    (targetPadBlocks table target)

def recordConstructionFixed (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (slot : Pipeline.FixedKeySlot) (label : Block) : SimulatorState :=
  (constructionOracleHandler (.fixedForward (fixedKeyIndex location window slot) label) state).2

/-- This operation records the five permutation queries from one gate construction. -/
def recordGateConstructionQueries (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (key : BitAdaptor.Key) :
    SimulatorState :=
  let hash0 := recordConstructionFixed state location window (.hash 0) key.falseLabel
  let hash1 := recordConstructionFixed hash0 location window (.hash 1) key.falseLabel
  let hash2 := recordConstructionFixed hash1 location window (.hash 2) key.falseLabel
  let pad0 := recordConstructionFixed hash2 location window (.pad 0) key.trueLabel
  recordConstructionFixed pad0 location window (.pad 1) key.trueLabel

/-- This operation constructs one gate and records its five permutation queries. -/
def garbleGate (state : SimulatorState) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (slope : BaseField) (key : BitAdaptor.Key) :
    BitAdaptor.Table × BitAdaptor.OutputKey × SimulatorState :=
  let result := BitAdaptor.garble
    (Pipeline.fixedKeyWindow state.fixedOracle location window) slope key
  (result.1, result.2, recordGateConstructionQueries state location window key)

theorem recordConstructionFixed_preservesInvariant (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (slot : Pipeline.FixedKeySlot) (label : Block)
    (invariant : SimulatorInvariant state) :
    SimulatorInvariant (recordConstructionFixed state location window slot label) :=
  oracleHandlerFor_preservesInvariant .construction
    (.fixedForward (fixedKeyIndex location window slot) label) state invariant

/-- Gate construction records all five queries and preserves the shared invariant. -/
theorem recordGateConstructionQueries_preservesInvariant (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (key : BitAdaptor.Key)
    (invariant : SimulatorInvariant state) :
    SimulatorInvariant (recordGateConstructionQueries state location window key) :=
  recordConstructionFixed_preservesInvariant _ _ _ _ _
    (recordConstructionFixed_preservesInvariant _ _ _ _ _
      (recordConstructionFixed_preservesInvariant _ _ _ _ _
        (recordConstructionFixed_preservesInvariant _ _ _ _ _
          (recordConstructionFixed_preservesInvariant _ _ _ _ _ invariant))))

/-- Gate construction adds five construction records. -/
theorem recordGateConstructionQueries_length (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (key : BitAdaptor.Key) :
    (recordGateConstructionQueries state location window key).fixedTranscript.length =
      state.fixedTranscript.length + 5 := by
  simp [recordGateConstructionQueries, recordConstructionFixed,
    constructionOracleHandler, oracleHandlerFor, recordFixed]

theorem recordGateConstructionQueries_origin (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (key : BitAdaptor.Key) :
    ∀ record ∈ (recordGateConstructionQueries state location window key).fixedTranscript.take 5,
      record.origin = .construction := by
  simp [recordGateConstructionQueries, recordConstructionFixed,
    constructionOracleHandler, oracleHandlerFor, recordFixed]

/-- Matching selected hash records make one false gate return its target. -/
theorem hashGate_evaluate_of_matches
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (table : BitAdaptor.Table) (target : BaseField) (blocks : Fin 3 → Block)
    (blocksTarget : ((blocks 2 ++ blocks 1 ++ blocks 0).toNat : BaseField) = target)
    (matchPoints : ∀ slot, oracle.permutation
      (fixedKeyIndex location window (.hash slot)) label = blocks slot ^^^ label) :
    BitAdaptor.evaluate (Pipeline.fixedKeyWindow oracle location window)
      table false label = target := by
  have hash (slot : Fin 3) : daviesMeyer
      (oracle.permutation (fixedKeyIndex location window (.hash slot))) label =
      blocks slot := by
    change Cryptography.xor
      (oracle.permutation (fixedKeyIndex location window (.hash slot)) label) label =
      blocks slot
    rw [matchPoints slot, Cryptography.xor, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  change ((daviesMeyer _ label ++ daviesMeyer _ label ++ daviesMeyer _ label).toNat :
    BaseField) = target
  rw [show daviesMeyer _ label = blocks 2 by
      simpa [Pipeline.fixedKeyPermutations, fixedKeyIndex] using hash 2]
  rw [show daviesMeyer _ label = blocks 1 by
      simpa [Pipeline.fixedKeyPermutations, fixedKeyIndex] using hash 1]
  rw [show daviesMeyer _ label = blocks 0 by
      simpa [Pipeline.fixedKeyPermutations, fixedKeyIndex] using hash 0]
  exact blocksTarget

/-- Matching selected pad records make one true gate return its target. -/
theorem padGate_evaluate_of_matches
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (table : BitAdaptor.Table) (target : BaseField) (blocks : Fin 2 → Block)
    (blocksTarget : blocks 1 ++ blocks 0 =
      table.trueRow ^^^ BitAdaptor.fieldBytes target)
    (matchPoints : ∀ slot, oracle.permutation
      (fixedKeyIndex location window (.pad slot)) label = blocks slot ^^^ label) :
    BitAdaptor.evaluate (Pipeline.fixedKeyWindow oracle location window)
      table true label = target := by
  have pad (slot : Fin 2) : daviesMeyer
      (oracle.permutation (fixedKeyIndex location window (.pad slot))) label =
      blocks slot := by
    change Cryptography.xor
      (oracle.permutation (fixedKeyIndex location window (.pad slot)) label) label =
      blocks slot
    rw [matchPoints slot, Cryptography.xor, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  change (((daviesMeyer _ label ++ daviesMeyer _ label) ^^^ table.trueRow).toNat :
    BaseField) = target
  rw [show daviesMeyer _ label = blocks 1 by
      simpa [Pipeline.fixedKeyPermutations, fixedKeyIndex] using pad 1]
  rw [show daviesMeyer _ label = blocks 0 by
      simpa [Pipeline.fixedKeyPermutations, fixedKeyIndex] using pad 0]
  rw [blocksTarget]
  rw [show (table.trueRow ^^^ BitAdaptor.fieldBytes target) ^^^ table.trueRow =
      BitAdaptor.fieldBytes target by
    rw [BitVec.xor_comm table.trueRow, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]]
  simp only [BitAdaptor.fieldBytes, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  · exact ZMod.natCast_zmod_val target
  · exact lt_trans target.val_lt (by decide)

theorem programHashGate_evaluate (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (table : BitAdaptor.Table) (target : BaseField) (blocks : Fin 3 → Block)
    (blocksTarget : ((blocks 2 ++ blocks 1 ++ blocks 0).toNat : BaseField) = target)
    (notBad : (programHashGate state location window label blocks).bad = false) :
    BitAdaptor.evaluate
        (Pipeline.fixedKeyWindow (programHashGate state location window label blocks).fixedOracle
          location window) table false label = target := by
  let index0 := fixedKeyIndex location window (.hash 0)
  let index1 := fixedKeyIndex location window (.hash 1)
  let index2 := fixedKeyIndex location window (.hash 2)
  let state0 := programFixedSlot state location window (.hash 0) label (blocks 0)
  let state1 := programFixedSlot state0 location window (.hash 1) label (blocks 1)
  have finalNotBad :
      (tryProgramFixed state1 index2 label (blocks 2 ^^^ label)).bad = false := notBad
  have state1NotBad : state1.bad = false :=
    tryProgramFixed_priorNotBad state1 index2 label (blocks 2 ^^^ label) notBad
  have state0NotBad : state0.bad = false :=
    tryProgramFixed_priorNotBad state0 index1 label (blocks 1 ^^^ label) state1NotBad
  have point0 := tryProgramFixed_apply_of_notBad state index0 label
    (blocks 0 ^^^ label) state0NotBad
  have point1 := tryProgramFixed_apply_of_notBad state0 index1 label
    (blocks 1 ^^^ label) state1NotBad
  have point2 := tryProgramFixed_apply_of_notBad state1 index2 label
    (blocks 2 ^^^ label) notBad
  have point0' := tryProgramFixed_preservesOther state0 index0 index1 label
    (blocks 0 ^^^ label) label (blocks 1 ^^^ label) (by simp [index0, index1, fixedKeyIndex]) point0
  have point0'' := tryProgramFixed_preservesOther state1 index0 index2 label
    (blocks 0 ^^^ label) label (blocks 2 ^^^ label) (by simp [index0, index2, fixedKeyIndex]) point0'
  have point1' := tryProgramFixed_preservesOther state1 index1 index2 label
    (blocks 1 ^^^ label) label (blocks 2 ^^^ label) (by simp [index1, index2, fixedKeyIndex]) point1
  apply hashGate_evaluate_of_matches
    (programHashGate state location window label blocks).fixedOracle
    location window label table target blocks blocksTarget
  intro slot
  fin_cases slot
  · simpa [programHashGate, index0, index1, index2, state0, state1] using point0''
  · simpa [programHashGate, index0, index1, index2, state0, state1] using point1'
  · simpa [programHashGate, index0, index1, index2, state0, state1] using point2

theorem programPadGate_evaluate (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (table : BitAdaptor.Table) (target : BaseField) (blocks : Fin 2 → Block)
    (blocksTarget : blocks 1 ++ blocks 0 = table.trueRow ^^^ BitAdaptor.fieldBytes target)
    (notBad : (programPadGate state location window label blocks).bad = false) :
    BitAdaptor.evaluate
        (Pipeline.fixedKeyWindow (programPadGate state location window label blocks).fixedOracle
          location window) table true label = target := by
  let index0 := fixedKeyIndex location window (.pad 0)
  let index1 := fixedKeyIndex location window (.pad 1)
  let state0 := programFixedSlot state location window (.pad 0) label (blocks 0)
  have state0NotBad : state0.bad = false :=
    tryProgramFixed_priorNotBad state0 index1 label (blocks 1 ^^^ label) notBad
  have point0 := tryProgramFixed_apply_of_notBad state index0 label
    (blocks 0 ^^^ label) state0NotBad
  have point1 := tryProgramFixed_apply_of_notBad state0 index1 label
    (blocks 1 ^^^ label) notBad
  have point0' := tryProgramFixed_preservesOther state0 index0 index1 label
    (blocks 0 ^^^ label) label (blocks 1 ^^^ label) (by simp [index0, index1, fixedKeyIndex]) point0
  apply padGate_evaluate_of_matches
    (programPadGate state location window label blocks).fixedOracle
    location window label table target blocks blocksTarget
  intro slot
  fin_cases slot
  · simpa [programPadGate, index0, index1, state0] using point0'
  · simpa [programPadGate, index0, index1, state0] using point1

/-- One programmed gate evaluates to its selected target. -/
theorem programGate_evaluate (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (bit : Bool) (label : Block)
    (table : BitAdaptor.Table) (target : BaseField)
    (hashBlocks : Fin 3 → Block) (padBlocks : Fin 2 → Block)
    (hashTarget : ((hashBlocks 2 ++ hashBlocks 1 ++ hashBlocks 0).toNat : BaseField) = target)
    (padTarget : padBlocks 1 ++ padBlocks 0 =
      table.trueRow ^^^ BitAdaptor.fieldBytes target)
    (notBad : (programGate state location window bit label hashBlocks padBlocks).bad = false) :
    BitAdaptor.evaluate
        (Pipeline.fixedKeyWindow
          (programGate state location window bit label hashBlocks padBlocks).fixedOracle
          location window) table bit label = target := by
  cases bit
  · exact programHashGate_evaluate state location window label table target hashBlocks
      hashTarget notBad
  · exact programPadGate_evaluate state location window label table target padBlocks
      padTarget notBad

/-- A programmed target evaluates without an external block condition. -/
theorem programGateForTarget_evaluate (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (bit : Bool) (label : Block)
    (table : BitAdaptor.Table) (target : BaseField) (lift : HashLift target)
    (notBad : (programGateForTarget state location window bit label table target lift).bad = false) :
    BitAdaptor.evaluate
        (Pipeline.fixedKeyWindow
          (programGateForTarget state location window bit label table target lift).fixedOracle
          location window) table bit label = target := by
  exact programGate_evaluate state location window bit label table target
    (liftHashBlocks lift.1) (targetPadBlocks table target)
    (by rw [liftHashBlocks_value]; exact lift.2)
    (targetPadBlocks_value table target) notBad

/-- One programmed gate preserves the shared invariant. -/
theorem programGate_preservesInvariant (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (bit : Bool) (label : Block)
    (hashBlocks : Fin 3 → Block) (padBlocks : Fin 2 → Block)
    (invariant : SimulatorInvariant state) :
    SimulatorInvariant (programGate state location window bit label hashBlocks padBlocks) := by
  cases bit
  · exact tryProgramFixed_preservesInvariant _ _ _ _
      (tryProgramFixed_preservesInvariant _ _ _ _
        (tryProgramFixed_preservesInvariant _ _ _ _ invariant))
  · exact tryProgramFixed_preservesInvariant _ _ _ _
      (tryProgramFixed_preservesInvariant _ _ _ _ invariant)

/-- Target programming preserves the shared invariant. -/
theorem programGateForTarget_preservesInvariant (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (bit : Bool) (label : Block)
    (table : BitAdaptor.Table) (target : BaseField) (lift : HashLift target)
    (invariant : SimulatorInvariant state) :
    SimulatorInvariant (programGateForTarget state location window bit label table target lift) :=
  programGate_preservesInvariant state location window bit label
    (liftHashBlocks lift.1) (targetPadBlocks table target) invariant

theorem programHashGate_fresh_of_notBad (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (blocks : Fin 3 → Block)
    (notBad : (programHashGate state location window label blocks).bad = false) :
    HashGateFresh state location window label blocks := by
  let index0 := fixedKeyIndex location window (.hash 0)
  let index1 := fixedKeyIndex location window (.hash 1)
  let index2 := fixedKeyIndex location window (.hash 2)
  let state0 := programFixedSlot state location window (.hash 0) label (blocks 0)
  let state1 := programFixedSlot state0 location window (.hash 1) label (blocks 1)
  have finalNotBad :
      (tryProgramFixed state1 index2 label (blocks 2 ^^^ label)).bad = false := notBad
  have state1NotBad : state1.bad = false :=
    tryProgramFixed_priorNotBad state1 index2 label (blocks 2 ^^^ label) notBad
  have state0NotBad : state0.bad = false :=
    tryProgramFixed_priorNotBad state0 index1 label (blocks 1 ^^^ label) state1NotBad
  have first := tryProgramFixed_badOrFresh state index0 label (blocks 0 ^^^ label)
  have second := tryProgramFixed_badOrFresh state0 index1 label (blocks 1 ^^^ label)
  have third := tryProgramFixed_badOrFresh state1 index2 label (blocks 2 ^^^ label)
  rcases first with bad | firstFresh
  · have bad0 : state0.bad = true := by simpa [state0, programFixedSlot] using bad
    exact (Bool.false_ne_true (state0NotBad.symm.trans bad0)).elim
  rcases second with bad | secondFresh
  · have bad1 : state1.bad = true := by simpa [state1, programFixedSlot] using bad
    exact (Bool.false_ne_true (state1NotBad.symm.trans bad1)).elim
  rcases third with bad | thirdFresh
  · exact (Bool.false_ne_true (finalNotBad.symm.trans bad)).elim
  exact ⟨firstFresh, secondFresh, thirdFresh⟩

theorem programPadGate_fresh_of_notBad (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (blocks : Fin 2 → Block)
    (notBad : (programPadGate state location window label blocks).bad = false) :
    PadGateFresh state location window label blocks := by
  let index0 := fixedKeyIndex location window (.pad 0)
  let index1 := fixedKeyIndex location window (.pad 1)
  let state0 := programFixedSlot state location window (.pad 0) label (blocks 0)
  have finalNotBad :
      (tryProgramFixed state0 index1 label (blocks 1 ^^^ label)).bad = false := notBad
  have state0NotBad : state0.bad = false :=
    tryProgramFixed_priorNotBad state0 index1 label (blocks 1 ^^^ label) notBad
  have first := tryProgramFixed_badOrFresh state index0 label (blocks 0 ^^^ label)
  have second := tryProgramFixed_badOrFresh state0 index1 label (blocks 1 ^^^ label)
  rcases first with bad | firstFresh
  · have bad0 : state0.bad = true := by simpa [state0, programFixedSlot] using bad
    exact (Bool.false_ne_true (state0NotBad.symm.trans bad0)).elim
  rcases second with bad | secondFresh
  · exact (Bool.false_ne_true (finalNotBad.symm.trans bad)).elim
  exact ⟨firstFresh, secondFresh⟩

/-- Gate programming succeeds at every slot or records a collision. -/
theorem programGate_badOrFreshAll (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (bit : Bool) (label : Block)
    (hashBlocks : Fin 3 → Block) (padBlocks : Fin 2 → Block) :
    (programGate state location window bit label hashBlocks padBlocks).bad = true ∨
      GateFresh state location window bit label hashBlocks padBlocks := by
  by_cases bad : (programGate state location window bit label hashBlocks padBlocks).bad = true
  · exact Or.inl bad
  · right
    have notBad : (programGate state location window bit label hashBlocks padBlocks).bad = false :=
      Bool.eq_false_of_not_eq_true bad
    cases bit
    · exact programHashGate_fresh_of_notBad state location window label hashBlocks notBad
    · exact programPadGate_fresh_of_notBad state location window label padBlocks notBad

/-- Target programming succeeds at every slot or records a collision. -/
theorem programGateForTarget_badOrFreshAll (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (bit : Bool) (label : Block)
    (table : BitAdaptor.Table) (target : BaseField) (lift : HashLift target) :
    (programGateForTarget state location window bit label table target lift).bad = true ∨
      GateFresh state location window bit label (liftHashBlocks lift.1)
        (targetPadBlocks table target) :=
  programGate_badOrFreshAll state location window bit label
    (liftHashBlocks lift.1) (targetPadBlocks table target)

/-- This value contains one selected gate-programming request. -/
structure GateDirective where
  location : Pipeline.FixedKeyLocation
  window : Nat
  bit : Bool
  label : Block
  table : BitAdaptor.Table
  target : BaseField
  lift : HashLift target

def GateDirective.apply (directive : GateDirective)
    (state : SimulatorState) : SimulatorState :=
  programGateForTarget state directive.location directive.window directive.bit
    directive.label directive.table directive.target directive.lift

def GateDirective.activeSlotCount (directive : GateDirective) : Nat :=
  if directive.bit then 2 else 3

/-- These are the selected records for one gate. -/
def GateDirective.programRecords (directive : GateDirective) :
    List (PermutationRecord Pipeline.FixedKeyIndex Block) :=
  if directive.bit then
    [fixedProgramRecord directive.location directive.window (.pad 1) directive.label
      (targetPadBlocks directive.table directive.target 1),
    fixedProgramRecord directive.location directive.window (.pad 0) directive.label
      (targetPadBlocks directive.table directive.target 0)]
  else
    [fixedProgramRecord directive.location directive.window (.hash 2) directive.label
      (liftHashBlocks directive.lift.1 2),
    fixedProgramRecord directive.location directive.window (.hash 1) directive.label
      (liftHashBlocks directive.lift.1 1),
    fixedProgramRecord directive.location directive.window (.hash 0) directive.label
      (liftHashBlocks directive.lift.1 0)]

def GateDirective.Satisfied (directive : GateDirective)
    (state : SimulatorState) : Prop :=
  BitAdaptor.evaluate
    (Pipeline.fixedKeyWindow state.fixedOracle directive.location directive.window)
    directive.table directive.bit directive.label = directive.target

/-- This operation applies the selected gate programs in order. -/
def programGateSchedule (state : SimulatorState)
    (schedule : List GateDirective) : SimulatorState :=
  schedule.foldl (fun current directive => directive.apply current) state

@[simp] theorem programFixedSlot_encOracle (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (slot : Pipeline.FixedKeySlot) (label block : Block) :
    (programFixedSlot state location window slot label block).encOracle =
      state.encOracle := by
  unfold programFixedSlot tryProgramFixed
  split <;> rfl

@[simp] theorem programFixedSlot_hashOracle (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (slot : Pipeline.FixedKeySlot) (label block : Block) :
    (programFixedSlot state location window slot label block).hashOracle =
      state.hashOracle := by
  unfold programFixedSlot tryProgramFixed
  split <;> rfl

@[simp] theorem programHashGate_encOracle (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : Block) (blocks : Fin 3 → Block) :
    (programHashGate state location window label blocks).encOracle = state.encOracle := by
  simp [programHashGate]

@[simp] theorem programHashGate_hashOracle (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : Block) (blocks : Fin 3 → Block) :
    (programHashGate state location window label blocks).hashOracle = state.hashOracle := by
  simp [programHashGate]

@[simp] theorem programPadGate_encOracle (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : Block) (blocks : Fin 2 → Block) :
    (programPadGate state location window label blocks).encOracle = state.encOracle := by
  simp [programPadGate]

@[simp] theorem programPadGate_hashOracle (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : Block) (blocks : Fin 2 → Block) :
    (programPadGate state location window label blocks).hashOracle = state.hashOracle := by
  simp [programPadGate]

@[simp] theorem GateDirective.apply_encOracle (directive : GateDirective)
    (state : SimulatorState) :
    (directive.apply state).encOracle = state.encOracle := by
  rcases directive with ⟨location, window, bit, label, table, target, lift⟩
  cases bit <;> simp [GateDirective.apply, programGateForTarget, programGate]

@[simp] theorem GateDirective.apply_hashOracle (directive : GateDirective)
    (state : SimulatorState) :
    (directive.apply state).hashOracle = state.hashOracle := by
  rcases directive with ⟨location, window, bit, label, table, target, lift⟩
  cases bit <;> simp [GateDirective.apply, programGateForTarget, programGate]

@[simp] theorem programGateSchedule_encOracle (state : SimulatorState)
    (schedule : List GateDirective) :
    (programGateSchedule state schedule).encOracle = state.encOracle := by
  induction schedule generalizing state with
  | nil => rfl
  | cons directive remaining inductionHypothesis =>
      exact (inductionHypothesis (directive.apply state)).trans
        (directive.apply_encOracle state)

@[simp] theorem programGateSchedule_hashOracle (state : SimulatorState)
    (schedule : List GateDirective) :
    (programGateSchedule state schedule).hashOracle = state.hashOracle := by
  induction schedule generalizing state with
  | nil => rfl
  | cons directive remaining inductionHypothesis =>
      exact (inductionHypothesis (directive.apply state)).trans
        (directive.apply_hashOracle state)

/-- This operation prepends each selected gate record in schedule order. -/
def gateScheduleProgramRecords
    (initial : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (schedule : List GateDirective) :
    List (PermutationRecord Pipeline.FixedKeyIndex Block) :=
  schedule.foldl (fun records directive => directive.programRecords ++ records) initial

theorem gateScheduleProgramRecords_suffix
    (initial : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (schedule : List GateDirective) :
    initial <:+ gateScheduleProgramRecords initial schedule := by
  induction schedule generalizing initial with
  | nil => simp [gateScheduleProgramRecords]
  | cons directive remaining inductionHypothesis =>
      rw [gateScheduleProgramRecords, List.foldl_cons]
      exact (List.suffix_append directive.programRecords initial).trans
        (inductionHypothesis (directive.programRecords ++ initial))

/-- This predicate records freshness at each reached programming step. -/
inductive GateScheduleFresh : SimulatorState → List GateDirective → Prop
  | nil (state : SimulatorState) : GateScheduleFresh state []
  | cons {state : SimulatorState} {directive : GateDirective}
      {remaining : List GateDirective}
      (current : GateFresh state directive.location directive.window directive.bit
        directive.label (liftHashBlocks directive.lift.1)
        (targetPadBlocks directive.table directive.target))
      (next : GateScheduleFresh (directive.apply state) remaining) :
      GateScheduleFresh state (directive :: remaining)

def gateScheduleActiveSlotCount (schedule : List GateDirective) : Nat :=
  (schedule.map GateDirective.activeSlotCount).sum

/-- This schedule programs one complete digit adaptor. -/
def digitGateSchedule {count : Nat}
    (location : Pipeline.FixedKeyLocation)
    (tables : Vector BitAdaptor.Table count) (values : Fin count → Bool)
    (labels : Vector Block count) (targets : Fin count → BaseField)
    (lifts : ∀ index, HashLift (targets index)) : List GateDirective :=
  List.ofFn fun index : Fin count => {
    location
    window := BitAdaptor.fixedKeyWindowIndex index.val
    bit := values index
    label := labels.get index
    table := tables.get index
    target := targets index
    lift := lifts index
  }

theorem digitGateSchedule_length {count : Nat}
    (location : Pipeline.FixedKeyLocation)
    (tables : Vector BitAdaptor.Table count) (values : Fin count → Bool)
    (labels : Vector Block count) (targets : Fin count → BaseField)
    (lifts : ∀ index, HashLift (targets index)) :
    (digitGateSchedule location tables values labels targets lifts).length = count := by
  simp [digitGateSchedule]

/-- This schedule programs the four active adaptors of one RCB X-coordinate. -/
def biquadraticXGateSchedule
    (output : Fin FieldMacToECMac.outputMacCount)
    (y6Table y8Table y10Table x9Table :
      Vector BitAdaptor.Table coordinateBitCount)
    (input : AffineInput) (inputMac : InputMac)
    (y6Targets y8Targets y10Targets x9Targets : Fin coordinateBitCount → BaseField)
    (y6Lifts : ∀ index, HashLift (y6Targets index))
    (y8Lifts : ∀ index, HashLift (y8Targets index))
    (y10Lifts : ∀ index, HashLift (y10Targets index))
    (x9Lifts : ∀ index, HashLift (x9Targets index)) : List GateDirective :=
  digitGateSchedule (.point output .x .y6) y6Table (coordinateValues input.y)
      inputMac.y y6Targets y6Lifts ++
    digitGateSchedule (.point output .x .y8) y8Table (coordinateValues input.y)
      inputMac.y y8Targets y8Lifts ++
    digitGateSchedule (.point output .x .y10) y10Table (coordinateValues input.y)
      inputMac.y y10Targets y10Lifts ++
    digitGateSchedule (.point output .x .x9) x9Table (coordinateValues input.x)
      inputMac.x x9Targets x9Lifts

theorem biquadraticXGateSchedule_length
    (output : Fin FieldMacToECMac.outputMacCount)
    (y6Table y8Table y10Table x9Table :
      Vector BitAdaptor.Table coordinateBitCount)
    (input : AffineInput) (inputMac : InputMac)
    (y6Targets y8Targets y10Targets x9Targets : Fin coordinateBitCount → BaseField)
    (y6Lifts : ∀ index, HashLift (y6Targets index))
    (y8Lifts : ∀ index, HashLift (y8Targets index))
    (y10Lifts : ∀ index, HashLift (y10Targets index))
    (x9Lifts : ∀ index, HashLift (x9Targets index)) :
    (biquadraticXGateSchedule output y6Table y8Table y10Table x9Table
      input inputMac y6Targets y8Targets y10Targets x9Targets
      y6Lifts y8Lifts y10Lifts x9Lifts).length = 4 * coordinateBitCount := by
  simp only [biquadraticXGateSchedule, List.length_append, digitGateSchedule_length]
  omega

/-- This schedule programs the four active adaptors of one RCB Y-coordinate. -/
def biquadraticYGateSchedule
    (output : Fin FieldMacToECMac.outputMacCount)
    (y8Table y10Table x7Table x9Table :
      Vector BitAdaptor.Table coordinateBitCount)
    (input : AffineInput) (inputMac : InputMac)
    (y8Targets y10Targets x7Targets x9Targets : Fin coordinateBitCount → BaseField)
    (y8Lifts : ∀ index, HashLift (y8Targets index))
    (y10Lifts : ∀ index, HashLift (y10Targets index))
    (x7Lifts : ∀ index, HashLift (x7Targets index))
    (x9Lifts : ∀ index, HashLift (x9Targets index)) : List GateDirective :=
  digitGateSchedule (.point output .y .y8) y8Table (coordinateValues input.y)
      inputMac.y y8Targets y8Lifts ++
    digitGateSchedule (.point output .y .y10) y10Table (coordinateValues input.y)
      inputMac.y y10Targets y10Lifts ++
    digitGateSchedule (.point output .y .x7) x7Table (coordinateValues input.x)
      inputMac.x x7Targets x7Lifts ++
    digitGateSchedule (.point output .y .x9) x9Table (coordinateValues input.x)
      inputMac.x x9Targets x9Lifts

theorem biquadraticYGateSchedule_length
    (output : Fin FieldMacToECMac.outputMacCount)
    (y8Table y10Table x7Table x9Table :
      Vector BitAdaptor.Table coordinateBitCount)
    (input : AffineInput) (inputMac : InputMac)
    (y8Targets y10Targets x7Targets x9Targets : Fin coordinateBitCount → BaseField)
    (y8Lifts : ∀ index, HashLift (y8Targets index))
    (y10Lifts : ∀ index, HashLift (y10Targets index))
    (x7Lifts : ∀ index, HashLift (x7Targets index))
    (x9Lifts : ∀ index, HashLift (x9Targets index)) :
    (biquadraticYGateSchedule output y8Table y10Table x7Table x9Table
      input inputMac y8Targets y10Targets x7Targets x9Targets
      y8Lifts y10Lifts x7Lifts x9Lifts).length = 4 * coordinateBitCount := by
  simp only [biquadraticYGateSchedule, List.length_append, digitGateSchedule_length]
  omega

/-- This schedule programs the five active adaptors of one RCB Z-coordinate. -/
def biquadraticZGateSchedule
    (output : Fin FieldMacToECMac.outputMacCount)
    (y6Table y8Table y10Table x7Table x9Table :
      Vector BitAdaptor.Table coordinateBitCount)
    (input : AffineInput) (inputMac : InputMac)
    (y6Targets y8Targets y10Targets x7Targets x9Targets :
      Fin coordinateBitCount → BaseField)
    (y6Lifts : ∀ index, HashLift (y6Targets index))
    (y8Lifts : ∀ index, HashLift (y8Targets index))
    (y10Lifts : ∀ index, HashLift (y10Targets index))
    (x7Lifts : ∀ index, HashLift (x7Targets index))
    (x9Lifts : ∀ index, HashLift (x9Targets index)) : List GateDirective :=
  digitGateSchedule (.point output .z .y6) y6Table (coordinateValues input.y)
      inputMac.y y6Targets y6Lifts ++
    digitGateSchedule (.point output .z .y8) y8Table (coordinateValues input.y)
      inputMac.y y8Targets y8Lifts ++
    digitGateSchedule (.point output .z .y10) y10Table (coordinateValues input.y)
      inputMac.y y10Targets y10Lifts ++
    digitGateSchedule (.point output .z .x7) x7Table (coordinateValues input.x)
      inputMac.x x7Targets x7Lifts ++
    digitGateSchedule (.point output .z .x9) x9Table (coordinateValues input.x)
      inputMac.x x9Targets x9Lifts

theorem biquadraticZGateSchedule_length
    (output : Fin FieldMacToECMac.outputMacCount)
    (y6Table y8Table y10Table x7Table x9Table :
      Vector BitAdaptor.Table coordinateBitCount)
    (input : AffineInput) (inputMac : InputMac)
    (y6Targets y8Targets y10Targets x7Targets x9Targets :
      Fin coordinateBitCount → BaseField)
    (y6Lifts : ∀ index, HashLift (y6Targets index))
    (y8Lifts : ∀ index, HashLift (y8Targets index))
    (y10Lifts : ∀ index, HashLift (y10Targets index))
    (x7Lifts : ∀ index, HashLift (x7Targets index))
    (x9Lifts : ∀ index, HashLift (x9Targets index)) :
    (biquadraticZGateSchedule output y6Table y8Table y10Table x7Table x9Table
      input inputMac y6Targets y8Targets y10Targets x7Targets x9Targets
      y6Lifts y8Lifts y10Lifts x7Lifts x9Lifts).length = 5 * coordinateBitCount := by
  simp only [biquadraticZGateSchedule, List.length_append, digitGateSchedule_length]
  omega

/-- This request contains the public data and selected targets for one RCB X-coordinate. -/
structure BiquadraticXRequest where
  c0 : BaseField
  c1 : BaseField
  c2 : BaseField
  c3 : BaseField
  c5 : BaseField
  y6Table : Vector BitAdaptor.Table coordinateBitCount
  y8Table : Vector BitAdaptor.Table coordinateBitCount
  y10Table : Vector BitAdaptor.Table coordinateBitCount
  x9Table : Vector BitAdaptor.Table coordinateBitCount
  y6Targets : Fin coordinateBitCount → BaseField
  y8Targets : Fin coordinateBitCount → BaseField
  y10Targets : Fin coordinateBitCount → BaseField
  x9Targets : Fin coordinateBitCount → BaseField
  y6Quotients : Fin coordinateBitCount → HashLiftQuotient
  y8Quotients : Fin coordinateBitCount → HashLiftQuotient
  y10Quotients : Fin coordinateBitCount → HashLiftQuotient
  x9Quotients : Fin coordinateBitCount → HashLiftQuotient
  y6Lifts : ∀ index, HashLift (y6Targets index)
  y8Lifts : ∀ index, HashLift (y8Targets index)
  y10Lifts : ∀ index, HashLift (y10Targets index)
  x9Lifts : ∀ index, HashLift (x9Targets index)

def BiquadraticXRequest.table (request : BiquadraticXRequest) : Biquadratic.Table := {
  c0 := some request.c0
  c1 := some request.c1
  c2 := some request.c2
  c3 := some request.c3
  c4 := none
  c5 := some request.c5
  x7 := none
  x9 := some request.x9Table
  y6 := some request.y6Table
  y8 := some request.y8Table
  y10 := some request.y10Table
}

def BiquadraticXRequest.schedule (request : BiquadraticXRequest)
    (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) : List GateDirective :=
  biquadraticXGateSchedule output request.y6Table request.y8Table request.y10Table
    request.x9Table input inputMac request.y6Targets request.y8Targets request.y10Targets
    request.x9Targets request.y6Lifts request.y8Lifts request.y10Lifts request.x9Lifts

def BiquadraticXRequest.result (request : BiquadraticXRequest)
    (input : AffineInput) : BaseField :=
  request.c0 + request.c1 * input.x + request.c2 * input.y +
    request.c3 * input.x * input.y + request.c5 * input.y ^ 2 +
    DigitAdaptor.fromBits request.y6Targets * input.x +
    DigitAdaptor.fromBits request.y8Targets * input.y +
    DigitAdaptor.fromBits request.x9Targets + DigitAdaptor.fromBits request.y10Targets

/-- This request contains the public data and selected targets for one RCB Y-coordinate. -/
structure BiquadraticYRequest where
  c0 : BaseField
  c1 : BaseField
  c4 : BaseField
  c5 : BaseField
  y8Table : Vector BitAdaptor.Table coordinateBitCount
  y10Table : Vector BitAdaptor.Table coordinateBitCount
  x7Table : Vector BitAdaptor.Table coordinateBitCount
  x9Table : Vector BitAdaptor.Table coordinateBitCount
  y8Targets : Fin coordinateBitCount → BaseField
  y10Targets : Fin coordinateBitCount → BaseField
  x7Targets : Fin coordinateBitCount → BaseField
  x9Targets : Fin coordinateBitCount → BaseField
  y8Quotients : Fin coordinateBitCount → HashLiftQuotient
  y10Quotients : Fin coordinateBitCount → HashLiftQuotient
  x7Quotients : Fin coordinateBitCount → HashLiftQuotient
  x9Quotients : Fin coordinateBitCount → HashLiftQuotient
  y8Lifts : ∀ index, HashLift (y8Targets index)
  y10Lifts : ∀ index, HashLift (y10Targets index)
  x7Lifts : ∀ index, HashLift (x7Targets index)
  x9Lifts : ∀ index, HashLift (x9Targets index)

def BiquadraticYRequest.table (request : BiquadraticYRequest) : Biquadratic.Table := {
  c0 := some request.c0
  c1 := some request.c1
  c2 := none
  c3 := none
  c4 := some request.c4
  c5 := some request.c5
  x7 := some request.x7Table
  x9 := some request.x9Table
  y6 := none
  y8 := some request.y8Table
  y10 := some request.y10Table
}

def BiquadraticYRequest.schedule (request : BiquadraticYRequest)
    (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) : List GateDirective :=
  biquadraticYGateSchedule output request.y8Table request.y10Table request.x7Table
    request.x9Table input inputMac request.y8Targets request.y10Targets request.x7Targets
    request.x9Targets request.y8Lifts request.y10Lifts request.x7Lifts request.x9Lifts

def BiquadraticYRequest.result (request : BiquadraticYRequest)
    (input : AffineInput) : BaseField :=
  request.c0 + request.c1 * input.x + request.c4 * input.x ^ 2 +
    request.c5 * input.y ^ 2 + DigitAdaptor.fromBits request.x7Targets * input.x +
    DigitAdaptor.fromBits request.y8Targets * input.y +
    DigitAdaptor.fromBits request.x9Targets + DigitAdaptor.fromBits request.y10Targets

/-- This request contains the public data and selected targets for one RCB Z-coordinate. -/
structure BiquadraticZRequest where
  c0 : BaseField
  c2 : BaseField
  c3 : BaseField
  c4 : BaseField
  c5 : BaseField
  y6Table : Vector BitAdaptor.Table coordinateBitCount
  y8Table : Vector BitAdaptor.Table coordinateBitCount
  y10Table : Vector BitAdaptor.Table coordinateBitCount
  x7Table : Vector BitAdaptor.Table coordinateBitCount
  x9Table : Vector BitAdaptor.Table coordinateBitCount
  y6Targets : Fin coordinateBitCount → BaseField
  y8Targets : Fin coordinateBitCount → BaseField
  y10Targets : Fin coordinateBitCount → BaseField
  x7Targets : Fin coordinateBitCount → BaseField
  x9Targets : Fin coordinateBitCount → BaseField
  y6Quotients : Fin coordinateBitCount → HashLiftQuotient
  y8Quotients : Fin coordinateBitCount → HashLiftQuotient
  y10Quotients : Fin coordinateBitCount → HashLiftQuotient
  x7Quotients : Fin coordinateBitCount → HashLiftQuotient
  x9Quotients : Fin coordinateBitCount → HashLiftQuotient
  y6Lifts : ∀ index, HashLift (y6Targets index)
  y8Lifts : ∀ index, HashLift (y8Targets index)
  y10Lifts : ∀ index, HashLift (y10Targets index)
  x7Lifts : ∀ index, HashLift (x7Targets index)
  x9Lifts : ∀ index, HashLift (x9Targets index)

def BiquadraticZRequest.table (request : BiquadraticZRequest) : Biquadratic.Table := {
  c0 := some request.c0
  c1 := none
  c2 := some request.c2
  c3 := some request.c3
  c4 := some request.c4
  c5 := some request.c5
  x7 := some request.x7Table
  x9 := some request.x9Table
  y6 := some request.y6Table
  y8 := some request.y8Table
  y10 := some request.y10Table
}

def BiquadraticZRequest.schedule (request : BiquadraticZRequest)
    (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) : List GateDirective :=
  biquadraticZGateSchedule output request.y6Table request.y8Table request.y10Table
    request.x7Table request.x9Table input inputMac request.y6Targets request.y8Targets
    request.y10Targets request.x7Targets request.x9Targets request.y6Lifts request.y8Lifts
    request.y10Lifts request.x7Lifts request.x9Lifts

def BiquadraticZRequest.result (request : BiquadraticZRequest)
    (input : AffineInput) : BaseField :=
  request.c0 + request.c2 * input.y + request.c3 * input.x * input.y +
    request.c4 * input.x ^ 2 + request.c5 * input.y ^ 2 +
    DigitAdaptor.fromBits request.y6Targets * input.x +
    DigitAdaptor.fromBits request.x7Targets * input.x +
    DigitAdaptor.fromBits request.y8Targets * input.y +
    DigitAdaptor.fromBits request.x9Targets + DigitAdaptor.fromBits request.y10Targets

/-- This schedule programs all 13 active adaptors of one complete RCB row. -/
def biquadraticRowGateSchedule (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac)
    (x : BiquadraticXRequest) (y : BiquadraticYRequest)
    (z : BiquadraticZRequest) : List GateDirective :=
  x.schedule output input inputMac ++ y.schedule output input inputMac ++
    z.schedule output input inputMac

theorem biquadraticRowGateSchedule_length
    (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac)
    (x : BiquadraticXRequest) (y : BiquadraticYRequest)
    (z : BiquadraticZRequest) :
    (biquadraticRowGateSchedule output input inputMac x y z).length =
      13 * coordinateBitCount := by
  simp only [biquadraticRowGateSchedule, List.length_append,
    BiquadraticXRequest.schedule, BiquadraticYRequest.schedule,
    BiquadraticZRequest.schedule, biquadraticXGateSchedule_length,
    biquadraticYGateSchedule_length, biquadraticZGateSchedule_length]
  omega

/-- This request groups all selected targets for one complete RCB row. -/
structure BiquadraticRowRequest where
  x : BiquadraticXRequest
  y : BiquadraticYRequest
  z : BiquadraticZRequest

def BiquadraticRowRequest.schedule (request : BiquadraticRowRequest)
    (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) : List GateDirective :=
  biquadraticRowGateSchedule output input inputMac request.x request.y request.z

def BiquadraticRowRequest.table (request : BiquadraticRowRequest) :
    FieldMacToECMac.RowTable := {
  x := request.x.table
  y := request.y.table
  z := request.z.table
}

def BiquadraticRowRequest.result (request : BiquadraticRowRequest)
    (input : AffineInput) : FieldMacToECMac.HomogeneousValue := {
  x := request.x.result input
  y := request.y.result input
  z := request.z.result input
}

theorem BiquadraticRowRequest.schedule_length (request : BiquadraticRowRequest)
    (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) :
    (request.schedule output input inputMac).length = 13 * coordinateBitCount :=
  biquadraticRowGateSchedule_length output input inputMac request.x request.y request.z

/-- This request contains the public data and selected targets for curve membership. -/
structure CurveGateRequest where
  c0 : BaseField
  c1 : BaseField
  c2 : BaseField
  x3Table : Vector BitAdaptor.Table coordinateBitCount
  x5Table : Vector BitAdaptor.Table coordinateBitCount
  x7Table : Vector BitAdaptor.Table coordinateBitCount
  y4Table : Vector BitAdaptor.Table coordinateBitCount
  y6Table : Vector BitAdaptor.Table coordinateBitCount
  x3Targets : Fin coordinateBitCount → BaseField
  x5Targets : Fin coordinateBitCount → BaseField
  x7Targets : Fin coordinateBitCount → BaseField
  y4Targets : Fin coordinateBitCount → BaseField
  y6Targets : Fin coordinateBitCount → BaseField
  x3Quotients : Fin coordinateBitCount → HashLiftQuotient
  x5Quotients : Fin coordinateBitCount → HashLiftQuotient
  x7Quotients : Fin coordinateBitCount → HashLiftQuotient
  y4Quotients : Fin coordinateBitCount → HashLiftQuotient
  y6Quotients : Fin coordinateBitCount → HashLiftQuotient
  x3Lifts : ∀ index, HashLift (x3Targets index)
  x5Lifts : ∀ index, HashLift (x5Targets index)
  x7Lifts : ∀ index, HashLift (x7Targets index)
  y4Lifts : ∀ index, HashLift (y4Targets index)
  y6Lifts : ∀ index, HashLift (y6Targets index)

def CurveGateRequest.table (request : CurveGateRequest) : CurveMembership.Table := {
  c0 := request.c0
  c1 := request.c1
  c2 := request.c2
  x3 := request.x3Table
  x5 := request.x5Table
  x7 := request.x7Table
  y4 := request.y4Table
  y6 := request.y6Table
}

def CurveGateRequest.schedule (request : CurveGateRequest)
    (input : AffineInput) (inputMac : InputMac) : List GateDirective :=
  digitGateSchedule (.curve .x3) request.x3Table (coordinateValues input.x)
      inputMac.x request.x3Targets request.x3Lifts ++
    digitGateSchedule (.curve .x5) request.x5Table (coordinateValues input.x)
      inputMac.x request.x5Targets request.x5Lifts ++
    digitGateSchedule (.curve .x7) request.x7Table (coordinateValues input.x)
      inputMac.x request.x7Targets request.x7Lifts ++
    digitGateSchedule (.curve .y4) request.y4Table (coordinateValues input.y)
      inputMac.y request.y4Targets request.y4Lifts ++
    digitGateSchedule (.curve .y6) request.y6Table (coordinateValues input.y)
      inputMac.y request.y6Targets request.y6Lifts

def CurveGateRequest.result (request : CurveGateRequest)
    (input : AffineInput) : BaseField :=
  request.c0 + request.c1 * input.x ^ 3 + request.c2 * input.y ^ 2 +
    DigitAdaptor.fromBits request.x3Targets * input.x ^ 2 +
    DigitAdaptor.fromBits request.y4Targets * input.y +
    DigitAdaptor.fromBits request.x5Targets * input.x +
    DigitAdaptor.fromBits request.y6Targets + DigitAdaptor.fromBits request.x7Targets

theorem CurveGateRequest.schedule_length (request : CurveGateRequest)
    (input : AffineInput) (inputMac : InputMac) :
    (request.schedule input inputMac).length = 5 * coordinateBitCount := by
  simp only [CurveGateRequest.schedule, List.length_append, digitGateSchedule_length]
  omega

/-- These requests contain the selected targets for all 91 complete RCB rows. -/
abbrev PointGateRequests := Vector BiquadraticRowRequest FieldMacToECMac.outputMacCount

def pointGateSchedule (requests : PointGateRequests)
    (input : AffineInput) (inputMac : InputMac) : List GateDirective :=
  (List.ofFn fun output => (requests.get output).schedule output input inputMac).flatten

def pointGateTable (requests : PointGateRequests) : FieldMacToECMac.Table := {
  x := Vector.ofFn fun output => (requests.get output).table.x
  y := Vector.ofFn fun output => (requests.get output).table.y
  z := Vector.ofFn fun output => (requests.get output).table.z
}

def pointGateResults (requests : PointGateRequests)
    (input : AffineInput) : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount :=
  Vector.ofFn fun output => (requests.get output).result input

theorem pointGateSchedule_length (requests : PointGateRequests)
    (input : AffineInput) (inputMac : InputMac) :
    (pointGateSchedule requests input inputMac).length =
      FieldMacToECMac.outputMacCount * 13 * coordinateBitCount := by
  rw [pointGateSchedule, List.length_flatten, List.map_ofFn]
  change (List.ofFn fun output =>
    ((requests.get output).schedule output input inputMac).length).sum = _
  simp_rw [BiquadraticRowRequest.schedule_length]
  rw [List.ofFn_const, List.sum_replicate_nat]
  exact (Nat.mul_assoc _ _ _).symm

/-- This schedule programs the fixed-key layer of the complete circuit. -/
def pipelineGateSchedule (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac) :
    List GateDirective :=
  curve.schedule input curveInputMac ++ pointGateSchedule points input pointInputMac

/-- This value applies the exact EncPRF link after the curve layer. -/
def linkedPointInputMac (state : SimulatorState) (curve : CurveGateRequest)
    (input : AffineInput) (inputMac : InputMac) : InputMac :=
  EncPRF.transformMac state.encOracle
    (EncPRF.whiteningKeys state.hashOracle (curve.result input))
    (BitInput.ofAffine input) inputMac

/-- This schedule uses one input MAC and the exact EncPRF layer link. -/
def linkedPipelineGateSchedule (state : SimulatorState)
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (inputMac : InputMac) : List GateDirective :=
  pipelineGateSchedule curve points input inputMac
    (linkedPointInputMac state curve input inputMac)

@[simp] theorem linkedPointInputMac_programGateSchedule
    (state : SimulatorState) (schedule : List GateDirective)
    (curve : CurveGateRequest) (input : AffineInput) (inputMac : InputMac) :
    linkedPointInputMac (programGateSchedule state schedule) curve input inputMac =
      linkedPointInputMac state curve input inputMac := by
  simp [linkedPointInputMac]

@[simp] theorem linkedPipelineGateSchedule_programGateSchedule
    (state : SimulatorState) (schedule : List GateDirective)
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (inputMac : InputMac) :
    linkedPipelineGateSchedule (programGateSchedule state schedule)
        curve points input inputMac =
      linkedPipelineGateSchedule state curve points input inputMac := by
  simp [linkedPipelineGateSchedule]

theorem pipelineGateSchedule_length (curve : CurveGateRequest)
    (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac) :
    (pipelineGateSchedule curve points input curveInputMac pointInputMac).length =
      Pipeline.digitAdaptorCount * coordinateBitCount := by
  rw [pipelineGateSchedule, List.length_append, curve.schedule_length,
    pointGateSchedule_length]
  simp only [Pipeline.digitAdaptorCount, Pipeline.curveDigitAdaptorCount,
    Pipeline.pointDigitAdaptorsPerOutput]
  exact (Nat.add_mul _ _ _).symm

theorem pipelineGateSchedule_length_value (curve : CurveGateRequest)
    (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac) :
    (pipelineGateSchedule curve points input curveInputMac pointInputMac).length =
      301752 := by
  rw [pipelineGateSchedule_length]
  decide

theorem linkedPipelineGateSchedule_length (state : SimulatorState)
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (inputMac : InputMac) :
    (linkedPipelineGateSchedule state curve points input inputMac).length =
      301752 := by
  exact pipelineGateSchedule_length_value curve points input inputMac
    (linkedPointInputMac state curve input inputMac)

theorem programFixedSlot_fixedTranscript_of_fresh (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (slot : Pipeline.FixedKeySlot) (label block : Block)
    (fresh : FreshPermutationPair state.fixedTranscript
      (fixedKeyIndex location window slot) label (block ^^^ label)) :
    (programFixedSlot state location window slot label block).fixedTranscript =
      fixedProgramRecord location window slot label block :: state.fixedTranscript := by
  have checked := (freshPermutationPairCheck_eq_true _ _ _ _).2 fresh
  simp [programFixedSlot, tryProgramFixed, checked, programFixed, fixedProgramRecord]

theorem programFixedSlot_fixedTranscript_length_of_fresh (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (slot : Pipeline.FixedKeySlot) (label block : Block)
    (fresh : FreshPermutationPair state.fixedTranscript
      (fixedKeyIndex location window slot) label (block ^^^ label)) :
    (programFixedSlot state location window slot label block).fixedTranscript.length =
      state.fixedTranscript.length + 1 := by
  rw [programFixedSlot_fixedTranscript_of_fresh state location window slot label block fresh]
  simp

theorem programHashGate_fixedTranscript_of_fresh (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : Block) (blocks : Fin 3 → Block)
    (fresh : HashGateFresh state location window label blocks) :
    (programHashGate state location window label blocks).fixedTranscript =
      fixedProgramRecord location window (.hash 2) label (blocks 2) ::
      fixedProgramRecord location window (.hash 1) label (blocks 1) ::
      fixedProgramRecord location window (.hash 0) label (blocks 0) ::
      state.fixedTranscript := by
  simp only [HashGateFresh] at fresh
  rcases fresh with ⟨firstFresh, secondFresh, thirdFresh⟩
  let first := programFixedSlot state location window (.hash 0) label (blocks 0)
  let second := programFixedSlot first location window (.hash 1) label (blocks 1)
  calc
    (programHashGate state location window label blocks).fixedTranscript =
        fixedProgramRecord location window (.hash 2) label (blocks 2) ::
          second.fixedTranscript :=
      programFixedSlot_fixedTranscript_of_fresh second location window (.hash 2)
        label (blocks 2) thirdFresh
    _ = fixedProgramRecord location window (.hash 2) label (blocks 2) ::
        fixedProgramRecord location window (.hash 1) label (blocks 1) ::
          first.fixedTranscript := by
      rw [programFixedSlot_fixedTranscript_of_fresh first location window (.hash 1)
        label (blocks 1) secondFresh]
    _ = _ := by
      rw [programFixedSlot_fixedTranscript_of_fresh state location window (.hash 0)
        label (blocks 0) firstFresh]

theorem programPadGate_fixedTranscript_of_fresh (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : Block) (blocks : Fin 2 → Block)
    (fresh : PadGateFresh state location window label blocks) :
    (programPadGate state location window label blocks).fixedTranscript =
      fixedProgramRecord location window (.pad 1) label (blocks 1) ::
      fixedProgramRecord location window (.pad 0) label (blocks 0) ::
      state.fixedTranscript := by
  simp only [PadGateFresh] at fresh
  rcases fresh with ⟨firstFresh, secondFresh⟩
  let first := programFixedSlot state location window (.pad 0) label (blocks 0)
  calc
    (programPadGate state location window label blocks).fixedTranscript =
        fixedProgramRecord location window (.pad 1) label (blocks 1) ::
          first.fixedTranscript :=
      programFixedSlot_fixedTranscript_of_fresh first location window (.pad 1)
        label (blocks 1) secondFresh
    _ = _ := by
      rw [programFixedSlot_fixedTranscript_of_fresh state location window (.pad 0)
        label (blocks 0) firstFresh]

theorem GateDirective.apply_fixedTranscript_of_fresh
    (directive : GateDirective) (state : SimulatorState)
    (fresh : GateFresh state directive.location directive.window directive.bit
      directive.label (liftHashBlocks directive.lift.1)
      (targetPadBlocks directive.table directive.target)) :
    (directive.apply state).fixedTranscript =
      directive.programRecords ++ state.fixedTranscript := by
  cases bit : directive.bit
  · simpa [GateDirective.apply, GateDirective.programRecords, programGateForTarget,
      programGate, bit] using
        programHashGate_fixedTranscript_of_fresh state directive.location directive.window
          directive.label (liftHashBlocks directive.lift.1) (by
            simpa [GateFresh, bit] using fresh)
  · simpa [GateDirective.apply, GateDirective.programRecords, programGateForTarget,
      programGate, bit] using
        programPadGate_fixedTranscript_of_fresh state directive.location directive.window
          directive.label (targetPadBlocks directive.table directive.target) (by
            simpa [GateFresh, bit] using fresh)

/-- Matching selected records make one gate return its target. -/
theorem GateDirective.satisfied_of_programRecords
    (directive : GateDirective) (state : SimulatorState)
    (invariant : SimulatorInvariant state)
    (records : ∀ record ∈ directive.programRecords,
      record ∈ state.fixedTranscript) :
    directive.Satisfied state := by
  unfold GateDirective.Satisfied
  cases bit : directive.bit
  · apply hashGate_evaluate_of_matches state.fixedOracle directive.location
      directive.window directive.label directive.table directive.target
      (liftHashBlocks directive.lift.1)
    · rw [liftHashBlocks_value]
      exact directive.lift.2
    · intro slot
      have member : fixedProgramRecord directive.location directive.window (.hash slot)
          directive.label (liftHashBlocks directive.lift.1 slot) ∈
          directive.programRecords := by
        fin_cases slot <;> simp [GateDirective.programRecords, bit]
      simpa [fixedProgramRecord] using invariant.1 _ (records _ member)
  · apply padGate_evaluate_of_matches state.fixedOracle directive.location
      directive.window directive.label directive.table directive.target
      (targetPadBlocks directive.table directive.target)
    · exact targetPadBlocks_value directive.table directive.target
    · intro slot
      have member : fixedProgramRecord directive.location directive.window (.pad slot)
          directive.label (targetPadBlocks directive.table directive.target slot) ∈
          directive.programRecords := by
        fin_cases slot <;> simp [GateDirective.programRecords, bit]
      simpa [fixedProgramRecord] using invariant.1 _ (records _ member)

theorem programHashGate_fixedTranscript_length_of_fresh (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : Block) (blocks : Fin 3 → Block)
    (fresh : HashGateFresh state location window label blocks) :
    (programHashGate state location window label blocks).fixedTranscript.length =
      state.fixedTranscript.length + 3 := by
  rw [programHashGate_fixedTranscript_of_fresh state location window label blocks fresh]
  simp

theorem programPadGate_fixedTranscript_length_of_fresh (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : Block) (blocks : Fin 2 → Block)
    (fresh : PadGateFresh state location window label blocks) :
    (programPadGate state location window label blocks).fixedTranscript.length =
      state.fixedTranscript.length + 2 := by
  rw [programPadGate_fixedTranscript_of_fresh state location window label blocks fresh]
  simp

theorem GateDirective.apply_fixedTranscript_length_of_fresh
    (directive : GateDirective) (state : SimulatorState)
    (fresh : GateFresh state directive.location directive.window directive.bit
      directive.label (liftHashBlocks directive.lift.1)
      (targetPadBlocks directive.table directive.target)) :
    (directive.apply state).fixedTranscript.length =
      state.fixedTranscript.length + directive.activeSlotCount := by
  cases bit : directive.bit
  · simpa [GateDirective.apply, GateDirective.activeSlotCount, programGateForTarget,
      programGate, bit] using
        programHashGate_fixedTranscript_length_of_fresh state directive.location
          directive.window directive.label (liftHashBlocks directive.lift.1) (by
            simpa [GateFresh, bit] using fresh)
  · simpa [GateDirective.apply, GateDirective.activeSlotCount, programGateForTarget,
      programGate, bit] using
        programPadGate_fixedTranscript_length_of_fresh state directive.location
          directive.window directive.label (targetPadBlocks directive.table directive.target) (by
            simpa [GateFresh, bit] using fresh)

theorem gateScheduleActiveSlotCount_le (schedule : List GateDirective) :
    gateScheduleActiveSlotCount schedule ≤ 3 * schedule.length := by
  induction schedule with
  | nil => simp [gateScheduleActiveSlotCount]
  | cons directive remaining inductionHypothesis =>
      change (remaining.map GateDirective.activeSlotCount).sum ≤
        3 * remaining.length at inductionHypothesis
      cases bit : directive.bit <;>
        simp [gateScheduleActiveSlotCount, GateDirective.activeSlotCount, bit] <;> omega

/-- A fresh schedule adds exactly its selected hash or pad slot count. -/
theorem programGateSchedule_fixedTranscript_length_of_fresh
    {state : SimulatorState} {schedule : List GateDirective}
    (fresh : GateScheduleFresh state schedule) :
    (programGateSchedule state schedule).fixedTranscript.length =
      state.fixedTranscript.length + gateScheduleActiveSlotCount schedule := by
  induction fresh with
  | nil state => simp [programGateSchedule, gateScheduleActiveSlotCount]
  | @cons state directive remaining current next inductionHypothesis =>
      rw [programGateSchedule, List.foldl_cons]
      change (programGateSchedule (directive.apply state) remaining).fixedTranscript.length = _
      rw [inductionHypothesis]
      rw [directive.apply_fixedTranscript_length_of_fresh state current]
      simp [gateScheduleActiveSlotCount]
      omega

/-- A fresh schedule keeps the exact selected programming records. -/
theorem programGateSchedule_fixedTranscript_of_fresh
    {state : SimulatorState} {schedule : List GateDirective}
    (fresh : GateScheduleFresh state schedule) :
    (programGateSchedule state schedule).fixedTranscript =
      gateScheduleProgramRecords state.fixedTranscript schedule := by
  induction fresh with
  | nil state => simp [programGateSchedule, gateScheduleProgramRecords]
  | @cons state directive remaining current next inductionHypothesis =>
      rw [programGateSchedule, List.foldl_cons]
      change (programGateSchedule (directive.apply state) remaining).fixedTranscript = _
      rw [inductionHypothesis]
      rw [directive.apply_fixedTranscript_of_fresh state current]
      rfl

/-- A fresh schedule keeps every prior fixed-key record. -/
theorem programGateSchedule_fixedTranscript_suffix_of_fresh
    {state : SimulatorState} {schedule : List GateDirective}
    (fresh : GateScheduleFresh state schedule) :
    state.fixedTranscript <:+
      (programGateSchedule state schedule).fixedTranscript := by
  rw [programGateSchedule_fixedTranscript_of_fresh fresh]
  exact gateScheduleProgramRecords_suffix state.fixedTranscript schedule

theorem GateDirective.apply_preservesInvariant (directive : GateDirective)
    (state : SimulatorState) (invariant : SimulatorInvariant state) :
    SimulatorInvariant (directive.apply state) :=
  programGateForTarget_preservesInvariant state directive.location directive.window
    directive.bit directive.label directive.table directive.target directive.lift invariant

theorem programFixedSlot_bad_of_bad (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (slot : Pipeline.FixedKeySlot) (label block : Block)
    (bad : state.bad = true) :
    (programFixedSlot state location window slot label block).bad = true :=
  tryProgramFixed_bad_of_bad state (fixedKeyIndex location window slot)
    label (block ^^^ label) bad

theorem programHashGate_bad_of_bad (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : Block) (blocks : Fin 3 → Block) (bad : state.bad = true) :
    (programHashGate state location window label blocks).bad = true :=
  programFixedSlot_bad_of_bad _ location window (.hash 2) label (blocks 2)
    (programFixedSlot_bad_of_bad _ location window (.hash 1) label (blocks 1)
      (programFixedSlot_bad_of_bad state location window (.hash 0) label (blocks 0) bad))

theorem programPadGate_bad_of_bad (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : Block) (blocks : Fin 2 → Block) (bad : state.bad = true) :
    (programPadGate state location window label blocks).bad = true :=
  programFixedSlot_bad_of_bad _ location window (.pad 1) label (blocks 1)
    (programFixedSlot_bad_of_bad state location window (.pad 0) label (blocks 0) bad)

/-- A prior collision remains recorded after one selected gate program. -/
theorem GateDirective.apply_bad_of_bad (directive : GateDirective)
    (state : SimulatorState) (bad : state.bad = true) :
    (directive.apply state).bad = true := by
  simp only [GateDirective.apply, programGateForTarget, programGate]
  split
  · exact programPadGate_bad_of_bad state directive.location directive.window
      directive.label (targetPadBlocks directive.table directive.target) bad
  · exact programHashGate_bad_of_bad state directive.location directive.window
      directive.label (liftHashBlocks directive.lift.1) bad

/-- A prior collision remains recorded after the complete gate schedule. -/
theorem programGateSchedule_bad_of_bad (state : SimulatorState)
    (schedule : List GateDirective) (bad : state.bad = true) :
    (programGateSchedule state schedule).bad = true := by
  induction schedule generalizing state with
  | nil => simpa [programGateSchedule] using bad
  | cons directive remaining inductionHypothesis =>
      rw [programGateSchedule, List.foldl_cons]
      exact inductionHypothesis (directive.apply state)
        (directive.apply_bad_of_bad state bad)

/-- The complete schedule preserves the shared simulator invariant. -/
theorem programGateSchedule_preservesInvariant (state : SimulatorState)
    (schedule : List GateDirective) (invariant : SimulatorInvariant state) :
    SimulatorInvariant (programGateSchedule state schedule) := by
  induction schedule generalizing state with
  | nil => simpa [programGateSchedule] using invariant
  | cons directive remaining inductionHypothesis =>
      rw [programGateSchedule, List.foldl_cons]
      exact inductionHypothesis (directive.apply state)
        (directive.apply_preservesInvariant state invariant)

/-- Every reached gate program is fresh unless the schedule records a collision. -/
theorem programGateSchedule_badOrFresh (state : SimulatorState)
    (schedule : List GateDirective) :
    (programGateSchedule state schedule).bad = true ∨
      GateScheduleFresh state schedule := by
  induction schedule generalizing state with
  | nil => exact Or.inr (.nil state)
  | cons directive remaining inductionHypothesis =>
      have current := programGateForTarget_badOrFreshAll state directive.location
        directive.window directive.bit directive.label directive.table directive.target
        directive.lift
      rcases current with bad | fresh
      · left
        rw [programGateSchedule, List.foldl_cons]
        exact programGateSchedule_bad_of_bad (directive.apply state) remaining bad
      · rcases inductionHypothesis (directive.apply state) with bad | remainingFresh
        · exact Or.inl (by simpa [programGateSchedule] using bad)
        · exact Or.inr (.cons fresh remainingFresh)

/-- A collision-free final state proves freshness at every reached step. -/
theorem programGateSchedule_fresh_of_notBad (state : SimulatorState)
    (schedule : List GateDirective)
    (notBad : (programGateSchedule state schedule).bad = false) :
    GateScheduleFresh state schedule := by
  rcases programGateSchedule_badOrFresh state schedule with bad | fresh
  · exact (Bool.false_ne_true (notBad.symm.trans bad)).elim
  · exact fresh

/-- A collision-free schedule keeps every prior fixed-key record. -/
theorem programGateSchedule_fixedTranscript_suffix_of_notBad
    (state : SimulatorState) (schedule : List GateDirective)
    (notBad : (programGateSchedule state schedule).bad = false) :
    state.fixedTranscript <:+
      (programGateSchedule state schedule).fixedTranscript :=
  programGateSchedule_fixedTranscript_suffix_of_fresh
    (programGateSchedule_fresh_of_notBad state schedule notBad)

/-- A collision-free schedule adds exactly its selected slot count. -/
theorem programGateSchedule_fixedTranscript_length_of_notBad
    (state : SimulatorState) (schedule : List GateDirective)
    (notBad : (programGateSchedule state schedule).bad = false) :
    (programGateSchedule state schedule).fixedTranscript.length =
      state.fixedTranscript.length + gateScheduleActiveSlotCount schedule :=
  programGateSchedule_fixedTranscript_length_of_fresh
    (programGateSchedule_fresh_of_notBad state schedule notBad)

/-- A collision-free gate schedule adds at most three slots per gate. -/
theorem programGateSchedule_fixedTranscript_length_le_of_notBad
    (state : SimulatorState) (schedule : List GateDirective)
    (notBad : (programGateSchedule state schedule).bad = false) :
    (programGateSchedule state schedule).fixedTranscript.length ≤
      state.fixedTranscript.length + 3 * schedule.length := by
  rw [programGateSchedule_fixedTranscript_length_of_notBad state schedule notBad]
  exact Nat.add_le_add_left (gateScheduleActiveSlotCount_le schedule) _

def GateScheduleSatisfied (state : SimulatorState)
    (schedule : List GateDirective) : Prop :=
  ∀ directive ∈ schedule, directive.Satisfied state

/-- A satisfied digit schedule returns every requested per-bit target. -/
theorem digitGateSchedule_evaluate
    {count : Nat} (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation)
    (tables : Vector BitAdaptor.Table count) (values : Fin count → Bool)
    (labels : Vector Block count) (targets : Fin count → BaseField)
    (lifts : ∀ index, HashLift (targets index))
    (satisfied : GateScheduleSatisfied state
      (digitGateSchedule location tables values labels targets lifts)) :
    DigitAdaptor.evaluate
        (fun window => Pipeline.fixedKeyWindow state.fixedOracle location window)
        values tables labels = Vector.ofFn targets := by
  apply Vector.ext
  intro index inRange
  let current : Fin count := ⟨index, inRange⟩
  have member : ({
      location
      window := BitAdaptor.fixedKeyWindowIndex current.val
      bit := values current
      label := labels.get current
      table := tables.get current
      target := targets current
      lift := lifts current
    } : GateDirective) ∈ digitGateSchedule location tables values labels targets lifts := by
    exact List.mem_ofFn.mpr ⟨current, rfl⟩
  simpa [DigitAdaptor.evaluate, current] using satisfied _ member

/-- A satisfied digit schedule returns the requested weighted field value. -/
theorem digitGateSchedule_evaluateValue
    {count : Nat} (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation)
    (tables : Vector BitAdaptor.Table count) (values : Fin count → Bool)
    (labels : Vector Block count) (targets : Fin count → BaseField)
    (lifts : ∀ index, HashLift (targets index))
    (satisfied : GateScheduleSatisfied state
      (digitGateSchedule location tables values labels targets lifts)) :
    DigitAdaptor.fromBits (fun index =>
      (DigitAdaptor.evaluate
        (fun window => Pipeline.fixedKeyWindow state.fixedOracle location window)
        values tables labels).get index) = DigitAdaptor.fromBits targets := by
  rw [digitGateSchedule_evaluate state location tables values labels targets lifts satisfied]
  simp

/-- A satisfied five-adaptor schedule returns the requested membership value. -/
theorem CurveGateRequest.evaluate (request : CurveGateRequest)
    (state : SimulatorState) (input : AffineInput) (inputMac : InputMac)
    (satisfied : GateScheduleSatisfied state (request.schedule input inputMac)) :
    CurveMembership.evaluate (Pipeline.curveOracles state.fixedOracle)
      request.table input inputMac = request.result input := by
  have x3Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.curve .x3) request.x3Table (coordinateValues input.x)
        inputMac.x request.x3Targets request.x3Lifts) := by
    intro directive member
    apply satisfied directive
    simp [CurveGateRequest.schedule, member]
  have x5Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.curve .x5) request.x5Table (coordinateValues input.x)
        inputMac.x request.x5Targets request.x5Lifts) := by
    intro directive member
    apply satisfied directive
    simp [CurveGateRequest.schedule, member]
  have x7Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.curve .x7) request.x7Table (coordinateValues input.x)
        inputMac.x request.x7Targets request.x7Lifts) := by
    intro directive member
    apply satisfied directive
    simp [CurveGateRequest.schedule, member]
  have y4Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.curve .y4) request.y4Table (coordinateValues input.y)
        inputMac.y request.y4Targets request.y4Lifts) := by
    intro directive member
    apply satisfied directive
    simp [CurveGateRequest.schedule, member]
  have y6Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.curve .y6) request.y6Table (coordinateValues input.y)
        inputMac.y request.y6Targets request.y6Lifts) := by
    intro directive member
    apply satisfied directive
    simp [CurveGateRequest.schedule, member]
  have x3Value := digitGateSchedule_evaluateValue state (.curve .x3)
    request.x3Table (coordinateValues input.x) inputMac.x request.x3Targets
    request.x3Lifts x3Satisfied
  have x5Value := digitGateSchedule_evaluateValue state (.curve .x5)
    request.x5Table (coordinateValues input.x) inputMac.x request.x5Targets
    request.x5Lifts x5Satisfied
  have x7Value := digitGateSchedule_evaluateValue state (.curve .x7)
    request.x7Table (coordinateValues input.x) inputMac.x request.x7Targets
    request.x7Lifts x7Satisfied
  have y4Value := digitGateSchedule_evaluateValue state (.curve .y4)
    request.y4Table (coordinateValues input.y) inputMac.y request.y4Targets
    request.y4Lifts y4Satisfied
  have y6Value := digitGateSchedule_evaluateValue state (.curve .y6)
    request.y6Table (coordinateValues input.y) inputMac.y request.y6Targets
    request.y6Lifts y6Satisfied
  simp only [CurveMembership.evaluate, Pipeline.curveOracles,
    CurveMembership.evaluateDigit, CurveGateRequest.table, CurveGateRequest.result]
  rw [x3Value, x5Value, x7Value, y4Value, y6Value]

/-- A satisfied four-adaptor schedule returns the requested RCB X-coordinate. -/
theorem biquadraticXGateSchedule_evaluate
    (state : SimulatorState) (output : Fin FieldMacToECMac.outputMacCount)
    (c0 c1 c2 c3 c5 : BaseField)
    (y6Table y8Table y10Table x9Table :
      Vector BitAdaptor.Table coordinateBitCount)
    (input : AffineInput) (inputMac : InputMac)
    (y6Targets y8Targets y10Targets x9Targets : Fin coordinateBitCount → BaseField)
    (y6Lifts : ∀ index, HashLift (y6Targets index))
    (y8Lifts : ∀ index, HashLift (y8Targets index))
    (y10Lifts : ∀ index, HashLift (y10Targets index))
    (x9Lifts : ∀ index, HashLift (x9Targets index))
    (satisfied : GateScheduleSatisfied state
      (biquadraticXGateSchedule output y6Table y8Table y10Table x9Table
        input inputMac y6Targets y8Targets y10Targets x9Targets
        y6Lifts y8Lifts y10Lifts x9Lifts)) :
    Biquadratic.evaluate (Pipeline.biquadraticOracles state.fixedOracle output .x) {
        c0 := some c0
        c1 := some c1
        c2 := some c2
        c3 := some c3
        c4 := none
        c5 := some c5
        x7 := none
        x9 := some x9Table
        y6 := some y6Table
        y8 := some y8Table
        y10 := some y10Table
      } input inputMac =
      c0 + c1 * input.x + c2 * input.y + c3 * input.x * input.y +
        c5 * input.y ^ 2 + DigitAdaptor.fromBits y6Targets * input.x +
        DigitAdaptor.fromBits y8Targets * input.y + DigitAdaptor.fromBits x9Targets +
        DigitAdaptor.fromBits y10Targets := by
  have y6Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .x .y6) y6Table (coordinateValues input.y)
        inputMac.y y6Targets y6Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticXGateSchedule, member]
  have y8Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .x .y8) y8Table (coordinateValues input.y)
        inputMac.y y8Targets y8Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticXGateSchedule, member]
  have y10Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .x .y10) y10Table (coordinateValues input.y)
        inputMac.y y10Targets y10Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticXGateSchedule, member]
  have x9Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .x .x9) x9Table (coordinateValues input.x)
        inputMac.x x9Targets x9Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticXGateSchedule, member]
  have y6Value := digitGateSchedule_evaluateValue state (.point output .x .y6)
    y6Table (coordinateValues input.y) inputMac.y y6Targets y6Lifts y6Satisfied
  have y8Value := digitGateSchedule_evaluateValue state (.point output .x .y8)
    y8Table (coordinateValues input.y) inputMac.y y8Targets y8Lifts y8Satisfied
  have y10Value := digitGateSchedule_evaluateValue state (.point output .x .y10)
    y10Table (coordinateValues input.y) inputMac.y y10Targets y10Lifts y10Satisfied
  have x9Value := digitGateSchedule_evaluateValue state (.point output .x .x9)
    x9Table (coordinateValues input.x) inputMac.x x9Targets x9Lifts x9Satisfied
  simp only [Biquadratic.evaluate, Pipeline.biquadraticOracles,
    Biquadratic.evaluateDigit,
    Biquadratic.coefficient, Option.getD_some, Option.getD_none]
  rw [y6Value, y8Value, y10Value, x9Value]
  ring

/-- A satisfied four-adaptor schedule returns the requested RCB Y-coordinate. -/
theorem biquadraticYGateSchedule_evaluate
    (state : SimulatorState) (output : Fin FieldMacToECMac.outputMacCount)
    (c0 c1 c4 c5 : BaseField)
    (y8Table y10Table x7Table x9Table :
      Vector BitAdaptor.Table coordinateBitCount)
    (input : AffineInput) (inputMac : InputMac)
    (y8Targets y10Targets x7Targets x9Targets : Fin coordinateBitCount → BaseField)
    (y8Lifts : ∀ index, HashLift (y8Targets index))
    (y10Lifts : ∀ index, HashLift (y10Targets index))
    (x7Lifts : ∀ index, HashLift (x7Targets index))
    (x9Lifts : ∀ index, HashLift (x9Targets index))
    (satisfied : GateScheduleSatisfied state
      (biquadraticYGateSchedule output y8Table y10Table x7Table x9Table
        input inputMac y8Targets y10Targets x7Targets x9Targets
        y8Lifts y10Lifts x7Lifts x9Lifts)) :
    Biquadratic.evaluate (Pipeline.biquadraticOracles state.fixedOracle output .y) {
        c0 := some c0
        c1 := some c1
        c2 := none
        c3 := none
        c4 := some c4
        c5 := some c5
        x7 := some x7Table
        x9 := some x9Table
        y6 := none
        y8 := some y8Table
        y10 := some y10Table
      } input inputMac =
      c0 + c1 * input.x + c4 * input.x ^ 2 + c5 * input.y ^ 2 +
        DigitAdaptor.fromBits x7Targets * input.x +
        DigitAdaptor.fromBits y8Targets * input.y + DigitAdaptor.fromBits x9Targets +
        DigitAdaptor.fromBits y10Targets := by
  have y8Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .y .y8) y8Table (coordinateValues input.y)
        inputMac.y y8Targets y8Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticYGateSchedule, member]
  have y10Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .y .y10) y10Table (coordinateValues input.y)
        inputMac.y y10Targets y10Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticYGateSchedule, member]
  have x7Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .y .x7) x7Table (coordinateValues input.x)
        inputMac.x x7Targets x7Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticYGateSchedule, member]
  have x9Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .y .x9) x9Table (coordinateValues input.x)
        inputMac.x x9Targets x9Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticYGateSchedule, member]
  have y8Value := digitGateSchedule_evaluateValue state (.point output .y .y8)
    y8Table (coordinateValues input.y) inputMac.y y8Targets y8Lifts y8Satisfied
  have y10Value := digitGateSchedule_evaluateValue state (.point output .y .y10)
    y10Table (coordinateValues input.y) inputMac.y y10Targets y10Lifts y10Satisfied
  have x7Value := digitGateSchedule_evaluateValue state (.point output .y .x7)
    x7Table (coordinateValues input.x) inputMac.x x7Targets x7Lifts x7Satisfied
  have x9Value := digitGateSchedule_evaluateValue state (.point output .y .x9)
    x9Table (coordinateValues input.x) inputMac.x x9Targets x9Lifts x9Satisfied
  simp only [Biquadratic.evaluate, Pipeline.biquadraticOracles,
    Biquadratic.evaluateDigit, Biquadratic.coefficient,
    Option.getD_some, Option.getD_none]
  rw [y8Value, y10Value, x7Value, x9Value]
  ring

/-- A satisfied five-adaptor schedule returns the requested RCB Z-coordinate. -/
theorem biquadraticZGateSchedule_evaluate
    (state : SimulatorState) (output : Fin FieldMacToECMac.outputMacCount)
    (c0 c2 c3 c4 c5 : BaseField)
    (y6Table y8Table y10Table x7Table x9Table :
      Vector BitAdaptor.Table coordinateBitCount)
    (input : AffineInput) (inputMac : InputMac)
    (y6Targets y8Targets y10Targets x7Targets x9Targets :
      Fin coordinateBitCount → BaseField)
    (y6Lifts : ∀ index, HashLift (y6Targets index))
    (y8Lifts : ∀ index, HashLift (y8Targets index))
    (y10Lifts : ∀ index, HashLift (y10Targets index))
    (x7Lifts : ∀ index, HashLift (x7Targets index))
    (x9Lifts : ∀ index, HashLift (x9Targets index))
    (satisfied : GateScheduleSatisfied state
      (biquadraticZGateSchedule output y6Table y8Table y10Table x7Table x9Table
        input inputMac y6Targets y8Targets y10Targets x7Targets x9Targets
        y6Lifts y8Lifts y10Lifts x7Lifts x9Lifts)) :
    Biquadratic.evaluate (Pipeline.biquadraticOracles state.fixedOracle output .z) {
        c0 := some c0
        c1 := none
        c2 := some c2
        c3 := some c3
        c4 := some c4
        c5 := some c5
        x7 := some x7Table
        x9 := some x9Table
        y6 := some y6Table
        y8 := some y8Table
        y10 := some y10Table
      } input inputMac =
      c0 + c2 * input.y + c3 * input.x * input.y + c4 * input.x ^ 2 +
        c5 * input.y ^ 2 + DigitAdaptor.fromBits y6Targets * input.x +
        DigitAdaptor.fromBits x7Targets * input.x +
        DigitAdaptor.fromBits y8Targets * input.y + DigitAdaptor.fromBits x9Targets +
        DigitAdaptor.fromBits y10Targets := by
  have y6Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .z .y6) y6Table (coordinateValues input.y)
        inputMac.y y6Targets y6Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticZGateSchedule, member]
  have y8Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .z .y8) y8Table (coordinateValues input.y)
        inputMac.y y8Targets y8Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticZGateSchedule, member]
  have y10Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .z .y10) y10Table (coordinateValues input.y)
        inputMac.y y10Targets y10Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticZGateSchedule, member]
  have x7Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .z .x7) x7Table (coordinateValues input.x)
        inputMac.x x7Targets x7Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticZGateSchedule, member]
  have x9Satisfied : GateScheduleSatisfied state
      (digitGateSchedule (.point output .z .x9) x9Table (coordinateValues input.x)
        inputMac.x x9Targets x9Lifts) := by
    intro directive member
    apply satisfied directive
    simp [biquadraticZGateSchedule, member]
  have y6Value := digitGateSchedule_evaluateValue state (.point output .z .y6)
    y6Table (coordinateValues input.y) inputMac.y y6Targets y6Lifts y6Satisfied
  have y8Value := digitGateSchedule_evaluateValue state (.point output .z .y8)
    y8Table (coordinateValues input.y) inputMac.y y8Targets y8Lifts y8Satisfied
  have y10Value := digitGateSchedule_evaluateValue state (.point output .z .y10)
    y10Table (coordinateValues input.y) inputMac.y y10Targets y10Lifts y10Satisfied
  have x7Value := digitGateSchedule_evaluateValue state (.point output .z .x7)
    x7Table (coordinateValues input.x) inputMac.x x7Targets x7Lifts x7Satisfied
  have x9Value := digitGateSchedule_evaluateValue state (.point output .z .x9)
    x9Table (coordinateValues input.x) inputMac.x x9Targets x9Lifts x9Satisfied
  simp only [Biquadratic.evaluate, Pipeline.biquadraticOracles,
    Biquadratic.evaluateDigit, Biquadratic.coefficient,
    Option.getD_some, Option.getD_none]
  rw [y6Value, y8Value, y10Value, x7Value, x9Value]
  ring

/-- A satisfied row request returns one complete homogeneous value. -/
theorem BiquadraticRowRequest.evaluate (request : BiquadraticRowRequest)
    (state : SimulatorState) (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac)
    (satisfied : GateScheduleSatisfied state (request.schedule output input inputMac)) :
    ({
      x := Biquadratic.evaluate
        (Pipeline.biquadraticOracles state.fixedOracle output .x)
        request.table.x input inputMac
      y := Biquadratic.evaluate
        (Pipeline.biquadraticOracles state.fixedOracle output .y)
        request.table.y input inputMac
      z := Biquadratic.evaluate
        (Pipeline.biquadraticOracles state.fixedOracle output .z)
        request.table.z input inputMac
    } : FieldMacToECMac.HomogeneousValue) = request.result input := by
  have xSatisfied : GateScheduleSatisfied state
      (request.x.schedule output input inputMac) := by
    intro directive member
    apply satisfied directive
    simp [BiquadraticRowRequest.schedule, biquadraticRowGateSchedule, member]
  have ySatisfied : GateScheduleSatisfied state
      (request.y.schedule output input inputMac) := by
    intro directive member
    apply satisfied directive
    simp [BiquadraticRowRequest.schedule, biquadraticRowGateSchedule, member]
  have zSatisfied : GateScheduleSatisfied state
      (request.z.schedule output input inputMac) := by
    intro directive member
    apply satisfied directive
    simp [BiquadraticRowRequest.schedule, biquadraticRowGateSchedule, member]
  have xValue : Biquadratic.evaluate
      (Pipeline.biquadraticOracles state.fixedOracle output .x)
      request.x.table input inputMac = request.x.result input := by
    simpa only [BiquadraticXRequest.table, BiquadraticXRequest.result,
      BiquadraticXRequest.schedule] using
      biquadraticXGateSchedule_evaluate state output request.x.c0 request.x.c1
        request.x.c2 request.x.c3 request.x.c5 request.x.y6Table request.x.y8Table
        request.x.y10Table request.x.x9Table input inputMac request.x.y6Targets
        request.x.y8Targets request.x.y10Targets request.x.x9Targets request.x.y6Lifts
        request.x.y8Lifts request.x.y10Lifts request.x.x9Lifts xSatisfied
  have yValue : Biquadratic.evaluate
      (Pipeline.biquadraticOracles state.fixedOracle output .y)
      request.y.table input inputMac = request.y.result input := by
    simpa only [BiquadraticYRequest.table, BiquadraticYRequest.result,
      BiquadraticYRequest.schedule] using
      biquadraticYGateSchedule_evaluate state output request.y.c0 request.y.c1
        request.y.c4 request.y.c5 request.y.y8Table request.y.y10Table request.y.x7Table
        request.y.x9Table input inputMac request.y.y8Targets request.y.y10Targets
        request.y.x7Targets request.y.x9Targets request.y.y8Lifts request.y.y10Lifts
        request.y.x7Lifts request.y.x9Lifts ySatisfied
  have zValue : Biquadratic.evaluate
      (Pipeline.biquadraticOracles state.fixedOracle output .z)
      request.z.table input inputMac = request.z.result input := by
    simpa only [BiquadraticZRequest.table, BiquadraticZRequest.result,
      BiquadraticZRequest.schedule] using
      biquadraticZGateSchedule_evaluate state output request.z.c0 request.z.c2
        request.z.c3 request.z.c4 request.z.c5 request.z.y6Table request.z.y8Table
        request.z.y10Table request.z.x7Table request.z.x9Table input inputMac
        request.z.y6Targets request.z.y8Targets request.z.y10Targets request.z.x7Targets
        request.z.x9Targets request.z.y6Lifts request.z.y8Lifts request.z.y10Lifts
        request.z.x7Lifts request.z.x9Lifts zSatisfied
  simp only [BiquadraticRowRequest.table, BiquadraticRowRequest.result]
  rw [xValue, yValue, zValue]

/-- A satisfied 91-row schedule returns every requested homogeneous value. -/
theorem pointGateSchedule_evaluate (requests : PointGateRequests)
    (state : SimulatorState) (input : AffineInput) (inputMac : InputMac)
    (satisfied : GateScheduleSatisfied state (pointGateSchedule requests input inputMac)) :
    FieldMacToECMac.evaluateHomogeneous (pointGateTable requests)
        (Pipeline.pointOracles state.fixedOracle) input inputMac =
      pointGateResults requests input := by
  apply Vector.ext
  intro index inRange
  let output : Fin FieldMacToECMac.outputMacCount := ⟨index, inRange⟩
  have rowSatisfied : GateScheduleSatisfied state
      ((requests.get output).schedule output input inputMac) := by
    intro directive member
    apply satisfied directive
    rw [pointGateSchedule, List.mem_flatten]
    exact ⟨(requests.get output).schedule output input inputMac,
      List.mem_ofFn.mpr ⟨output, rfl⟩, member⟩
  have rowValue := (requests.get output).evaluate state output input inputMac rowSatisfied
  simpa [FieldMacToECMac.evaluateHomogeneous, pointGateTable,
    Pipeline.pointOracles, pointGateResults, output] using rowValue

/-- A satisfied linked schedule returns all requested pipeline values. -/
theorem linkedPipelineGateSchedule_evaluate [FieldCertificate]
    (curve : CurveGateRequest)
    (points : PointGateRequests) (state : SimulatorState)
    (input : AffineInput) (inputMac : InputMac) (point : Point)
    (decoded : decodePoint input = some point)
    (satisfied : GateScheduleSatisfied state
      (linkedPipelineGateSchedule state curve points input inputMac)) :
    Pipeline.evaluate state.fixedOracle state.encOracle state.hashOracle
        { curve := curve.table, pointMAC := pointGateTable points }
        (BitInput.ofAffine input) inputMac =
      some ({ point := input, pointMacs := pointGateResults points input } :
        FieldMacToECMac.Result) := by
  have curveSatisfied : GateScheduleSatisfied state
      (curve.schedule input inputMac) := by
    intro directive member
    apply satisfied directive
    simp [linkedPipelineGateSchedule, pipelineGateSchedule, member]
  have pointSatisfied : GateScheduleSatisfied state
      (pointGateSchedule points input
        (linkedPointInputMac state curve input inputMac)) := by
    intro directive member
    apply satisfied directive
    simp [linkedPipelineGateSchedule, pipelineGateSchedule, member]
  have curveValue := curve.evaluate state input inputMac curveSatisfied
  have pointValue := pointGateSchedule_evaluate points state input
    (linkedPointInputMac state curve input inputMac) pointSatisfied
  simp only [Pipeline.evaluate, BitInput.toAffineOfAffine, decoded]
  rw [curveValue]
  change some (FieldMacToECMac.evaluate (pointGateTable points)
    (Pipeline.pointOracles state.fixedOracle) input
    (linkedPointInputMac state curve input inputMac)) = _
  simp only [FieldMacToECMac.evaluate]
  rw [pointValue]

/-- The final state satisfies every target in one fresh schedule. -/
theorem programGateSchedule_satisfies_of_fresh
    {state : SimulatorState} {schedule : List GateDirective}
    (fresh : GateScheduleFresh state schedule)
    (invariant : SimulatorInvariant state) :
    GateScheduleSatisfied (programGateSchedule state schedule) schedule := by
  induction fresh with
  | nil state => simp [GateScheduleSatisfied]
  | @cons state directive remaining current next inductionHypothesis =>
      intro selected member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · apply GateDirective.satisfied_of_programRecords selected
          (programGateSchedule state (selected :: remaining))
          (programGateSchedule_preservesInvariant state (selected :: remaining) invariant)
        intro record recordMember
        have inNext : record ∈ (selected.apply state).fixedTranscript := by
          rw [selected.apply_fixedTranscript_of_fresh state current]
          exact List.mem_append_left state.fixedTranscript recordMember
        have inFinal :=
          (programGateSchedule_fixedTranscript_suffix_of_fresh next).mem inNext
        simpa [programGateSchedule] using inFinal
      · have satisfied := inductionHypothesis
          (directive.apply_preservesInvariant state invariant) selected member
        simpa [programGateSchedule] using satisfied

/-- A collision-free schedule satisfies every selected gate target. -/
theorem programGateSchedule_satisfies_of_notBad
    (state : SimulatorState) (schedule : List GateDirective)
    (invariant : SimulatorInvariant state)
    (notBad : (programGateSchedule state schedule).bad = false) :
    GateScheduleSatisfied (programGateSchedule state schedule) schedule :=
  programGateSchedule_satisfies_of_fresh
    (programGateSchedule_fresh_of_notBad state schedule notBad) invariant

/-- Collision-free programming makes one digit return its requested value. -/
theorem programDigitGateSchedule_evaluateValue
    {count : Nat} (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation)
    (tables : Vector BitAdaptor.Table count) (values : Fin count → Bool)
    (labels : Vector Block count) (targets : Fin count → BaseField)
    (lifts : ∀ index, HashLift (targets index))
    (invariant : SimulatorInvariant state)
    (notBad : (programGateSchedule state
      (digitGateSchedule location tables values labels targets lifts)).bad = false) :
    DigitAdaptor.fromBits (fun index =>
      (DigitAdaptor.evaluate
        (fun window => Pipeline.fixedKeyWindow
          (programGateSchedule state
            (digitGateSchedule location tables values labels targets lifts)).fixedOracle
          location window)
        values tables labels).get index) = DigitAdaptor.fromBits targets := by
  apply digitGateSchedule_evaluateValue
  exact programGateSchedule_satisfies_of_notBad state
    (digitGateSchedule location tables values labels targets lifts) invariant notBad

/-- Collision-free programming returns the requested RCB X-coordinate. -/
theorem programBiquadraticXGateSchedule_evaluate
    (state : SimulatorState) (output : Fin FieldMacToECMac.outputMacCount)
    (c0 c1 c2 c3 c5 : BaseField)
    (y6Table y8Table y10Table x9Table :
      Vector BitAdaptor.Table coordinateBitCount)
    (input : AffineInput) (inputMac : InputMac)
    (y6Targets y8Targets y10Targets x9Targets : Fin coordinateBitCount → BaseField)
    (y6Lifts : ∀ index, HashLift (y6Targets index))
    (y8Lifts : ∀ index, HashLift (y8Targets index))
    (y10Lifts : ∀ index, HashLift (y10Targets index))
    (x9Lifts : ∀ index, HashLift (x9Targets index))
    (invariant : SimulatorInvariant state)
    (notBad : (programGateSchedule state
      (biquadraticXGateSchedule output y6Table y8Table y10Table x9Table
        input inputMac y6Targets y8Targets y10Targets x9Targets
        y6Lifts y8Lifts y10Lifts x9Lifts)).bad = false) :
    Biquadratic.evaluate
        (Pipeline.biquadraticOracles
          (programGateSchedule state
            (biquadraticXGateSchedule output y6Table y8Table y10Table x9Table
              input inputMac y6Targets y8Targets y10Targets x9Targets
              y6Lifts y8Lifts y10Lifts x9Lifts)).fixedOracle output .x) {
        c0 := some c0
        c1 := some c1
        c2 := some c2
        c3 := some c3
        c4 := none
        c5 := some c5
        x7 := none
        x9 := some x9Table
        y6 := some y6Table
        y8 := some y8Table
        y10 := some y10Table
      } input inputMac =
      c0 + c1 * input.x + c2 * input.y + c3 * input.x * input.y +
        c5 * input.y ^ 2 + DigitAdaptor.fromBits y6Targets * input.x +
        DigitAdaptor.fromBits y8Targets * input.y + DigitAdaptor.fromBits x9Targets +
        DigitAdaptor.fromBits y10Targets := by
  apply biquadraticXGateSchedule_evaluate
  exact programGateSchedule_satisfies_of_notBad state
    (biquadraticXGateSchedule output y6Table y8Table y10Table x9Table
      input inputMac y6Targets y8Targets y10Targets x9Targets
      y6Lifts y8Lifts y10Lifts x9Lifts) invariant notBad

/-- Collision-free programming returns all three coordinates of one RCB row. -/
theorem programBiquadraticRowGateSchedule_evaluate
    (state : SimulatorState) (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac)
    (x : BiquadraticXRequest) (y : BiquadraticYRequest)
    (z : BiquadraticZRequest)
    (invariant : SimulatorInvariant state)
    (notBad : (programGateSchedule state
      (biquadraticRowGateSchedule output input inputMac x y z)).bad = false) :
    let final := programGateSchedule state
      (biquadraticRowGateSchedule output input inputMac x y z)
    Biquadratic.evaluate (Pipeline.biquadraticOracles final.fixedOracle output .x)
        x.table input inputMac = x.result input ∧
      Biquadratic.evaluate (Pipeline.biquadraticOracles final.fixedOracle output .y)
        y.table input inputMac = y.result input ∧
      Biquadratic.evaluate (Pipeline.biquadraticOracles final.fixedOracle output .z)
        z.table input inputMac = z.result input := by
  dsimp only
  let schedule := biquadraticRowGateSchedule output input inputMac x y z
  let final := programGateSchedule state schedule
  change final.bad = false at notBad
  have satisfied : GateScheduleSatisfied final schedule :=
    programGateSchedule_satisfies_of_notBad state schedule invariant notBad
  have xSatisfied : GateScheduleSatisfied final (x.schedule output input inputMac) := by
    intro directive member
    apply satisfied directive
    simp [schedule, biquadraticRowGateSchedule, member]
  have ySatisfied : GateScheduleSatisfied final (y.schedule output input inputMac) := by
    intro directive member
    apply satisfied directive
    simp [schedule, biquadraticRowGateSchedule, member]
  have zSatisfied : GateScheduleSatisfied final (z.schedule output input inputMac) := by
    intro directive member
    apply satisfied directive
    simp [schedule, biquadraticRowGateSchedule, member]
  change Biquadratic.evaluate (Pipeline.biquadraticOracles final.fixedOracle output .x)
      x.table input inputMac = x.result input ∧
    Biquadratic.evaluate (Pipeline.biquadraticOracles final.fixedOracle output .y)
      y.table input inputMac = y.result input ∧
    Biquadratic.evaluate (Pipeline.biquadraticOracles final.fixedOracle output .z)
      z.table input inputMac = z.result input
  constructor
  · simpa only [BiquadraticXRequest.table, BiquadraticXRequest.result,
      BiquadraticXRequest.schedule] using
      biquadraticXGateSchedule_evaluate final output x.c0 x.c1 x.c2 x.c3 x.c5
        x.y6Table x.y8Table x.y10Table x.x9Table input inputMac x.y6Targets
        x.y8Targets x.y10Targets x.x9Targets x.y6Lifts x.y8Lifts x.y10Lifts
        x.x9Lifts xSatisfied
  · constructor
    · simpa only [BiquadraticYRequest.table, BiquadraticYRequest.result,
        BiquadraticYRequest.schedule] using
        biquadraticYGateSchedule_evaluate final output y.c0 y.c1 y.c4 y.c5
          y.y8Table y.y10Table y.x7Table y.x9Table input inputMac y.y8Targets
          y.y10Targets y.x7Targets y.x9Targets y.y8Lifts y.y10Lifts y.x7Lifts
          y.x9Lifts ySatisfied
    · simpa only [BiquadraticZRequest.table, BiquadraticZRequest.result,
        BiquadraticZRequest.schedule] using
        biquadraticZGateSchedule_evaluate final output z.c0 z.c2 z.c3 z.c4 z.c5
          z.y6Table z.y8Table z.y10Table z.x7Table z.x9Table input inputMac
          z.y6Targets z.y8Targets z.y10Targets z.x7Targets z.x9Targets z.y6Lifts
          z.y8Lifts z.y10Lifts z.x7Lifts z.x9Lifts zSatisfied

end Kriterion.ArgoMAC.Security
