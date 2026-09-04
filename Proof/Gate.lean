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

set_option exponentiation.threshold 400 in
def canonicalHashLift (target : BaseField) : HashLift target :=
  ⟨BitVec.ofNat 384 target.val, by
    simp only [HashLiftRepresents, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (lt_trans target.val_lt
      (by decide : baseFieldModulus < 2 ^ 384))]
    exact ZMod.natCast_zmod_val target⟩

instance hashLiftNonempty (target : BaseField) : Nonempty (HashLift target) :=
  ⟨canonicalHashLift target⟩

noncomputable instance hashLiftBitsFintype : Fintype (BitVec 384) :=
  Fintype.ofEquiv (Fin (2 ^ 384)) BitVec.equivFin.symm.toEquiv

noncomputable instance hashLiftFintype (target : BaseField) : Fintype (HashLift target) :=
  by
    classical
    exact Fintype.subtype
      (Finset.univ.filter fun lift => HashLiftRepresents lift target) (by simp)

/-- This tape samples a uniform valid lift for one field target. -/
noncomputable def hashLiftTape (target : BaseField) : PMF (HashLift target) :=
  PMF.uniformOfFintype (HashLift target)

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
  have hash0 : daviesMeyer
      ((programHashGate state location window label blocks).fixedOracle.permutation index0)
      label = blocks 0 := by
    change Cryptography.xor
      (((tryProgramFixed state1 index2 label (blocks 2 ^^^ label)).fixedOracle.permutation index0)
        label) label = blocks 0
    rw [point0'', Cryptography.xor, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  have hash1 : daviesMeyer
      ((programHashGate state location window label blocks).fixedOracle.permutation index1)
      label = blocks 1 := by
    change Cryptography.xor
      (((tryProgramFixed state1 index2 label (blocks 2 ^^^ label)).fixedOracle.permutation index1)
        label) label = blocks 1
    rw [point1', Cryptography.xor, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  have hash2 : daviesMeyer
      ((programHashGate state location window label blocks).fixedOracle.permutation index2)
      label = blocks 2 := by
    change Cryptography.xor
      (((tryProgramFixed state1 index2 label (blocks 2 ^^^ label)).fixedOracle.permutation index2)
        label) label = blocks 2
    rw [point2, Cryptography.xor, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  change ((daviesMeyer _ label ++ daviesMeyer _ label ++ daviesMeyer _ label).toNat :
    BaseField) = target
  rw [show daviesMeyer _ label = blocks 2 by
      simpa [index2, fixedKeyIndex] using hash2]
  rw [show daviesMeyer _ label = blocks 1 by
      simpa [index1, fixedKeyIndex] using hash1]
  rw [show daviesMeyer _ label = blocks 0 by
      simpa [index0, fixedKeyIndex] using hash0]
  exact blocksTarget

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
  have pad0 : daviesMeyer
      ((programPadGate state location window label blocks).fixedOracle.permutation index0)
      label = blocks 0 := by
    change Cryptography.xor
      (((tryProgramFixed state0 index1 label (blocks 1 ^^^ label)).fixedOracle.permutation index0)
        label) label = blocks 0
    rw [point0', Cryptography.xor, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  have pad1 : daviesMeyer
      ((programPadGate state location window label blocks).fixedOracle.permutation index1)
      label = blocks 1 := by
    change Cryptography.xor
      (((tryProgramFixed state0 index1 label (blocks 1 ^^^ label)).fixedOracle.permutation index1)
        label) label = blocks 1
    rw [point1, Cryptography.xor, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  change (((daviesMeyer _ label ++ daviesMeyer _ label) ^^^ table.trueRow).toNat :
    BaseField) = target
  rw [show daviesMeyer _ label = blocks 1 by
      simpa [index1, fixedKeyIndex] using pad1]
  rw [show daviesMeyer _ label = blocks 0 by
      simpa [index0, fixedKeyIndex] using pad0]
  rw [blocksTarget]
  rw [show (table.trueRow ^^^ BitAdaptor.fieldBytes target) ^^^ table.trueRow =
      BitAdaptor.fieldBytes target by
    rw [BitVec.xor_comm table.trueRow, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]]
  simp only [BitAdaptor.fieldBytes, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  · exact ZMod.natCast_zmod_val target
  · exact lt_trans target.val_lt (by decide)

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

end Kriterion.ArgoMAC.Security
