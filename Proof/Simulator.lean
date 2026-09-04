/-
This file defines one simulator state for all ArgoMAC layers.
The paper uses shared state in `gc_optimizations.tex`.
The paper source is https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/gc_optimizations.tex.
-/

import Proof.Linking

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

/-- This value identifies one layer in the composed circuit. -/
inductive Layer
  | input
  | curve
  | point
deriving DecidableEq

/-- This value identifies one label wire. -/
structure Wire where
  layer : Layer
  position : Nat
  branch : Bool
deriving DecidableEq

/-- This value records one pending or committed wire label. -/
structure LabelCommitment where
  wire : Wire
  label : Block
  pending : Bool
deriving DecidableEq

/-- Distinct wires use distinct labels. -/
def DistinctCommitments (commitments : List LabelCommitment) : Prop :=
  commitments.Pairwise fun first second =>
    first.wire ≠ second.wire ∧ first.label ≠ second.label

/-- This value contains the inputs for the exact non-black-box key relation. -/
structure LinkingState where
  bridgeKey : BaseField
  sourceKey : InputMacKey

/-- This value records one random-oracle query. -/
structure HashRecord where
  input : BaseField
  output : Block × Block

/-- This state is shared by every simulator layer. -/
structure SimulatorState where
  fixedOracle : PermutationOracle Pipeline.FixedKeyIndex Block
  encOracle : PermutationOracle EncPRF.PermutationIndex Block
  hashOracle : EncPRF.HashOracle
  fixedTranscript : List (PermutationRecord Pipeline.FixedKeyIndex Block)
  encTranscript : List (PermutationRecord EncPRF.PermutationIndex Block)
  hashTranscript : List HashRecord
  commitments : List LabelCommitment
  linking : Option LinkingState
  bad : Bool

/-- This relation connects one permutation transcript to its oracle. -/
def PermutationTranscriptMatches (oracle : PermutationOracle Index Block)
    (history : List (PermutationRecord Index Block)) : Prop :=
  ∀ record ∈ history, oracle.permutation record.index record.domain = record.range

/-- This relation connects one random-oracle transcript to its oracle. -/
def HashTranscriptMatches (oracle : EncPRF.HashOracle) (history : List HashRecord) : Prop :=
  ∀ record ∈ history, oracle record.input = record.output

/-- A fresh random-oracle input does not occur in the transcript. -/
def FreshHashInput (history : List HashRecord) (input : BaseField) : Prop :=
  ∀ record ∈ history, record.input ≠ input

/-- This executable check tests random-oracle input freshness. -/
def freshHashInputCheck (history : List HashRecord) (input : BaseField) : Bool :=
  history.all fun record => decide (record.input ≠ input)

theorem freshHashInputCheck_eq_true (history : List HashRecord) (input : BaseField) :
    freshHashInputCheck history input = true ↔ FreshHashInput history input := by
  rw [freshHashInputCheck, List.all_eq_true]
  constructor
  · intro check record member
    exact of_decide_eq_true (check record member)
  · intro fresh record member
    exact decide_eq_true (fresh record member)

/-- This operation programs one permutation point by swapping two range values. -/
def programPermutation [DecidableEq Index] (oracle : PermutationOracle Index Block)
    (index : Index) (input output : Block) : PermutationOracle Index Block := {
  permutation := fun current => if current = index then
    (oracle.permutation current).trans
      (Equiv.swap (oracle.permutation current input) output)
  else oracle.permutation current
}

theorem programPermutation_apply [DecidableEq Index]
    (oracle : PermutationOracle Index Block) (index : Index) (input output : Block) :
    (programPermutation oracle index input output).permutation index input = output := by
  simp [programPermutation, Equiv.trans_apply, Equiv.swap_apply_left]

theorem programPermutation_symm [DecidableEq Index]
    (oracle : PermutationOracle Index Block) (index : Index) (input output : Block) :
    ((programPermutation oracle index input output).permutation index).symm output = input := by
  rw [Equiv.symm_apply_eq]
  exact (programPermutation_apply oracle index input output).symm

/-- Fresh programming preserves one prior permutation pair. -/
theorem programPermutation_preserves [DecidableEq Index]
    (oracle : PermutationOracle Index Block) (index : Index) (input output : Block)
    (record : PermutationRecord Index Block)
    (recordMatches : oracle.permutation record.index record.domain = record.range)
    (fresh : record.index = index → record.domain ≠ input ∧ record.range ≠ output) :
    (programPermutation oracle index input output).permutation record.index record.domain =
      record.range := by
  by_cases sameIndex : record.index = index
  · have different := fresh sameIndex
    have differentImage : record.range ≠ oracle.permutation record.index input := by
      rw [← recordMatches]
      exact (oracle.permutation record.index).injective.ne different.1
    simp only [programPermutation, if_pos sameIndex, Equiv.trans_apply]
    rw [recordMatches]
    exact Equiv.swap_apply_of_ne_of_ne differentImage different.2
  · simp [programPermutation, sameIndex, recordMatches]

/-- A matching permutation transcript defines one partial injection. -/
theorem permutationTranscriptMatches_consistent
    {oracle : PermutationOracle Index Block}
    {history : List (PermutationRecord Index Block)}
    (matchesOracle : PermutationTranscriptMatches oracle history) :
    ConsistentPermutationTranscript history := by
  intro first firstMember second secondMember sameIndex
  have firstMatches := matchesOracle first firstMember
  have secondMatches := matchesOracle second secondMember
  constructor
  · intro sameDomain
    rw [← firstMatches, ← secondMatches, sameIndex, sameDomain]
  · intro sameRange
    apply (oracle.permutation first.index).injective
    rw [firstMatches, sameRange, ← secondMatches, sameIndex]

/-- A matching hash transcript gives one output to each input. -/
theorem hashTranscriptMatches_consistent {oracle : EncPRF.HashOracle}
    {history : List HashRecord} (matchesOracle : HashTranscriptMatches oracle history) :
    ∀ first ∈ history, ∀ second ∈ history,
      first.input = second.input → first.output = second.output := by
  intro first firstMember second secondMember sameInput
  rw [← matchesOracle first firstMember, ← matchesOracle second secondMember, sameInput]

/-- This key uses the exact non-black-box relation. -/
def SimulatorState.linkedKey (state : SimulatorState) : Option InputMacKey :=
  state.linking.map fun linking =>
    linkedInputKey state.encOracle state.hashOracle linking.bridgeKey linking.sourceKey

/-- This invariant covers every public oracle and every layer label. -/
def SimulatorInvariant (state : SimulatorState) : Prop :=
  PermutationTranscriptMatches state.fixedOracle state.fixedTranscript ∧
    PermutationTranscriptMatches state.encOracle state.encTranscript ∧
      HashTranscriptMatches state.hashOracle state.hashTranscript ∧
      DistinctCommitments state.commitments

/-- The shared invariant gives consistent public-oracle transcripts. -/
theorem SimulatorInvariant.transcriptsConsistent {state : SimulatorState}
    (invariant : SimulatorInvariant state) :
    ConsistentPermutationTranscript state.fixedTranscript ∧
      ConsistentPermutationTranscript state.encTranscript :=
  ⟨permutationTranscriptMatches_consistent invariant.1,
    permutationTranscriptMatches_consistent invariant.2.1⟩

/-- This state uses the oracle functions from one random tape. -/
def initialState (randomness : Garbling.Randomness) : SimulatorState := {
  fixedOracle := randomness.fixedKeyOracle
  encOracle := randomness.encPRFOracle
  hashOracle := randomness.hashOracle
  fixedTranscript := []
  encTranscript := []
  hashTranscript := []
  commitments := []
  linking := none
  bad := false
}

theorem initialState_invariant (randomness : Garbling.Randomness) :
    SimulatorInvariant (initialState randomness) := by
  simp [SimulatorInvariant, initialState, PermutationTranscriptMatches,
    HashTranscriptMatches, DistinctCommitments]

/-- This operation programs one fresh fixed-key permutation pair. -/
def programFixed (state : SimulatorState) (index : Pipeline.FixedKeyIndex)
    (input output : Block) : SimulatorState :=
  { state with
    fixedOracle := programPermutation state.fixedOracle index input output
    fixedTranscript := PermutationRecord.mk .program .simulator index input output ::
      state.fixedTranscript }

/-- This operation programs one fresh EncPRF permutation pair. -/
def programEnc (state : SimulatorState) (index : EncPRF.PermutationIndex)
    (input output : Block) : SimulatorState :=
  { state with
    encOracle := programPermutation state.encOracle index input output
    encTranscript := PermutationRecord.mk .program .simulator index input output ::
      state.encTranscript }

/-- This operation programs one fresh random-oracle input. -/
def programHash (state : SimulatorState) (input : BaseField)
    (output : Block × Block) : SimulatorState :=
  { state with
    hashOracle := Function.update state.hashOracle input output
    hashTranscript := { input := input, output := output } :: state.hashTranscript }

/-- This operation records a programming collision. -/
def markBad (state : SimulatorState) : SimulatorState := { state with bad := true }

/-- This operation programs one fixed-key pair or records a collision. -/
def tryProgramFixed (state : SimulatorState) (index : Pipeline.FixedKeyIndex)
    (input output : Block) : SimulatorState :=
  if freshPermutationPairCheck state.fixedTranscript index input output
  then programFixed state index input output else markBad state

/-- This operation programs one EncPRF pair or records a collision. -/
def tryProgramEnc (state : SimulatorState) (index : EncPRF.PermutationIndex)
    (input output : Block) : SimulatorState :=
  if freshPermutationPairCheck state.encTranscript index input output
  then programEnc state index input output else markBad state

/-- This operation programs one random-oracle input or records a collision. -/
def tryProgramHash (state : SimulatorState) (input : BaseField)
    (output : Block × Block) : SimulatorState :=
  if freshHashInputCheck state.hashTranscript input
  then programHash state input output else markBad state

theorem programHash_apply (state : SimulatorState) (input : BaseField)
    (output : Block × Block) :
    (programHash state input output).hashOracle input = output := by
  exact Function.update_self input output state.hashOracle

/-- Fresh fixed-key programming preserves the shared invariant. -/
theorem programFixed_preservesInvariant {state : SimulatorState}
    {index : Pipeline.FixedKeyIndex} {input output : Block}
    (invariant : SimulatorInvariant state)
    (fresh : FreshPermutationPair state.fixedTranscript index input output) :
    SimulatorInvariant (programFixed state index input output) := by
  refine ⟨?_, invariant.2⟩
  intro record member
  simp only [programFixed, List.mem_cons] at member
  rcases member with rfl | member
  · exact programPermutation_apply state.fixedOracle index input output
  · exact programPermutation_preserves state.fixedOracle index input output record
      (invariant.1 record member) (fresh record member)

/-- Fresh EncPRF programming preserves the shared invariant. -/
theorem programEnc_preservesInvariant {state : SimulatorState}
    {index : EncPRF.PermutationIndex} {input output : Block}
    (invariant : SimulatorInvariant state)
    (fresh : FreshPermutationPair state.encTranscript index input output) :
    SimulatorInvariant (programEnc state index input output) := by
  refine ⟨invariant.1, ?_, invariant.2.2⟩
  intro record member
  simp only [programEnc, List.mem_cons] at member
  rcases member with rfl | member
  · exact programPermutation_apply state.encOracle index input output
  · exact programPermutation_preserves state.encOracle index input output record
      (invariant.2.1 record member) (fresh record member)

/-- Fresh random-oracle programming preserves the shared invariant. -/
theorem programHash_preservesInvariant {state : SimulatorState}
    {input : BaseField} {output : Block × Block}
    (invariant : SimulatorInvariant state)
    (fresh : FreshHashInput state.hashTranscript input) :
    SimulatorInvariant (programHash state input output) := by
  refine ⟨invariant.1, invariant.2.1, ?_, invariant.2.2.2⟩
  intro record member
  simp only [programHash, List.mem_cons] at member
  rcases member with rfl | member
  · exact programHash_apply state input output
  · change Function.update state.hashOracle input output record.input = record.output
    rw [Function.update_of_ne (fresh record member)]
    exact invariant.2.2.1 record member

/-- Checked fixed-key programming preserves the shared invariant. -/
theorem tryProgramFixed_preservesInvariant (state : SimulatorState)
    (index : Pipeline.FixedKeyIndex) (input output : Block)
    (invariant : SimulatorInvariant state) :
    SimulatorInvariant (tryProgramFixed state index input output) := by
  by_cases checked : freshPermutationPairCheck state.fixedTranscript index input output = true
  · have fresh := (freshPermutationPairCheck_eq_true _ _ _ _).mp checked
    simpa [tryProgramFixed, checked] using programFixed_preservesInvariant invariant fresh
  · simpa [tryProgramFixed, checked, markBad, SimulatorInvariant] using invariant

/-- Checked EncPRF programming preserves the shared invariant. -/
theorem tryProgramEnc_preservesInvariant (state : SimulatorState)
    (index : EncPRF.PermutationIndex) (input output : Block)
    (invariant : SimulatorInvariant state) :
    SimulatorInvariant (tryProgramEnc state index input output) := by
  by_cases checked : freshPermutationPairCheck state.encTranscript index input output = true
  · have fresh := (freshPermutationPairCheck_eq_true _ _ _ _).mp checked
    simpa [tryProgramEnc, checked] using programEnc_preservesInvariant invariant fresh
  · simpa [tryProgramEnc, checked, markBad, SimulatorInvariant] using invariant

/-- Checked random-oracle programming preserves the shared invariant. -/
theorem tryProgramHash_preservesInvariant (state : SimulatorState)
    (input : BaseField) (output : Block × Block)
    (invariant : SimulatorInvariant state) :
    SimulatorInvariant (tryProgramHash state input output) := by
  by_cases checked : freshHashInputCheck state.hashTranscript input = true
  · have fresh := (freshHashInputCheck_eq_true _ _).mp checked
    simpa [tryProgramHash, checked] using programHash_preservesInvariant invariant fresh
  · simpa [tryProgramHash, checked, markBad, SimulatorInvariant] using invariant

/-- Checked fixed-key programming succeeds or records a collision. -/
theorem tryProgramFixed_badOrFresh (state : SimulatorState)
    (index : Pipeline.FixedKeyIndex) (input output : Block) :
    (tryProgramFixed state index input output).bad = true ∨
      FreshPermutationPair state.fixedTranscript index input output := by
  by_cases checked : freshPermutationPairCheck state.fixedTranscript index input output = true
  · exact Or.inr ((freshPermutationPairCheck_eq_true _ _ _ _).mp checked)
  · simp [tryProgramFixed, checked, markBad]

/-- A non-bad result implies a non-bad prior state. -/
theorem tryProgramFixed_priorNotBad (state : SimulatorState)
    (index : Pipeline.FixedKeyIndex) (input output : Block)
    (notBad : (tryProgramFixed state index input output).bad = false) :
    state.bad = false := by
  by_cases checked : freshPermutationPairCheck state.fixedTranscript index input output = true
  · simpa [tryProgramFixed, checked, programFixed] using notBad
  · simp [tryProgramFixed, checked, markBad] at notBad

/-- A non-bad result contains the requested fixed-key pair. -/
theorem tryProgramFixed_apply_of_notBad (state : SimulatorState)
    (index : Pipeline.FixedKeyIndex) (input output : Block)
    (notBad : (tryProgramFixed state index input output).bad = false) :
    (tryProgramFixed state index input output).fixedOracle.permutation index input = output := by
  by_cases checked : freshPermutationPairCheck state.fixedTranscript index input output = true
  · simp [tryProgramFixed, checked, programFixed, programPermutation_apply]
  · simp [tryProgramFixed, checked, markBad] at notBad

/-- Programming a different index preserves one fixed-key pair. -/
theorem tryProgramFixed_preservesOther (state : SimulatorState)
    (oldIndex newIndex : Pipeline.FixedKeyIndex) (oldInput oldOutput input output : Block)
    (different : oldIndex ≠ newIndex)
    (prior : state.fixedOracle.permutation oldIndex oldInput = oldOutput) :
    (tryProgramFixed state newIndex input output).fixedOracle.permutation oldIndex oldInput =
      oldOutput := by
  by_cases checked : freshPermutationPairCheck state.fixedTranscript newIndex input output = true
  · simpa [tryProgramFixed, checked, programFixed, programPermutation, different] using prior
  · simpa [tryProgramFixed, checked, markBad] using prior

/-- Checked EncPRF programming succeeds or records a collision. -/
theorem tryProgramEnc_badOrFresh (state : SimulatorState)
    (index : EncPRF.PermutationIndex) (input output : Block) :
    (tryProgramEnc state index input output).bad = true ∨
      FreshPermutationPair state.encTranscript index input output := by
  by_cases checked : freshPermutationPairCheck state.encTranscript index input output = true
  · exact Or.inr ((freshPermutationPairCheck_eq_true _ _ _ _).mp checked)
  · simp [tryProgramEnc, checked, markBad]

/-- Checked random-oracle programming succeeds or records a collision. -/
theorem tryProgramHash_badOrFresh (state : SimulatorState)
    (input : BaseField) (output : Block × Block) :
    (tryProgramHash state input output).bad = true ∨
      FreshHashInput state.hashTranscript input := by
  by_cases checked : freshHashInputCheck state.hashTranscript input = true
  · exact Or.inr ((freshHashInputCheck_eq_true _ _).mp checked)
  · simp [tryProgramHash, checked, markBad]

/-- This operation records one fixed-key permutation pair. -/
def recordFixed (state : SimulatorState)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) : SimulatorState :=
  { state with fixedTranscript := record :: state.fixedTranscript }

/-- This operation records one EncPRF permutation pair. -/
def recordEnc (state : SimulatorState)
    (record : PermutationRecord EncPRF.PermutationIndex Block) : SimulatorState :=
  { state with encTranscript := record :: state.encTranscript }

/-- This operation records one random-oracle query. -/
def recordHash (state : SimulatorState) (record : HashRecord) : SimulatorState :=
  { state with hashTranscript := record :: state.hashTranscript }

/-- This operation records one label constraint. -/
def addCommitment (state : SimulatorState)
    (commitment : LabelCommitment) : SimulatorState :=
  { state with commitments := commitment :: state.commitments }

/-- A compatible fixed-key record preserves the shared invariant. -/
theorem recordFixed_preservesInvariant {state : SimulatorState}
    {record : PermutationRecord Pipeline.FixedKeyIndex Block}
    (invariant : SimulatorInvariant state)
    (recordMatches : state.fixedOracle.permutation record.index record.domain = record.range) :
    SimulatorInvariant (recordFixed state record) := by
  exact ⟨by simpa [PermutationTranscriptMatches, recordFixed] using And.intro recordMatches invariant.1,
    invariant.2⟩

/-- A compatible EncPRF record preserves the shared invariant. -/
theorem recordEnc_preservesInvariant {state : SimulatorState}
    {record : PermutationRecord EncPRF.PermutationIndex Block}
    (invariant : SimulatorInvariant state)
    (recordMatches : state.encOracle.permutation record.index record.domain = record.range) :
    SimulatorInvariant (recordEnc state record) := by
  exact ⟨invariant.1,
    by simpa [PermutationTranscriptMatches, recordEnc] using And.intro recordMatches invariant.2.1,
    invariant.2.2⟩

/-- An exact random-oracle record preserves the shared invariant. -/
theorem recordHash_preservesInvariant {state : SimulatorState} {record : HashRecord}
    (invariant : SimulatorInvariant state)
    (recordMatches : state.hashOracle record.input = record.output) :
    SimulatorInvariant (recordHash state record) := by
  exact ⟨invariant.1, invariant.2.1,
    by simpa [HashTranscriptMatches, recordHash] using And.intro recordMatches invariant.2.2.1,
    invariant.2.2.2⟩

/-- A fresh label constraint preserves the shared invariant. -/
theorem addCommitment_preservesInvariant {state : SimulatorState}
    {commitment : LabelCommitment}
    (invariant : SimulatorInvariant state)
    (fresh : ∀ prior ∈ state.commitments,
      commitment.wire ≠ prior.wire ∧ commitment.label ≠ prior.label) :
    SimulatorInvariant (addCommitment state commitment) := by
  exact ⟨invariant.1, invariant.2.1, invariant.2.2.1,
    List.pairwise_cons.mpr ⟨fresh, invariant.2.2.2⟩⟩

/-- This handler records every public-oracle query with its origin. -/
def oracleHandlerFor (origin : PermutationOrigin) :
    OracleHandler Garbling.oracleSpec SimulatorState
  | .fixedForward index input, state =>
      let output := state.fixedOracle.permutation index input
      (output, recordFixed state
        (PermutationRecord.mk .forward origin index input output))
  | .fixedInverse index output, state =>
      let input := (state.fixedOracle.permutation index).symm output
      (input, recordFixed state
        (PermutationRecord.mk .inverse origin index input output))
  | .encForward index input, state =>
      let output := state.encOracle.permutation index input
      (output, recordEnc state
        (PermutationRecord.mk .forward origin index input output))
  | .encInverse index output, state =>
      let input := (state.encOracle.permutation index).symm output
      (input, recordEnc state
        (PermutationRecord.mk .inverse origin index input output))
  | .hash input, state =>
      let output := state.hashOracle input
      (output, recordHash state { input := input, output := output })

/-- The ideal handler records every adversary query. -/
def idealOracleHandler : OracleHandler Garbling.oracleSpec SimulatorState :=
  oracleHandlerFor .adversary

/-- This handler records every construction query. -/
def constructionOracleHandler : OracleHandler Garbling.oracleSpec SimulatorState :=
  oracleHandlerFor .construction

/-- Every public-oracle query preserves the shared invariant. -/
theorem oracleHandlerFor_preservesInvariant (origin : PermutationOrigin)
    (query : Garbling.oracleSpec.Query)
    (state : SimulatorState) (invariant : SimulatorInvariant state) :
    SimulatorInvariant (oracleHandlerFor origin query state).2 := by
  cases query <;> simp only [oracleHandlerFor]
  · exact recordFixed_preservesInvariant invariant rfl
  · exact recordFixed_preservesInvariant invariant (Equiv.apply_symm_apply _ _)
  · exact recordEnc_preservesInvariant invariant rfl
  · exact recordEnc_preservesInvariant invariant (Equiv.apply_symm_apply _ _)
  · exact recordHash_preservesInvariant invariant rfl

theorem idealOracleHandler_preservesInvariant (query : Garbling.oracleSpec.Query)
    (state : SimulatorState) (invariant : SimulatorInvariant state) :
    SimulatorInvariant (idealOracleHandler query state).2 :=
  oracleHandlerFor_preservesInvariant .adversary query state invariant

end Kriterion.ArgoMAC.Security
