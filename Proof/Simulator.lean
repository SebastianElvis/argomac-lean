/-
This file defines one simulator state for all ArgoMAC layers.
The paper uses shared state in `gc_optimizations.tex`.
The paper source is https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/gc_optimizations.tex.
-/

import Proof.Linking

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

universe uSample uDomain uRange uIndex uSlot
  uQuery uAnswer uResult uStateOne uStateTwo

/-- An equivalence preserves the uniform distribution on one finite type. -/
theorem map_uniformOfFintype_equiv
    {Sample : Type uSample} [Fintype Sample] [Nonempty Sample]
    (equivalence : Sample ≃ Sample) :
    (PMF.uniformOfFintype Sample).map equivalence =
      PMF.uniformOfFintype Sample := by
  classical
  apply PMF.ext
  intro output
  rw [PMF.map_apply, PMF.uniformOfFintype_apply]
  simp only [PMF.uniformOfFintype_apply, ← equivalence.symm_apply_eq,
    eq_comm]
  exact (tsum_ite_eq (equivalence.symm output)
    (Inv.inv (Fintype.card Sample : ENNReal))).symm

/-- A handler equivalence lifts through every oracle program. -/
theorem oracleProgram_run_stateEquiv
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (stateEquiv : StateOne ≃ StateTwo)
    (handlerEquiv : ∀ query state,
      (handlerOne query state).1 =
          (handlerTwo query (stateEquiv state)).1 ∧
        stateEquiv (handlerOne query state).2 =
          (handlerTwo query (stateEquiv state)).2)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (state : StateOne) :
    (program.run handlerOne state).map
        (fun output => (output.1, stateEquiv output.2)) =
      program.run handlerTwo (stateEquiv state) := by
  induction program generalizing state with
  | pure result =>
      rw [OracleProgram.run, OracleProgram.run, PMF.map_comp]
      congr 1
  | query request next inductionHypothesis =>
      simp only [OracleProgram.run]
      have related := handlerEquiv request state
      rw [show (handlerOne request state).1 =
        (handlerTwo request (stateEquiv state)).1 from related.1]
      rw [inductionHypothesis]
      rw [related.2]
  | sample distribution next inductionHypothesis =>
      simp only [OracleProgram.run, PMF.map_bind]
      congr 1
      funext sample
      exact inductionHypothesis sample state

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

/-- This map programs one point and returns its old range value. -/
def swapProgramPair [DecidableEq Index]
    (index : Index) (input : Block) :
    PermutationOracle Index Block × Block →
      PermutationOracle Index Block × Block :=
  fun sample =>
    (programPermutation sample.1 index input sample.2,
      sample.1.permutation index input)

theorem programPermutation_apply [DecidableEq Index]
    (oracle : PermutationOracle Index Block) (index : Index) (input output : Block) :
    (programPermutation oracle index input output).permutation index input = output := by
  simp [programPermutation, Equiv.trans_apply, Equiv.swap_apply_left]

theorem programPermutation_symm [DecidableEq Index]
    (oracle : PermutationOracle Index Block) (index : Index) (input output : Block) :
    ((programPermutation oracle index input output).permutation index).symm output = input := by
  rw [Equiv.symm_apply_eq]
  exact (programPermutation_apply oracle index input output).symm

/-- Applying the swap-programming map two times restores its input. -/
theorem swapProgramPair_involutive [DecidableEq Index]
    (index : Index) (input : Block) :
    Function.Involutive (swapProgramPair index input) := by
  intro sample
  rcases sample with ⟨oracle, target⟩
  refine Prod.ext ?_ ?_
  · change programPermutation
      (programPermutation oracle index input target) index input
        (oracle.permutation index input) = oracle
    cases oracle with
    | mk permutation =>
      change PermutationOracle.mk _ = PermutationOracle.mk permutation
      rw [PermutationOracle.mk.injEq]
      funext current
      by_cases sameIndex : current = index
      · subst current
        apply Equiv.ext
        intro value
        simp only [programPermutation, if_pos, Equiv.trans_apply,
          Equiv.swap_apply_left]
        rw [Equiv.swap_comm target]
        exact Equiv.swap_apply_self _ _ _
      · simp [programPermutation, sameIndex]
  · exact programPermutation_apply oracle index input target

/-- This equivalence contains the swap-programming map. -/
noncomputable def swapProgramEquiv [DecidableEq Index]
    (index : Index) (input : Block) :
    (PermutationOracle Index Block × Block) ≃
      (PermutationOracle Index Block × Block) :=
  (swapProgramPair_involutive index input).toPerm

/-- Fresh swap programming preserves the uniform joint distribution exactly. -/
theorem map_uniform_swapProgramPair
    [Fintype Index] [DecidableEq Index]
    (index : Index) (input : Block) :
    (PMF.uniformOfFintype (PermutationOracle Index Block × Block)).map
        (swapProgramPair index input) =
      PMF.uniformOfFintype (PermutationOracle Index Block × Block) :=
  map_uniformOfFintype_equiv (swapProgramEquiv (Index := Index) index input)

/-- This map programs one point from one coordinate of a target tape. -/
def swapProgramTapeStep {Index : Type uIndex} {Slot : Type uSlot}
    [DecidableEq Index] [DecidableEq Slot]
    (index : Index) (input : Block) (slot : Slot) :
    PermutationOracle Index Block × (Slot → Block) →
      PermutationOracle Index Block × (Slot → Block) :=
  fun sample =>
    (programPermutation sample.1 index input (sample.2 slot),
      Function.update sample.2 slot (sample.1.permutation index input))

/-- Applying one target-tape step two times restores its input. -/
theorem swapProgramTapeStep_involutive
    {Index : Type uIndex} {Slot : Type uSlot}
    [DecidableEq Index] [DecidableEq Slot]
    (index : Index) (input : Block) (slot : Slot) :
    Function.Involutive (swapProgramTapeStep index input slot) := by
  intro sample
  rcases sample with ⟨oracle, tape⟩
  refine Prod.ext ?_ ?_
  · simp only [swapProgramTapeStep, Function.update_self]
    exact congrArg Prod.fst
      (swapProgramPair_involutive index input (oracle, tape slot))
  · funext current
    by_cases sameSlot : current = slot
    · subst current
      simp [swapProgramTapeStep, programPermutation_apply]
    · simp [swapProgramTapeStep, sameSlot]

/-- This equivalence contains one target-tape step. -/
noncomputable def swapProgramTapeStepEquiv
    {Index : Type uIndex} {Slot : Type uSlot}
    [DecidableEq Index] [DecidableEq Slot]
    (index : Index) (input : Block) (slot : Slot) :
    (PermutationOracle Index Block × (Slot → Block)) ≃
      (PermutationOracle Index Block × (Slot → Block)) :=
  (swapProgramTapeStep_involutive index input slot).toPerm

/-- One target-tape step preserves its uniform joint distribution exactly. -/
theorem map_uniform_swapProgramTapeStep
    {Index : Type uIndex} {Slot : Type uSlot}
    [Fintype Index] [DecidableEq Index]
    [Fintype Slot] [DecidableEq Slot]
    (index : Index) (input : Block) (slot : Slot) :
    (PMF.uniformOfFintype
      (PermutationOracle Index Block × (Slot → Block))).map
        (swapProgramTapeStep index input slot) =
      PMF.uniformOfFintype
        (PermutationOracle Index Block × (Slot → Block)) :=
  map_uniformOfFintype_equiv
    (swapProgramTapeStepEquiv index input slot)

/-- This equivalence composes a fixed list of target-tape steps. -/
noncomputable def swapProgramTapeScheduleEquiv
    {Index : Type uIndex} {Slot : Type uSlot}
    [DecidableEq Index] [DecidableEq Slot] :
    List (Index × Block × Slot) →
      (PermutationOracle Index Block × (Slot → Block)) ≃
        (PermutationOracle Index Block × (Slot → Block))
  | [] => Equiv.refl _
  | point :: rest =>
      (swapProgramTapeStepEquiv point.1 point.2.1 point.2.2).trans
        (swapProgramTapeScheduleEquiv rest)

/-- A fixed swap-programming schedule preserves the uniform joint tape exactly. -/
theorem map_uniform_swapProgramTapeSchedule
    {Index : Type uIndex} {Slot : Type uSlot}
    [Fintype Index] [DecidableEq Index]
    [Fintype Slot] [DecidableEq Slot]
    (schedule : List (Index × Block × Slot)) :
    (PMF.uniformOfFintype
      (PermutationOracle Index Block × (Slot → Block))).map
        (swapProgramTapeScheduleEquiv schedule) =
      PMF.uniformOfFintype
        (PermutationOracle Index Block × (Slot → Block)) :=
  map_uniformOfFintype_equiv
    (swapProgramTapeScheduleEquiv schedule)

/-- This map programs one function point and returns its old output. -/
def updateProgramPair {Domain : Type uDomain} {Range : Type uRange}
    [DecidableEq Domain] (input : Domain) :
    (Domain → Range) × Range → (Domain → Range) × Range :=
  fun sample =>
    (Function.update sample.1 input sample.2, sample.1 input)

/-- Applying the function-programming map two times restores its input. -/
theorem updateProgramPair_involutive
    {Domain : Type uDomain} {Range : Type uRange} [DecidableEq Domain]
    (input : Domain) : Function.Involutive
      (updateProgramPair (Range := Range) input) := by
  intro sample
  rcases sample with ⟨oracle, target⟩
  refine Prod.ext ?_ ?_
  · funext current
    by_cases sameInput : current = input
    · subst current
      simp [updateProgramPair]
    · simp [updateProgramPair]
  · simp [updateProgramPair]

/-- This equivalence contains the function-programming map. -/
noncomputable def updateProgramEquiv
    {Domain : Type uDomain} {Range : Type uRange} [DecidableEq Domain]
    (input : Domain) :
    ((Domain → Range) × Range) ≃ ((Domain → Range) × Range) :=
  (updateProgramPair_involutive (Range := Range) input).toPerm

/-- Fresh function programming preserves the uniform joint distribution exactly. -/
theorem map_uniform_updateProgramPair
    {Domain : Type uDomain} {Range : Type uRange}
    [Fintype Domain] [DecidableEq Domain] [Fintype Range] [Nonempty Range]
    (input : Domain) :
    (PMF.uniformOfFintype ((Domain → Range) × Range)).map
        (updateProgramPair input) =
      PMF.uniformOfFintype ((Domain → Range) × Range) :=
  map_uniformOfFintype_equiv
    (updateProgramEquiv (Range := Range) input)

/-- A different function query has the same answer after programming. -/
theorem updateProgramPair_apply_of_ne
    {Domain : Type uDomain} {Range : Type uRange} [DecidableEq Domain]
    (oracle : Domain → Range) (input : Domain) (target : Range)
    (current : Domain) (different : current ≠ input) :
    (updateProgramPair input (oracle, target)).1 current = oracle current := by
  simp [updateProgramPair, different]

/-- This type contains one fresh hash target that matches a fixed transcript. -/
def FreshHashProgrammingSample (history : List HashRecord)
    (input : BaseField) :=
  { sample : EncPRF.HashOracle × (Block × Block) //
    HashTranscriptMatches sample.1 history ∧ FreshHashInput history input }

/-- A matching hash oracle and one fresh input give a nonempty fiber. -/
theorem freshHashProgrammingSample_nonempty (history : List HashRecord)
    (input : BaseField) (oracle : EncPRF.HashOracle)
    (matchesTranscript : HashTranscriptMatches oracle history)
    (fresh : FreshHashInput history input) :
    Nonempty (FreshHashProgrammingSample history input) :=
  ⟨⟨(oracle, (0, 0)), matchesTranscript, fresh⟩⟩

noncomputable instance freshHashProgrammingSampleFintype
    (history : List HashRecord) (input : BaseField) :
    Fintype (FreshHashProgrammingSample history input) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun sample : EncPRF.HashOracle × (Block × Block) =>
      HashTranscriptMatches sample.1 history ∧ FreshHashInput history input) (by simp)

/-- This map swaps one fresh hash target inside a fixed transcript fiber. -/
def swapFreshHashProgrammingSample (history : List HashRecord)
    (input : BaseField) :
    FreshHashProgrammingSample history input →
      FreshHashProgrammingSample history input := by
  intro sample
  refine ⟨updateProgramPair input sample.1, ?_⟩
  constructor
  · intro record member
    change Function.update sample.1.1 input sample.1.2 record.input = record.output
    rw [Function.update_of_ne (sample.2.2 record member)]
    exact sample.2.1 record member
  · exact sample.2.2

/-- The fresh hash swap is an involution inside its transcript fiber. -/
theorem swapFreshHashProgrammingSample_involutive
    (history : List HashRecord) (input : BaseField) :
    Function.Involutive (swapFreshHashProgrammingSample history input) := by
  intro sample
  apply Subtype.ext
  exact updateProgramPair_involutive input sample.1

/-- This equivalence contains the fresh hash swap in one transcript fiber. -/
noncomputable def swapFreshHashProgrammingSampleEquiv
    (history : List HashRecord) (input : BaseField) :
    FreshHashProgrammingSample history input ≃
      FreshHashProgrammingSample history input :=
  (swapFreshHashProgrammingSample_involutive history input).toPerm

/-- Fresh hash programming preserves a uniform transcript fiber exactly. -/
theorem map_uniform_swapFreshHashProgrammingSample
    (history : List HashRecord) (input : BaseField)
    [Nonempty (FreshHashProgrammingSample history input)] :
    (PMF.uniformOfFintype
      (FreshHashProgrammingSample history input)).map
        (swapFreshHashProgrammingSample history input) =
      PMF.uniformOfFintype
        (FreshHashProgrammingSample history input) :=
  map_uniformOfFintype_equiv
    (swapFreshHashProgrammingSampleEquiv history input)

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

/-- A fresh forward query has the same answer after swap programming. -/
theorem programPermutation_forward_eq_of_fresh [DecidableEq Index]
    (oracle : PermutationOracle Index Block) (index : Index)
    (input target : Block) (current : Index) (domain : Block)
    (fresh : current = index →
      domain ≠ input ∧ oracle.permutation current domain ≠ target) :
    (programPermutation oracle index input target).permutation current domain =
      oracle.permutation current domain := by
  exact programPermutation_preserves oracle index input target
    (PermutationRecord.mk .forward .adversary current domain
      (oracle.permutation current domain)) rfl fresh

/-- A fresh inverse query has the same answer after swap programming. -/
theorem programPermutation_inverse_eq_of_fresh [DecidableEq Index]
    (oracle : PermutationOracle Index Block) (index : Index)
    (input target : Block) (current : Index) (range : Block)
    (fresh : current = index →
      range ≠ oracle.permutation current input ∧ range ≠ target) :
    ((programPermutation oracle index input target).permutation current).symm range =
      (oracle.permutation current).symm range := by
  let domain := (oracle.permutation current).symm range
  have domainFresh : current = index → domain ≠ input ∧ range ≠ target := by
    intro sameIndex
    have freshAtIndex := fresh sameIndex
    constructor
    · intro sameDomain
      apply freshAtIndex.1
      calc
        range = oracle.permutation current domain :=
          (oracle.permutation current).apply_symm_apply range |>.symm
        _ = oracle.permutation current input := congrArg _ sameDomain
    · exact freshAtIndex.2
  have preserved :
      (programPermutation oracle index input target).permutation current domain = range :=
    programPermutation_preserves oracle index input target
      (PermutationRecord.mk .inverse .adversary current domain range)
      (Equiv.apply_symm_apply (oracle.permutation current) range) domainFresh
  apply (programPermutation oracle index input target).permutation current |>.injective
  rw [Equiv.apply_symm_apply, preserved]

/-- This type contains one fresh programming pair that matches a fixed transcript. -/
def FreshProgrammingSample {Index : Type uIndex} [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block) :=
  { sample : PermutationOracle Index Block × Block //
    PermutationTranscriptMatches sample.1 history ∧
      FreshPermutationPair history index input sample.2 }

/-- A matching oracle and one fresh domain give a nonempty fiber. -/
theorem freshProgrammingSample_nonempty
    {Index : Type uIndex} [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block) (oracle : PermutationOracle Index Block)
    (matchesTranscript : PermutationTranscriptMatches oracle history)
    (freshDomain : ∀ record ∈ history, record.index = index →
      record.domain ≠ input) :
    Nonempty (FreshProgrammingSample history index input) := by
  refine ⟨⟨(oracle, oracle.permutation index input), matchesTranscript, ?_⟩⟩
  intro record member sameIndex
  constructor
  · exact freshDomain record member sameIndex
  · intro sameRange
    apply freshDomain record member sameIndex
    apply (oracle.permutation record.index).injective
    rw [matchesTranscript record member]
    simpa [sameIndex] using sameRange

noncomputable instance freshProgrammingSampleFintype
    {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block) :
    Fintype (FreshProgrammingSample history index input) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun sample : PermutationOracle Index Block × Block =>
      PermutationTranscriptMatches sample.1 history ∧
        FreshPermutationPair history index input sample.2) (by simp)

/-- This map swaps one fresh pair inside a fixed transcript fiber. -/
def swapFreshProgrammingSample
    {Index : Type uIndex} [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block) :
    FreshProgrammingSample history index input →
      FreshProgrammingSample history index input := by
  intro sample
  refine ⟨swapProgramPair index input sample.1, ?_⟩
  constructor
  · intro record member
    exact programPermutation_preserves sample.1.1 index input sample.1.2
      record (sample.2.1 record member) (sample.2.2 record member)
  · intro record member sameIndex
    have fresh := sample.2.2 record member sameIndex
    constructor
    · exact fresh.1
    · intro sameRange
      apply fresh.1
      apply (sample.1.1.permutation record.index).injective
      rw [sample.2.1 record member]
      simpa [sameIndex] using sameRange

/-- The fresh swap map is an involution inside its transcript fiber. -/
theorem swapFreshProgrammingSample_involutive
    {Index : Type uIndex} [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block) :
    Function.Involutive
      (swapFreshProgrammingSample history index input) := by
  intro sample
  apply Subtype.ext
  exact swapProgramPair_involutive index input sample.1

/-- This equivalence contains the fresh swap map in one transcript fiber. -/
noncomputable def swapFreshProgrammingSampleEquiv
    {Index : Type uIndex} [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block) :
    FreshProgrammingSample history index input ≃
      FreshProgrammingSample history index input :=
  (swapFreshProgrammingSample_involutive history index input).toPerm

/-- Fresh swap programming preserves a uniform transcript fiber exactly. -/
theorem map_uniform_swapFreshProgrammingSample
    {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block)
    [Nonempty (FreshProgrammingSample history index input)] :
    (PMF.uniformOfFintype
      (FreshProgrammingSample history index input)).map
        (swapFreshProgrammingSample history index input) =
      PMF.uniformOfFintype
        (FreshProgrammingSample history index input) :=
  map_uniformOfFintype_equiv
    (swapFreshProgrammingSampleEquiv history index input)

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
