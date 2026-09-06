/-
This file proves scalar-independent distribution transport for public values.
-/

import Proof.PublicSample

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

universe uSource uTarget uSample uIndex

/-- An equivalence transports a finite uniform distribution between two types. -/
theorem map_uniformOfFintype_equivBetween
    {Source : Type uSource} {Target : Type uTarget}
    [Fintype Source] [Nonempty Source] [Fintype Target] [Nonempty Target]
    (equivalence : Source ≃ Target) :
    (PMF.uniformOfFintype Source).map equivalence =
      PMF.uniformOfFintype Target := by
  classical
  apply PMF.ext
  intro output
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply]
  simp only [← equivalence.symm_apply_eq, eq_comm]
  rw [Fintype.card_congr equivalence]
  exact (tsum_ite_eq (equivalence.symm output)
    (Inv.inv (Fintype.card Target : ENNReal))).symm

/-- The second part of a finite uniform product is uniform. -/
theorem map_uniform_prod_snd
    {First : Type uSource} {Second : Type uTarget}
    [Fintype First] [Nonempty First] [Fintype Second] [Nonempty Second] :
    (PMF.uniformOfFintype (First × Second)).map Prod.snd =
      PMF.uniformOfFintype Second := by
  classical
  apply PMF.ext
  intro output
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod]
  rw [ENNReal.tsum_prod']
  push_cast
  rw [ENNReal.mul_inv] <;> try simp [Fintype.card_ne_zero]
  rw [tsum_eq_single output]
  · simp only [if_pos]
    rw [← mul_assoc, ENNReal.mul_inv_cancel]
    · simp
    · exact_mod_cast Fintype.card_ne_zero
    · simp
  · intro other different
    simp [Ne.symm different]

/-- The first part of a finite uniform product is uniform. -/
theorem map_uniform_prod_fst
    {First : Type uSource} {Second : Type uTarget}
    [Fintype First] [Nonempty First] [Fintype Second] [Nonempty Second] :
    (PMF.uniformOfFintype (First × Second)).map Prod.fst =
      PMF.uniformOfFintype First := by
  calc
    (PMF.uniformOfFintype (First × Second)).map Prod.fst =
        ((PMF.uniformOfFintype (First × Second)).map
          (Equiv.prodComm First Second)).map Prod.snd := by
            rw [PMF.map_comp]
            rfl
    _ = (PMF.uniformOfFintype (Second × First)).map Prod.snd := by
      rw [map_uniformOfFintype_equivBetween]
    _ = PMF.uniformOfFintype First := map_uniform_prod_snd

/-- A function that ignores the second uniform part keeps its first marginal. -/
theorem map_uniform_prod_ignore_snd
    {First : Type uSource} {Second : Type uTarget} {Output : Type uSample}
    [Fintype First] [Nonempty First] [Fintype Second] [Nonempty Second]
    (function : First → Output) :
    (PMF.uniformOfFintype (First × Second)).map (function ∘ Prod.fst) =
      (PMF.uniformOfFintype First).map function := by
  rw [← PMF.map_comp]
  rw [map_uniform_prod_fst]

/-- A finite uniform product is two independent uniform samples. -/
theorem uniform_prod_eq_bind
    {First : Type uSource} {Second : Type uTarget}
    [Fintype First] [Nonempty First] [Fintype Second] [Nonempty Second] :
    PMF.uniformOfFintype (First × Second) =
      (PMF.uniformOfFintype Second).bind fun second =>
        (PMF.uniformOfFintype First).map fun first => (first, second) := by
  classical
  apply PMF.ext
  intro output
  rcases output with ⟨first, second⟩
  rw [PMF.bind_apply]
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, Fintype.card_prod]
  push_cast
  rw [tsum_eq_single second]
  · rw [tsum_eq_single first]
    · simp only [if_pos]
      rw [ENNReal.mul_inv] <;> try simp [Fintype.card_ne_zero]
      ac_rfl
    · intro other different
      simp [Ne.symm different]
  · intro other different
    simp [Ne.symm different]

/-- Equal uniform fiber laws give one uniform mixed law. -/
theorem map_uniform_prod_of_uniform_fiber
    {First : Type uSource} {Second : Type uTarget} {Output : Type uSample}
    [Fintype First] [Nonempty First] [Fintype Second] [Nonempty Second]
    [Fintype Output] [Nonempty Output]
    (function : First → Second → Output)
    (fiber : ∀ second,
      (PMF.uniformOfFintype First).map (fun first => function first second) =
        PMF.uniformOfFintype Output) :
    (PMF.uniformOfFintype (First × Second)).map
        (fun sample => function sample.1 sample.2) =
      PMF.uniformOfFintype Output := by
  rw [uniform_prod_eq_bind]
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  simp only [Function.comp_def]
  simp_rw [fiber]
  exact PMF.bind_const _ _

/-- Equal uniform second-part laws give one uniform mixed law. -/
theorem map_uniform_prod_of_uniform_snd_fiber
    {First : Type uSource} {Second : Type uTarget} {Output : Type uSample}
    [Fintype First] [Nonempty First] [Fintype Second] [Nonempty Second]
    [Fintype Output] [Nonempty Output]
    (function : First → Second → Output)
    (fiber : ∀ first,
      (PMF.uniformOfFintype Second).map (function first) =
        PMF.uniformOfFintype Output) :
    (PMF.uniformOfFintype (First × Second)).map
        (fun sample => function sample.1 sample.2) =
      PMF.uniformOfFintype Output := by
  calc
    (PMF.uniformOfFintype (First × Second)).map
        (fun sample => function sample.1 sample.2) =
      ((PMF.uniformOfFintype (First × Second)).map
        (Equiv.prodComm First Second)).map
          (fun sample => function sample.2 sample.1) := by
        rw [PMF.map_comp]
        rfl
    _ = (PMF.uniformOfFintype (Second × First)).map
        (fun sample => function sample.2 sample.1) := by
      rw [map_uniformOfFintype_equivBetween]
    _ = PMF.uniformOfFintype Output := by
      exact map_uniform_prod_of_uniform_fiber
        (First := Second) (Second := First) (Output := Output)
        (fun second first => function first second) fiber

/-- The fixed-key oracle is uniform in the complete garbling tape. -/
theorem map_uniform_garblingRandomness_fixedKeyOracle
    (witness : Garbling.Randomness) :
    letI : Nonempty Garbling.Randomness := ⟨witness⟩
    (PMF.uniformOfFintype Garbling.Randomness).map
        Garbling.Randomness.fixedKeyOracle =
      PMF.uniformOfFintype
        (PermutationOracle Pipeline.FixedKeyIndex Block) := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  letI : Nonempty GarblingRandomnessRest := ⟨garblingRandomnessRest witness⟩
  calc
    (PMF.uniformOfFintype Garbling.Randomness).map
        Garbling.Randomness.fixedKeyOracle =
      ((PMF.uniformOfFintype Garbling.Randomness).map
        garblingRandomnessFixedOracleEquiv).map Prod.fst := by
          rw [PMF.map_comp]
          rfl
    _ = (PMF.uniformOfFintype
        (PermutationOracle Pipeline.FixedKeyIndex Block × GarblingRandomnessRest)).map
          Prod.fst := by rw [map_uniformOfFintype_equivBetween]
    _ = PMF.uniformOfFintype
        (PermutationOracle Pipeline.FixedKeyIndex Block) := map_uniform_prod_fst

/-- The security tape keeps the exact uniform fixed-key-oracle marginal. -/
theorem map_randomTape_fixedKeyOracle
    (witness : Garbling.Randomness) (parameter : Nat) :
    (randomTape witness parameter).map Garbling.Randomness.fixedKeyOracle =
      PMF.uniformOfFintype
        (PermutationOracle Pipeline.FixedKeyIndex Block) := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  rw [randomTape]
  exact map_uniform_garblingRandomness_fixedKeyOracle witness

/-- A swap-programmed target tape keeps a uniform marginal. -/
theorem map_uniform_swapProgramTapeSchedule_snd
    {Index : Type uIndex} {Slot : Type uSample}
    [Fintype Index] [DecidableEq Index]
    [Fintype Slot] [DecidableEq Slot]
    (schedule : List (Index × Block × Slot)) :
    (PMF.uniformOfFintype
      (PermutationOracle Index Block × (Slot → Block))).map
        (fun sample => (swapProgramTapeScheduleEquiv schedule sample).2) =
      PMF.uniformOfFintype (Slot → Block) := by
  rw [show (fun sample => (swapProgramTapeScheduleEquiv schedule sample).2) =
      Prod.snd ∘ swapProgramTapeScheduleEquiv schedule from rfl]
  rw [← PMF.map_comp]
  rw [map_uniform_swapProgramTapeSchedule]
  exact map_uniform_prod_snd

/-- This schedule reads the three hash permutations for one fixed gate. -/
def hashTapeSchedule (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block) :
    List (Pipeline.FixedKeyIndex × Block × Fin 3) :=
  [
    (fixedKeyIndex location window (.hash 0), label, 0),
    (fixedKeyIndex location window (.hash 1), label, 1),
    (fixedKeyIndex location window (.hash 2), label, 2)
  ]

/-- The schedule tape contains the original three permutation outputs. -/
theorem swapProgramHashTapeSchedule_snd
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (tape : Fin 3 → Block) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block) :
    (swapProgramTapeScheduleEquiv (hashTapeSchedule location window label)
      (oracle, tape)).2 =
      fun slot => oracle.permutation (fixedKeyIndex location window (.hash slot)) label := by
  funext slot
  fin_cases slot <;>
    simp [hashTapeSchedule, swapProgramTapeScheduleEquiv,
      swapProgramTapeStepEquiv, Function.Involutive.toPerm,
      swapProgramTapeStep, programPermutation, fixedKeyIndex]

/-- Three fixed-gate permutation outputs are jointly uniform. -/
theorem map_uniform_fixedHashBlocks
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block)).map
        (fun (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) slot => oracle.permutation
          (fixedKeyIndex location window (.hash slot)) label) =
      PMF.uniformOfFintype (Fin 3 → Block) := by
  let output : PermutationOracle Pipeline.FixedKeyIndex Block → Fin 3 → Block :=
    fun oracle slot => oracle.permutation
      (fixedKeyIndex location window (.hash slot)) label
  rw [← map_uniform_prod_ignore_snd
    (Second := Fin 3 → Block) output]
  calc
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block × (Fin 3 → Block))).map
        (output ∘ Prod.fst) =
      (PMF.uniformOfFintype
        (PermutationOracle Pipeline.FixedKeyIndex Block × (Fin 3 → Block))).map
          (fun sample => (swapProgramTapeScheduleEquiv
            (hashTapeSchedule location window label) sample).2) := by
        congr 1
        funext sample
        exact (swapProgramHashTapeSchedule_snd sample.1 sample.2
          location window label).symm
    _ = PMF.uniformOfFintype (Fin 3 → Block) :=
      map_uniform_swapProgramTapeSchedule_snd _

/-- This map applies Davies--Meyer feed-forward to three blocks. -/
def xorHashBlockTape (label : Block) (tape : Fin 3 → Block) : Fin 3 → Block :=
  fun slot => tape slot ^^^ label

theorem xorHashBlockTape_involutive (label : Block) :
    Function.Involutive (xorHashBlockTape label) := by
  intro tape
  funext slot
  simp only [xorHashBlockTape]
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Davies--Meyer feed-forward is an equivalence on the three-block tape. -/
def xorHashBlockTapeEquiv (label : Block) :
    (Fin 3 → Block) ≃ (Fin 3 → Block) :=
  (xorHashBlockTape_involutive label).toPerm

/-- Three fixed-gate Davies--Meyer blocks are jointly uniform. -/
theorem map_uniform_fixedDaviesMeyerBlocks
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block)).map
        (fun (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) slot =>
          oracle.permutation (fixedKeyIndex location window (.hash slot)) label ^^^ label) =
      PMF.uniformOfFintype (Fin 3 → Block) := by
  let output : PermutationOracle Pipeline.FixedKeyIndex Block → Fin 3 → Block :=
    fun oracle slot => oracle.permutation
      (fixedKeyIndex location window (.hash slot)) label
  rw [show (fun (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) slot =>
      oracle.permutation (fixedKeyIndex location window (.hash slot)) label ^^^ label) =
      xorHashBlockTape label ∘ output from rfl]
  rw [← PMF.map_comp]
  rw [map_uniform_fixedHashBlocks]
  exact map_uniformOfFintype_equivBetween (xorHashBlockTapeEquiv label)

/-- This schedule reads the two pad permutations for one fixed gate. -/
def padTapeSchedule (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block) :
    List (Pipeline.FixedKeyIndex × Block × Fin 2) :=
  [
    (fixedKeyIndex location window (.pad 0), label, 0),
    (fixedKeyIndex location window (.pad 1), label, 1)
  ]

/-- The schedule tape contains the original two permutation outputs. -/
theorem swapProgramPadTapeSchedule_snd
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (tape : Fin 2 → Block) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block) :
    (swapProgramTapeScheduleEquiv (padTapeSchedule location window label)
      (oracle, tape)).2 =
      fun slot => oracle.permutation (fixedKeyIndex location window (.pad slot)) label := by
  funext slot
  fin_cases slot <;>
    simp [padTapeSchedule, swapProgramTapeScheduleEquiv,
      swapProgramTapeStepEquiv, Function.Involutive.toPerm,
      swapProgramTapeStep, programPermutation, fixedKeyIndex]

/-- Two fixed-gate permutation outputs are jointly uniform. -/
theorem map_uniform_fixedPadBlocks
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block)).map
        (fun (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) slot => oracle.permutation
          (fixedKeyIndex location window (.pad slot)) label) =
      PMF.uniformOfFintype (Fin 2 → Block) := by
  let output : PermutationOracle Pipeline.FixedKeyIndex Block → Fin 2 → Block :=
    fun oracle slot => oracle.permutation
      (fixedKeyIndex location window (.pad slot)) label
  rw [← map_uniform_prod_ignore_snd
    (Second := Fin 2 → Block) output]
  calc
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block × (Fin 2 → Block))).map
        (output ∘ Prod.fst) =
      (PMF.uniformOfFintype
        (PermutationOracle Pipeline.FixedKeyIndex Block × (Fin 2 → Block))).map
          (fun sample => (swapProgramTapeScheduleEquiv
            (padTapeSchedule location window label) sample).2) := by
        congr 1
        funext sample
        exact (swapProgramPadTapeSchedule_snd sample.1 sample.2
          location window label).symm
    _ = PMF.uniformOfFintype (Fin 2 → Block) :=
      map_uniform_swapProgramTapeSchedule_snd _

/-- This map applies Davies--Meyer feed-forward to two blocks. -/
def xorPadBlockTape (label : Block) (tape : Fin 2 → Block) : Fin 2 → Block :=
  fun slot => tape slot ^^^ label

theorem xorPadBlockTape_involutive (label : Block) :
    Function.Involutive (xorPadBlockTape label) := by
  intro tape
  funext slot
  simp only [xorPadBlockTape]
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Davies--Meyer feed-forward is an equivalence on the two-block tape. -/
def xorPadBlockTapeEquiv (label : Block) :
    (Fin 2 → Block) ≃ (Fin 2 → Block) :=
  (xorPadBlockTape_involutive label).toPerm

/-- Two fixed-gate Davies--Meyer pad blocks are jointly uniform. -/
theorem map_uniform_fixedDaviesMeyerPadBlocks
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block)).map
        (fun (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) slot =>
          oracle.permutation (fixedKeyIndex location window (.pad slot)) label ^^^ label) =
      PMF.uniformOfFintype (Fin 2 → Block) := by
  let output : PermutationOracle Pipeline.FixedKeyIndex Block → Fin 2 → Block :=
    fun oracle slot => oracle.permutation
      (fixedKeyIndex location window (.pad slot)) label
  rw [show (fun (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) slot =>
      oracle.permutation (fixedKeyIndex location window (.pad slot)) label ^^^ label) =
      xorPadBlockTape label ∘ output from rfl]
  rw [← PMF.map_comp]
  rw [map_uniform_fixedPadBlocks]
  exact map_uniformOfFintype_equivBetween (xorPadBlockTapeEquiv label)

/-- A distinct-index, distinct-slot schedule reads each entry at its slot. -/
theorem swapProgramTapeSchedule_snd_reads
    {Index : Type uIndex} {Slot : Type uSample}
    [DecidableEq Index] [DecidableEq Slot]
    (schedule : List (Index × Block × Slot))
    (slotNodup : (schedule.map (fun entry => entry.2.2)).Nodup)
    (indexNodup : (schedule.map (fun entry => entry.1)).Nodup)
    (oracle : PermutationOracle Index Block) (tape : Slot → Block) :
    (∀ entry ∈ schedule,
        (swapProgramTapeScheduleEquiv schedule (oracle, tape)).2 entry.2.2 =
          oracle.permutation entry.1 entry.2.1) ∧
      (∀ slot, slot ∉ schedule.map (fun entry => entry.2.2) →
        (swapProgramTapeScheduleEquiv schedule (oracle, tape)).2 slot = tape slot) := by
  induction schedule generalizing oracle tape with
  | nil => exact ⟨by simp, by intro slot _; rfl⟩
  | cons head rest ih =>
      have stepEq :
          swapProgramTapeScheduleEquiv (head :: rest) (oracle, tape) =
            swapProgramTapeScheduleEquiv rest
              (swapProgramTapeStep head.1 head.2.1 head.2.2 (oracle, tape)) := rfl
      rw [List.map_cons] at slotNodup indexNodup
      obtain ⟨headSlotFresh, slotNodupRest⟩ := List.nodup_cons.mp slotNodup
      obtain ⟨headIndexFresh, indexNodupRest⟩ := List.nodup_cons.mp indexNodup
      set stepped := swapProgramTapeStep head.1 head.2.1 head.2.2 (oracle, tape)
        with steppedDef
      have steppedOracle : stepped.1 =
          programPermutation oracle head.1 head.2.1 (tape head.2.2) := rfl
      have steppedTape : stepped.2 =
          Function.update tape head.2.2 (oracle.permutation head.1 head.2.1) := rfl
      obtain ⟨readRest, unchangedRest⟩ :=
        ih slotNodupRest indexNodupRest stepped.1 stepped.2
      rw [stepEq]
      refine ⟨?_, ?_⟩
      · intro entry entryMem
        rcases List.mem_cons.mp entryMem with headEq | restMem
        · subst headEq
          rw [unchangedRest entry.2.2 headSlotFresh, steppedTape,
            Function.update_self]
        · have indexNe : entry.1 ≠ head.1 := by
            intro same
            exact headIndexFresh (same ▸ List.mem_map_of_mem restMem)
          rw [readRest entry restMem, steppedOracle]
          simp [programPermutation, indexNe]
      · intro slot slotFresh
        rw [List.map_cons, List.mem_cons] at slotFresh
        push_neg at slotFresh
        obtain ⟨slotNeHead, slotFreshRest⟩ := slotFresh
        rw [unchangedRest slot slotFreshRest, steppedTape,
          Function.update_of_ne slotNeHead]

/-- Reading distinct fixed-key indices gives jointly uniform blocks. -/
theorem map_uniform_distinctReads
    {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
    {n : Nat} (index : Fin n → Index) (input : Fin n → Block)
    (hindex : Function.Injective index) :
    (PMF.uniformOfFintype (PermutationOracle Index Block)).map
        (fun oracle i => oracle.permutation (index i) (input i)) =
      PMF.uniformOfFintype (Fin n → Block) := by
  classical
  let schedule : List (Index × Block × Fin n) :=
    List.ofFn (fun i => (index i, input i, i))
  have slotNodup : (schedule.map (fun entry => entry.2.2)).Nodup := by
    simp only [schedule, List.map_ofFn]
    exact List.nodup_ofFn.mpr fun a b h => h
  have indexNodup : (schedule.map (fun entry => entry.1)).Nodup := by
    simp only [schedule, List.map_ofFn]
    exact List.nodup_ofFn.mpr hindex
  let output : PermutationOracle Index Block → Fin n → Block :=
    fun oracle i => oracle.permutation (index i) (input i)
  rw [← map_uniform_prod_ignore_snd (Second := Fin n → Block) output]
  calc
    (PMF.uniformOfFintype
      (PermutationOracle Index Block × (Fin n → Block))).map (output ∘ Prod.fst) =
      (PMF.uniformOfFintype
        (PermutationOracle Index Block × (Fin n → Block))).map
          (fun sample => (swapProgramTapeScheduleEquiv schedule sample).2) := by
        congr 1
        funext sample
        funext i
        have entryMem : (index i, input i, i) ∈ schedule :=
          List.mem_ofFn.mpr ⟨i, rfl⟩
        exact ((swapProgramTapeSchedule_snd_reads schedule slotNodup indexNodup
          sample.1 sample.2).1 (index i, input i, i) entryMem).symm
    _ = PMF.uniformOfFintype (Fin n → Block) :=
      map_uniform_swapProgramTapeSchedule_snd _

/-- This schedule reads the three hash and two pad permutations for one gate. -/
def hashPadTapeSchedule (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block) :
    List (Pipeline.FixedKeyIndex × Block × (Fin 3 ⊕ Fin 2)) :=
  [
    (fixedKeyIndex location window (.hash 0), label, Sum.inl 0),
    (fixedKeyIndex location window (.hash 1), label, Sum.inl 1),
    (fixedKeyIndex location window (.hash 2), label, Sum.inl 2),
    (fixedKeyIndex location window (.pad 0), label, Sum.inr 0),
    (fixedKeyIndex location window (.pad 1), label, Sum.inr 1)
  ]

/-- This map reads one gate's five permutations into one hash-pad tape. -/
def hashPadBlocks (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    (Fin 3 ⊕ Fin 2) → Block
  | Sum.inl s => oracle.permutation (fixedKeyIndex location window (.hash s)) label
  | Sum.inr s => oracle.permutation (fixedKeyIndex location window (.pad s)) label

/-- The schedule tape contains the original five permutation outputs. -/
theorem swapProgramHashPadTapeSchedule_snd
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (tape : (Fin 3 ⊕ Fin 2) → Block) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block) :
    (swapProgramTapeScheduleEquiv (hashPadTapeSchedule location window label)
      (oracle, tape)).2 =
      hashPadBlocks oracle location window label := by
  funext slot
  cases slot with
  | inl s =>
      fin_cases s <;>
        simp [hashPadTapeSchedule, hashPadBlocks, swapProgramTapeScheduleEquiv,
          swapProgramTapeStepEquiv, Function.Involutive.toPerm,
          swapProgramTapeStep, programPermutation, fixedKeyIndex]
  | inr s =>
      fin_cases s <;>
        simp [hashPadTapeSchedule, hashPadBlocks, swapProgramTapeScheduleEquiv,
          swapProgramTapeStepEquiv, Function.Involutive.toPerm,
          swapProgramTapeStep, programPermutation, fixedKeyIndex]

/-- Five fixed-gate permutation outputs are jointly uniform. -/
theorem map_uniform_fixedHashPadBlocks
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block)).map
        (fun oracle => hashPadBlocks oracle location window label) =
      PMF.uniformOfFintype ((Fin 3 ⊕ Fin 2) → Block) := by
  let output : PermutationOracle Pipeline.FixedKeyIndex Block →
      (Fin 3 ⊕ Fin 2) → Block :=
    fun oracle => hashPadBlocks oracle location window label
  rw [← map_uniform_prod_ignore_snd
    (Second := (Fin 3 ⊕ Fin 2) → Block) output]
  calc
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block ×
        ((Fin 3 ⊕ Fin 2) → Block))).map (output ∘ Prod.fst) =
      (PMF.uniformOfFintype
        (PermutationOracle Pipeline.FixedKeyIndex Block ×
          ((Fin 3 ⊕ Fin 2) → Block))).map
          (fun sample => (swapProgramTapeScheduleEquiv
            (hashPadTapeSchedule location window label) sample).2) := by
        congr 1
        funext sample
        exact (swapProgramHashPadTapeSchedule_snd sample.1 sample.2
          location window label).symm
    _ = PMF.uniformOfFintype ((Fin 3 ⊕ Fin 2) → Block) :=
      map_uniform_swapProgramTapeSchedule_snd _

/-- This equivalence joins the two Davies--Meyer groups of one gate. -/
def hashPadDaviesMeyerEquiv (label : Block) :
    ((Fin 3 ⊕ Fin 2) → Block) ≃ ((Fin 3 → Block) × (Fin 2 → Block)) :=
  (Equiv.sumArrowEquivProdArrow (Fin 3) (Fin 2) Block).trans
    ((xorHashBlockTapeEquiv label).prodCongr (xorPadBlockTapeEquiv label))

/-- One gate's hash blocks and pad blocks are jointly uniform after feed-forward. -/
theorem map_uniform_fixedDaviesMeyerHashPadBlocks
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block)).map
        (fun oracle =>
          ((fun s : Fin 3 => oracle.permutation
              (fixedKeyIndex location window (.hash s)) label ^^^ label),
            (fun s : Fin 2 => oracle.permutation
              (fixedKeyIndex location window (.pad s)) label ^^^ label))) =
      PMF.uniformOfFintype ((Fin 3 → Block) × (Fin 2 → Block)) := by
  rw [show (fun oracle : PermutationOracle Pipeline.FixedKeyIndex Block =>
      ((fun s : Fin 3 => oracle.permutation
          (fixedKeyIndex location window (.hash s)) label ^^^ label),
        (fun s : Fin 2 => oracle.permutation
          (fixedKeyIndex location window (.pad s)) label ^^^ label))) =
      hashPadDaviesMeyerEquiv label ∘
        (fun oracle => hashPadBlocks oracle location window label) from rfl]
  rw [← PMF.map_comp]
  rw [map_uniform_fixedHashPadBlocks]
  exact map_uniformOfFintype_equivBetween (hashPadDaviesMeyerEquiv label)

/-- This map splits one ciphertext into its two blocks. -/
def splitCiphertextBlocks (value : BitAdaptor.Ciphertext)
    (index : Fin 2) : Block :=
  value.extractLsb' (index.val * 128) 128

/-- This map joins two blocks into one ciphertext. -/
def ciphertextBlocksValue (blocks : Fin 2 → Block) : BitAdaptor.Ciphertext :=
  blocks 1 ++ blocks 0

theorem splitCiphertextBlocks_value (value : BitAdaptor.Ciphertext) :
    ciphertextBlocksValue (splitCiphertextBlocks value) = value := by
  simp only [ciphertextBlocksValue, splitCiphertextBlocks]
  change value.extractLsb' 128 128 ++ value.extractLsb' 0 128 = value
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
    (by decide : 128 = 0 + 128)]
  simp

theorem splitCiphertextBlocks_ciphertextBlocksValue
    (blocks : Fin 2 → Block) :
    splitCiphertextBlocks (ciphertextBlocksValue blocks) = blocks := by
  funext index
  fin_cases index
  · simp only [splitCiphertextBlocks, ciphertextBlocksValue]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
    simp
  · simp only [splitCiphertextBlocks, ciphertextBlocksValue]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    simp

/-- Two blocks and one 256-bit ciphertext contain the same bits. -/
def ciphertextBlockEquiv :
    BitAdaptor.Ciphertext ≃ (Fin 2 → Block) where
  toFun := splitCiphertextBlocks
  invFun := ciphertextBlocksValue
  left_inv := splitCiphertextBlocks_value
  right_inv := splitCiphertextBlocks_ciphertextBlocksValue

/-- This type contains each 256-bit ciphertext. -/
abbrev FullCiphertext := Fin (2 ^ 256)

/-- A full ciphertext is exactly two fixed-key blocks. -/
def fullCiphertextBlockEquiv : FullCiphertext ≃ (Fin 2 → Block) :=
  BitVec.equivFin.symm.toEquiv.trans ciphertextBlockEquiv

/-- This value is the complete Davies--Meyer pad for one fixed gate. -/
def fixedDaviesMeyerPadLift (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) : FullCiphertext :=
  BitVec.equivFin (BitAdaptor.padBytes
    (Pipeline.fixedKeyPermutations oracle location window) label)

theorem fixedDaviesMeyerPadLift_eq
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) :
    fixedDaviesMeyerPadLift location window label oracle =
      fullCiphertextBlockEquiv.symm
        (fun slot => oracle.permutation
          (fixedKeyIndex location window (.pad slot)) label ^^^ label) := by
  rfl

/-- One fixed gate has an exact uniform 256-bit Davies--Meyer pad. -/
theorem map_uniform_fixedDaviesMeyerPadLift
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block)).map
        (fixedDaviesMeyerPadLift location window label) =
      PMF.uniformOfFintype FullCiphertext := by
  rw [show fixedDaviesMeyerPadLift location window label =
      fullCiphertextBlockEquiv.symm ∘
        (fun (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) slot =>
          oracle.permutation (fixedKeyIndex location window (.pad slot)) label ^^^ label) by
        funext oracle
        exact fixedDaviesMeyerPadLift_eq location window label oracle]
  rw [← PMF.map_comp]
  rw [map_uniform_fixedDaviesMeyerPadBlocks]
  exact map_uniformOfFintype_equivBetween fullCiphertextBlockEquiv.symm

/-- XOR by one fixed ciphertext is an involution. -/
def xorCiphertext (mask : BitAdaptor.Ciphertext)
    (value : BitAdaptor.Ciphertext) : BitAdaptor.Ciphertext :=
  value ^^^ mask

theorem xorCiphertext_involutive (mask : BitAdaptor.Ciphertext) :
    Function.Involutive (xorCiphertext mask) := by
  intro value
  simp only [xorCiphertext]
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- XOR by one fixed ciphertext is an equivalence. -/
def xorCiphertextEquiv (mask : BitAdaptor.Ciphertext) :
    BitAdaptor.Ciphertext ≃ BitAdaptor.Ciphertext :=
  (xorCiphertext_involutive mask).toPerm

/-- XOR by one fixed ciphertext is an equivalence on its finite index. -/
def xorFullCiphertextEquiv (mask : BitAdaptor.Ciphertext) :
    FullCiphertext ≃ FullCiphertext :=
  (BitVec.equivFin.symm.toEquiv.trans (xorCiphertextEquiv mask)).trans
    BitVec.equivFin.toEquiv

/-- This value is one real encrypted field row. -/
def fixedEncryptedFieldLift (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block) (message : BaseField)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) : FullCiphertext :=
  BitVec.equivFin
    ((Pipeline.fixedKeyWindow oracle location window).encrypt label message)

theorem fixedEncryptedFieldLift_eq
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (message : BaseField)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) :
    fixedEncryptedFieldLift location window label message oracle =
      xorFullCiphertextEquiv (BitAdaptor.fieldBytes message)
        (fixedDaviesMeyerPadLift location window label oracle) := by
  rfl

/-- One fixed real encrypted field row is exactly uniform on 256 bits. -/
theorem map_uniform_fixedEncryptedFieldLift
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (message : BaseField) :
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block)).map
        (fixedEncryptedFieldLift location window label message) =
      PMF.uniformOfFintype FullCiphertext := by
  rw [show fixedEncryptedFieldLift location window label message =
      xorFullCiphertextEquiv (BitAdaptor.fieldBytes message) ∘
        fixedDaviesMeyerPadLift location window label by
      funext oracle
      exact fixedEncryptedFieldLift_eq location window label message oracle]
  rw [← PMF.map_comp]
  rw [map_uniform_fixedDaviesMeyerPadLift]
  exact map_uniformOfFintype_equivBetween
    (xorFullCiphertextEquiv (BitAdaptor.fieldBytes message))

/-- Pad extraction preserves every hash-permutation output. -/
theorem swapProgramPadTapeSchedule_hash_apply
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (tape : Fin 2 → Block) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (padLabel hashLabel : Block) (slot : Fin 3) :
    (swapProgramTapeScheduleEquiv (padTapeSchedule location window padLabel)
      (oracle, tape)).1.permutation
        (fixedKeyIndex location window (.hash slot)) hashLabel =
      oracle.permutation (fixedKeyIndex location window (.hash slot)) hashLabel := by
  fin_cases slot <;>
    simp [padTapeSchedule, swapProgramTapeScheduleEquiv,
      swapProgramTapeStepEquiv, Function.Involutive.toPerm,
      swapProgramTapeStep, programPermutation, fixedKeyIndex]

/-- Pad extraction preserves the hash-to-field result. -/
theorem swapProgramPadTapeSchedule_hashToField
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (tape : Fin 2 → Block) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (padLabel hashLabel : Block) :
    (Pipeline.fixedKeyWindow
      (swapProgramTapeScheduleEquiv (padTapeSchedule location window padLabel)
        (oracle, tape)).1 location window).hashToField hashLabel =
      (Pipeline.fixedKeyWindow oracle location window).hashToField hashLabel := by
  simp [Pipeline.fixedKeyWindow, BitAdaptor.fixedKeyOracle,
    BitAdaptor.hashBytes, Pipeline.fixedKeyPermutations, padTapeSchedule,
    swapProgramTapeScheduleEquiv, swapProgramTapeStepEquiv,
    Function.Involutive.toPerm, swapProgramTapeStep, programPermutation,
    fixedKeyIndex]

/-- A separated pad tape encrypts one hash-dependent field value bijectively. -/
def separatedEncryptedFieldEquiv
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (falseLabel trueLabel : Block) (slope : BaseField) :
    (Fin 2 → Block) ≃ FullCiphertext :=
  ((xorPadBlockTapeEquiv trueLabel).trans fullCiphertextBlockEquiv.symm).trans
    (xorFullCiphertextEquiv (BitAdaptor.fieldBytes
      (slope + (Pipeline.fixedKeyWindow oracle location window).hashToField falseLabel)))

/-- This map encrypts one field value from a separated oracle and pad tape. -/
def separatedEncryptedFieldLift
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (falseLabel trueLabel : Block) (slope : BaseField)
    (sample : PermutationOracle Pipeline.FixedKeyIndex Block × (Fin 2 → Block)) :
    FullCiphertext :=
  separatedEncryptedFieldEquiv sample.1 location window
    falseLabel trueLabel slope sample.2

/-- A separated hash-dependent field ciphertext is exactly uniform. -/
theorem map_uniform_separatedEncryptedFieldLift
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (falseLabel trueLabel : Block) (slope : BaseField) :
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block × (Fin 2 → Block))).map
        (separatedEncryptedFieldLift location window falseLabel trueLabel slope) =
      PMF.uniformOfFintype FullCiphertext := by
  exact map_uniform_prod_of_uniform_snd_fiber
    (Output := FullCiphertext)
    (fun oracle tape => separatedEncryptedFieldLift location window
      falseLabel trueLabel slope (oracle, tape))
    (fun oracle => map_uniformOfFintype_equivBetween
      (separatedEncryptedFieldEquiv oracle location window
        falseLabel trueLabel slope))

/-- Pad extraction maps one real true row to its separated form. -/
theorem fixedBitAdaptorTrueRow_swap
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (tape : Fin 2 → Block) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (key : BitAdaptor.Key) (slope : BaseField) :
    BitVec.equivFin
        (BitAdaptor.garble (Pipeline.fixedKeyWindow oracle location window)
          slope key).1.trueRow =
      separatedEncryptedFieldLift location window key.falseLabel
        key.trueLabel slope
        (swapProgramTapeScheduleEquiv
          (padTapeSchedule location window key.trueLabel) (oracle, tape)) := by
  simp only [separatedEncryptedFieldLift,
    separatedEncryptedFieldEquiv, Equiv.trans_apply,
    xorPadBlockTapeEquiv, xorFullCiphertextEquiv, xorCiphertextEquiv,
    Function.Involutive.toPerm, BitAdaptor.garble]
  rw [swapProgramPadTapeSchedule_snd]
  rw [swapProgramPadTapeSchedule_hashToField]
  rfl

/-- This value is the real ciphertext row of one bit adaptor. -/
def realBitAdaptorTrueRowLift
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (key : BitAdaptor.Key) (slope : BaseField)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) : FullCiphertext :=
  BitVec.equivFin
    (BitAdaptor.garble (Pipeline.fixedKeyWindow oracle location window)
      slope key).1.trueRow

theorem realBitAdaptorTrueRowLift_eq_separated
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (key : BitAdaptor.Key) (slope : BaseField) :
    realBitAdaptorTrueRowLift location window key slope ∘ Prod.fst =
      separatedEncryptedFieldLift location window key.falseLabel
        key.trueLabel slope ∘
          swapProgramTapeScheduleEquiv
            (padTapeSchedule location window key.trueLabel) := by
  funext sample
  exact fixedBitAdaptorTrueRow_swap sample.1 sample.2
    location window key slope

/-- One real bit-adaptor ciphertext row is exactly uniform on 256 bits. -/
theorem map_uniform_realBitAdaptorTrueRowLift
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (key : BitAdaptor.Key) (slope : BaseField) :
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block)).map
        (realBitAdaptorTrueRowLift location window key slope) =
      PMF.uniformOfFintype FullCiphertext := by
  let output : PermutationOracle Pipeline.FixedKeyIndex Block → FullCiphertext :=
    realBitAdaptorTrueRowLift location window key slope
  rw [← map_uniform_prod_ignore_snd
    (Second := Fin 2 → Block) output]
  change (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block × (Fin 2 → Block))).map
        (realBitAdaptorTrueRowLift location window key slope ∘ Prod.fst) = _
  rw [realBitAdaptorTrueRowLift_eq_separated]
  calc
    (PMF.uniformOfFintype
        (PermutationOracle Pipeline.FixedKeyIndex Block × (Fin 2 → Block))).map
          (separatedEncryptedFieldLift location window key.falseLabel
            key.trueLabel slope ∘
              swapProgramTapeScheduleEquiv
                (padTapeSchedule location window key.trueLabel)) =
      ((PMF.uniformOfFintype
        (PermutationOracle Pipeline.FixedKeyIndex Block × (Fin 2 → Block))).map
          (swapProgramTapeScheduleEquiv
            (padTapeSchedule location window key.trueLabel))).map
          (separatedEncryptedFieldLift location window key.falseLabel
            key.trueLabel slope) := by rw [PMF.map_comp]
    _ = (PMF.uniformOfFintype
        (PermutationOracle Pipeline.FixedKeyIndex Block × (Fin 2 → Block))).map
          (separatedEncryptedFieldLift location window key.falseLabel
            key.trueLabel slope) := by
      rw [map_uniform_swapProgramTapeSchedule]
    _ = PMF.uniformOfFintype FullCiphertext :=
      map_uniform_separatedEncryptedFieldLift
        location window key.falseLabel key.trueLabel slope

/-- A real row stays uniform when its key and slope depend on the rest tape. -/
theorem map_uniform_garblingRandomness_dependentRealBitAdaptorTrueRowLift
    (witness : Garbling.Randomness)
    (location : GarblingRandomnessRest → Pipeline.FixedKeyLocation)
    (window : GarblingRandomnessRest → Nat)
    (key : GarblingRandomnessRest → BitAdaptor.Key)
    (slope : GarblingRandomnessRest → BaseField) :
    letI : Nonempty Garbling.Randomness := ⟨witness⟩
    (PMF.uniformOfFintype Garbling.Randomness).map
        (fun randomness =>
          let rest := garblingRandomnessRest randomness
          realBitAdaptorTrueRowLift (location rest) (window rest)
            (key rest) (slope rest) randomness.fixedKeyOracle) =
      PMF.uniformOfFintype FullCiphertext := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  letI : Nonempty GarblingRandomnessRest := ⟨garblingRandomnessRest witness⟩
  rw [show (fun randomness : Garbling.Randomness =>
      let rest := garblingRandomnessRest randomness
      realBitAdaptorTrueRowLift (location rest) (window rest)
        (key rest) (slope rest) randomness.fixedKeyOracle) =
      (fun sample => realBitAdaptorTrueRowLift
        (location sample.2) (window sample.2) (key sample.2)
        (slope sample.2) sample.1) ∘ garblingRandomnessFixedOracleEquiv by rfl]
  rw [← PMF.map_comp]
  rw [map_uniformOfFintype_equivBetween]
  exact map_uniform_prod_of_uniform_fiber
    (First := PermutationOracle Pipeline.FixedKeyIndex Block)
    (Second := GarblingRandomnessRest)
    (Output := FullCiphertext)
    (fun oracle rest => realBitAdaptorTrueRowLift
      (location rest) (window rest) (key rest) (slope rest) oracle)
    (fun rest => map_uniform_realBitAdaptorTrueRowLift
      (location rest) (window rest) (key rest) (slope rest))

/-- The security tape gives every rest-dependent real row a uniform marginal. -/
theorem map_randomTape_dependentRealBitAdaptorTrueRowLift
    (witness : Garbling.Randomness) (parameter : Nat)
    (location : GarblingRandomnessRest → Pipeline.FixedKeyLocation)
    (window : GarblingRandomnessRest → Nat)
    (key : GarblingRandomnessRest → BitAdaptor.Key)
    (slope : GarblingRandomnessRest → BaseField) :
    (randomTape witness parameter).map
        (fun randomness =>
          let rest := garblingRandomnessRest randomness
          realBitAdaptorTrueRowLift (location rest) (window rest)
            (key rest) (slope rest) randomness.fixedKeyOracle) =
      PMF.uniformOfFintype FullCiphertext := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  rw [randomTape]
  exact map_uniform_garblingRandomness_dependentRealBitAdaptorTrueRowLift
    witness location window key slope

/-- A finite union has at most the sum of its local event bounds. -/
theorem finiteBadEventUnionMass_le
    {Sample : Type uSample} {Index : Type uIndex} [Fintype Index]
    (measure : MeasureTheory.OuterMeasure Sample) (event : Index → Set Sample)
    (bound : ENNReal) (localBound : ∀ index, measure (event index) ≤ bound) :
    measure (⋃ index, event index) ≤ (Fintype.card Index : ENNReal) * bound := by
  calc
    measure (⋃ index, event index) ≤ ∑ index, measure (event index) :=
      MeasureTheory.measure_iUnion_fintype_le measure event
    _ ≤ ∑ _index : Index, bound := Finset.sum_le_sum fun index _ => localBound index
    _ = (Fintype.card Index : ENNReal) * bound := by simp

/-- A digit adaptor offset does not depend on its private slope. -/
theorem digitBitsK_independentOfSlope
    (windows : Nat → BitAdaptor.FixedKeyOracle)
    (firstSlope secondSlope : BaseField) (key : CoordinateMacKey) :
    DigitAdaptor.bitsK (DigitAdaptor.garble windows firstSlope key).2 =
      DigitAdaptor.bitsK (DigitAdaptor.garble windows secondSlope key).2 := by
  simp [DigitAdaptor.bitsK, DigitAdaptor.garble, BitAdaptor.garble]

/-- This offset is the public-mask context of one digit adaptor. -/
def digitPublicOffset (windows : Nat → BitAdaptor.FixedKeyOracle)
    (key : CoordinateMacKey) : BaseField :=
  DigitAdaptor.bitsK (DigitAdaptor.garble windows 0 key).2

/-- The low value is an additive pivot for one 254-bit digit offset. -/
def digitOffsetPairTransport
    (sample : BaseField × (Fin 253 → BaseField)) :
    BaseField × (Fin 253 → BaseField) :=
  (2 * DigitAdaptor.fromBits sample.2 + sample.1, sample.2)

/-- This map recovers the low value from one digit offset. -/
def digitOffsetPairTransportInverse
    (sample : BaseField × (Fin 253 → BaseField)) :
    BaseField × (Fin 253 → BaseField) :=
  (sample.1 - 2 * DigitAdaptor.fromBits sample.2, sample.2)

theorem digitOffsetPairTransport_leftInverse :
    Function.LeftInverse digitOffsetPairTransportInverse
      digitOffsetPairTransport := by
  intro sample
  cases sample
  simp only [digitOffsetPairTransportInverse, digitOffsetPairTransport]
  apply Prod.ext
  · simp only
    ring
  · rfl

theorem digitOffsetPairTransport_rightInverse :
    Function.RightInverse digitOffsetPairTransportInverse
      digitOffsetPairTransport := by
  intro sample
  cases sample
  simp only [digitOffsetPairTransportInverse, digitOffsetPairTransport]
  apply Prod.ext
  · simp only
    ring
  · rfl

/-- One digit offset and its tail are equivalent to all 254 values. -/
def digitOffsetPairEquiv :
    (BaseField × (Fin 253 → BaseField)) ≃
      (BaseField × (Fin 253 → BaseField)) where
  toFun := digitOffsetPairTransport
  invFun := digitOffsetPairTransportInverse
  left_inv := digitOffsetPairTransport_leftInverse
  right_inv := digitOffsetPairTransport_rightInverse

/-- This equivalence exposes one digit offset and keeps its tail. -/
def digitOffsetVectorEquiv :
    (Fin coordinateBitCount → BaseField) ≃
      (BaseField × (Fin 253 → BaseField)) :=
  (Fin.insertNthEquiv (fun _ : Fin coordinateBitCount => BaseField) 0).symm.trans
    digitOffsetPairEquiv

set_option maxRecDepth 100000 in
theorem digitOffsetVectorEquiv_fst
    (values : Fin coordinateBitCount → BaseField) :
    (digitOffsetVectorEquiv values).1 = DigitAdaptor.fromBits values := by
  change 2 * DigitAdaptor.fromBits (fun index : Fin 253 => values index.succ) +
    values ⟨0, by decide⟩ = DigitAdaptor.fromBits values
  rw [DigitAdaptor.fromBits, Fin.foldr_succ]
  rfl

/-- A uniform vector gives an exact uniform digit offset. -/
theorem map_uniform_digitOffset :
    (PMF.uniformOfFintype (Fin coordinateBitCount → BaseField)).map
        DigitAdaptor.fromBits =
      PMF.uniformOfFintype BaseField := by
  rw [show DigitAdaptor.fromBits = Prod.fst ∘ digitOffsetVectorEquiv by
    funext values
    exact (digitOffsetVectorEquiv_fst values).symm]
  rw [← PMF.map_comp]
  rw [map_uniformOfFintype_equivBetween]
  exact map_uniform_prod_fst

/-- Addition by one fixed field value is an equivalence. -/
def addFieldEquiv (offset : BaseField) : BaseField ≃ BaseField where
  toFun value := value + offset
  invFun value := value - offset
  left_inv := by intro value; ring
  right_inv := by intro value; ring

/-- Adding a fixed value preserves a uniform digit offset. -/
theorem map_uniform_digitOffset_add (offset : BaseField) :
    (PMF.uniformOfFintype (Fin coordinateBitCount → BaseField)).map
        (fun values => DigitAdaptor.fromBits values + offset) =
      PMF.uniformOfFintype BaseField := by
  rw [show (fun values : Fin coordinateBitCount → BaseField =>
      DigitAdaptor.fromBits values + offset) =
      addFieldEquiv offset ∘ DigitAdaptor.fromBits from rfl]
  rw [← PMF.map_comp]
  rw [map_uniform_digitOffset]
  exact map_uniformOfFintype_equivBetween (addFieldEquiv offset)

/-- Two independent digit-offset vectors give one uniform zero pad. -/
theorem map_uniform_twoDigitOffsetSum :
    (PMF.uniformOfFintype
      ((Fin coordinateBitCount → BaseField) ×
        (Fin coordinateBitCount → BaseField))).map
        (fun sample => DigitAdaptor.fromBits sample.1 +
          DigitAdaptor.fromBits sample.2) =
      PMF.uniformOfFintype BaseField := by
  exact map_uniform_prod_of_uniform_fiber
    (First := Fin coordinateBitCount → BaseField)
    (Second := Fin coordinateBitCount → BaseField)
    (Output := BaseField)
    (fun first second => DigitAdaptor.fromBits first +
      DigitAdaptor.fromBits second)
    (fun second => map_uniform_digitOffset_add
      (DigitAdaptor.fromBits second))

/-- The public digit offset is the weighted false-label hash vector. -/
theorem digitPublicOffset_eq_fromBits
    (windows : Nat → BitAdaptor.FixedKeyOracle)
    (key : CoordinateMacKey) :
    digitPublicOffset windows key =
      DigitAdaptor.fromBits (fun index =>
        (windows (BitAdaptor.fixedKeyWindowIndex index.val)).hashToField
          (key.get index).falseLabel) := by
  simp [digitPublicOffset, DigitAdaptor.bitsK, DigitAdaptor.garble,
    BitAdaptor.garble]

/-- This value is the last Y-adaptor offset in curve garbling. -/
def curveY6Offset (r2 : BaseField) (oracles : CurveMembership.Oracles)
    (inputKey : InputMacKey) : BaseField :=
  let y4 := DigitAdaptor.garble oracles.y4 (-r2) inputKey.y
  let r4 := DigitAdaptor.bitsK y4.2
  DigitAdaptor.bitsK (DigitAdaptor.garble oracles.y6 (-r4) inputKey.y).2

/-- This value is the last X-adaptor offset in curve garbling. -/
def curveX7Offset (r1 : BaseField) (oracles : CurveMembership.Oracles)
    (inputKey : InputMacKey) : BaseField :=
  let x3 := DigitAdaptor.garble oracles.x3 (-r1) inputKey.x
  let r3 := DigitAdaptor.bitsK x3.2
  let x5 := DigitAdaptor.garble oracles.x5 (-r3) inputKey.x
  let r5 := DigitAdaptor.bitsK x5.2
  DigitAdaptor.bitsK (DigitAdaptor.garble oracles.x7 (-r5) inputKey.x).2

theorem curveY6Offset_eq_public (r2 : BaseField)
    (oracles : CurveMembership.Oracles) (inputKey : InputMacKey) :
    curveY6Offset r2 oracles inputKey =
      digitPublicOffset oracles.y6 inputKey.y := by
  exact digitBitsK_independentOfSlope _ _ _ _

theorem curveX7Offset_eq_public (r1 : BaseField)
    (oracles : CurveMembership.Oracles) (inputKey : InputMacKey) :
    curveX7Offset r1 oracles inputKey =
      digitPublicOffset oracles.x7 inputKey.x := by
  exact digitBitsK_independentOfSlope _ _ _ _

/-- These values are the three independent curve coefficient masks. -/
structure CurveCoefficientCoin where
  bridgeKey : BaseField
  r1 : BaseField
  r2 : BaseField
deriving Fintype, Inhabited

/-- These values are the three public curve coefficients. -/
structure CurveCoefficients where
  c0 : BaseField
  c1 : BaseField
  c2 : BaseField
deriving Fintype, Inhabited

/-- This is the affine map from curve masks to public coefficients. -/
def curveCoefficientTransport (mask r6 r7 : BaseField) :
    CurveCoefficientCoin → CurveCoefficients :=
  fun coin => {
    c0 := 3 * mask + coin.bridgeKey - r6 - r7
    c1 := mask + coin.r1
    c2 := -mask + coin.r2
  }

/-- This map recovers all curve masks from the public coefficients. -/
def curveCoefficientTransportInverse (mask r6 r7 : BaseField) :
    CurveCoefficients → CurveCoefficientCoin :=
  fun coefficients => {
    bridgeKey := coefficients.c0 - 3 * mask + r6 + r7
    r1 := coefficients.c1 - mask
    r2 := coefficients.c2 + mask
  }

theorem curveCoefficientTransport_leftInverse (mask r6 r7 : BaseField) :
    Function.LeftInverse
      (curveCoefficientTransportInverse mask r6 r7)
      (curveCoefficientTransport mask r6 r7) := by
  intro coin
  cases coin
  simp only [curveCoefficientTransport, curveCoefficientTransportInverse]
  congr <;> ring

theorem curveCoefficientTransport_rightInverse (mask r6 r7 : BaseField) :
    Function.RightInverse
      (curveCoefficientTransportInverse mask r6 r7)
      (curveCoefficientTransport mask r6 r7) := by
  intro coefficients
  cases coefficients
  simp only [curveCoefficientTransport, curveCoefficientTransportInverse]
  congr <;> ring

/-- The curve coefficient transform is a finite equivalence. -/
def curveCoefficientEquiv (mask r6 r7 : BaseField) :
    CurveCoefficientCoin ≃ CurveCoefficients := {
  toFun := curveCoefficientTransport mask r6 r7
  invFun := curveCoefficientTransportInverse mask r6 r7
  left_inv := curveCoefficientTransport_leftInverse mask r6 r7
  right_inv := curveCoefficientTransport_rightInverse mask r6 r7
}

/-- Public curve coefficients are uniform for each fixed hidden context. -/
theorem map_uniform_curveCoefficientTransport (mask r6 r7 : BaseField) :
    (PMF.uniformOfFintype CurveCoefficientCoin).map
        (curveCoefficientTransport mask r6 r7) =
      PMF.uniformOfFintype CurveCoefficients :=
  map_uniformOfFintype_equivBetween (curveCoefficientEquiv mask r6 r7)

/-- This projection reads the three public curve coefficients. -/
def CurveCoefficients.ofTable (table : CurveMembership.Table) :
    CurveCoefficients := {
  c0 := table.c0
  c1 := table.c1
  c2 := table.c2
}

set_option maxRecDepth 10000 in
/-- Real curve garbling uses the affine coefficient transport. -/
theorem curveGarble_coefficients
    (bridgeKey mask r1 r2 : BaseField)
    (oracles : CurveMembership.Oracles) (inputKey : InputMacKey) :
    CurveCoefficients.ofTable
        (CurveMembership.garble bridgeKey mask r1 r2 oracles inputKey) =
      curveCoefficientTransport mask
        (digitPublicOffset oracles.y6 inputKey.y)
        (digitPublicOffset oracles.x7 inputKey.x)
        { bridgeKey, r1, r2 } := by
  change CurveCoefficients.mk
    (3 * mask + bridgeKey - curveY6Offset r2 oracles inputKey -
      curveX7Offset r1 oracles inputKey)
    (mask + r1) (-mask + r2) = _
  rw [curveY6Offset_eq_public, curveX7Offset_eq_public]
  rfl

/-- This is the public zero-pad form for one RCB coordinate. -/
def biquadraticZeroPad (oracles : Biquadratic.Oracles)
    (inputKey : InputMacKey) : BaseField :=
  digitPublicOffset oracles.y10 inputKey.y +
    digitPublicOffset oracles.x9 inputKey.x

/-- These values are the five independent masks for an RCB X table. -/
structure XCoefficientCoin where
  zeroPad : BaseField
  r1 : BaseField
  r2 : BaseField
  r3 : BaseField
  r5 : BaseField
deriving Fintype, Inhabited

/-- These values are the five public coefficients of an RCB X table. -/
structure XCoefficients where
  c0 : BaseField
  c1 : BaseField
  c2 : BaseField
  c3 : BaseField
  c5 : BaseField
deriving Fintype, Inhabited

/-- This is the affine map from X-table masks to public coefficients. -/
def xCoefficientTransport (c0 c1 c2 c3 c5 : BaseField) :
    XCoefficientCoin → XCoefficients :=
  fun coin => {
    c0 := c0 - coin.zeroPad
    c1 := c1 + coin.r1
    c2 := c2 + coin.r2
    c3 := c3 + coin.r3
    c5 := c5 + coin.r5
  }

/-- This map recovers all X-table masks from the public coefficients. -/
def xCoefficientTransportInverse (c0 c1 c2 c3 c5 : BaseField) :
    XCoefficients → XCoefficientCoin :=
  fun coefficients => {
    zeroPad := c0 - coefficients.c0
    r1 := coefficients.c1 - c1
    r2 := coefficients.c2 - c2
    r3 := coefficients.c3 - c3
    r5 := coefficients.c5 - c5
  }

theorem xCoefficientTransport_leftInverse (c0 c1 c2 c3 c5 : BaseField) :
    Function.LeftInverse
      (xCoefficientTransportInverse c0 c1 c2 c3 c5)
      (xCoefficientTransport c0 c1 c2 c3 c5) := by
  intro coin
  cases coin
  simp only [xCoefficientTransport, xCoefficientTransportInverse]
  congr <;> ring

theorem xCoefficientTransport_rightInverse (c0 c1 c2 c3 c5 : BaseField) :
    Function.RightInverse
      (xCoefficientTransportInverse c0 c1 c2 c3 c5)
      (xCoefficientTransport c0 c1 c2 c3 c5) := by
  intro coefficients
  cases coefficients
  simp only [xCoefficientTransport, xCoefficientTransportInverse]
  congr <;> ring

/-- The X-table coefficient transform is a finite equivalence. -/
def xCoefficientEquiv (c0 c1 c2 c3 c5 : BaseField) :
    XCoefficientCoin ≃ XCoefficients := {
  toFun := xCoefficientTransport c0 c1 c2 c3 c5
  invFun := xCoefficientTransportInverse c0 c1 c2 c3 c5
  left_inv := xCoefficientTransport_leftInverse c0 c1 c2 c3 c5
  right_inv := xCoefficientTransport_rightInverse c0 c1 c2 c3 c5
}

/-- Public X-table coefficients are uniform for each fixed private row. -/
theorem map_uniform_xCoefficientTransport (c0 c1 c2 c3 c5 : BaseField) :
    (PMF.uniformOfFintype XCoefficientCoin).map
        (xCoefficientTransport c0 c1 c2 c3 c5) =
      PMF.uniformOfFintype XCoefficients :=
  map_uniformOfFintype_equivBetween
    (xCoefficientEquiv c0 c1 c2 c3 c5)

/-- This projection reads the five public X coefficients. -/
def XCoefficients.ofTable (table : Biquadratic.Table) : XCoefficients := {
  c0 := table.c0.getD 0
  c1 := table.c1.getD 0
  c2 := table.c2.getD 0
  c3 := table.c3.getD 0
  c5 := table.c5.getD 0
}

/-- Real X garbling uses the public zero-pad affine transport. -/
theorem biquadraticGarbleX_coefficients
    (c0 c1 c2 c3 c5 : BaseField) (randomness : Biquadratic.XRandomness)
    (oracles : Biquadratic.Oracles) (inputKey : InputMacKey) :
    XCoefficients.ofTable
        (Biquadratic.garbleX c0 c1 c2 c3 c5 randomness oracles inputKey) =
      xCoefficientTransport c0 c1 c2 c3 c5 {
        zeroPad := biquadraticZeroPad oracles inputKey
        r1 := randomness.r1
        r2 := randomness.r2
        r3 := randomness.r3
        r5 := randomness.r5
      } := by
  let y6 := DigitAdaptor.garble oracles.y6 (-randomness.r3) inputKey.y
  let r6 := DigitAdaptor.bitsK y6.2
  let y8 := DigitAdaptor.garble oracles.y8 (-randomness.r5) inputKey.y
  let r8 := DigitAdaptor.bitsK y8.2
  let y10 := DigitAdaptor.garble oracles.y10 (-(randomness.r2 + r8)) inputKey.y
  let r10 := DigitAdaptor.bitsK y10.2
  let x9 := DigitAdaptor.garble oracles.x9 (-(randomness.r1 + r6)) inputKey.x
  let r9 := DigitAdaptor.bitsK x9.2
  have r10Public : r10 = digitPublicOffset oracles.y10 inputKey.y :=
    digitBitsK_independentOfSlope _ _ _ _
  have r9Public : r9 = digitPublicOffset oracles.x9 inputKey.x :=
    digitBitsK_independentOfSlope _ _ _ _
  change XCoefficients.mk (c0 - r10 - r9) (c1 + randomness.r1)
    (c2 + randomness.r2) (c3 + randomness.r3) (c5 + randomness.r5) = _
  rw [r10Public, r9Public]
  simp only [xCoefficientTransport, biquadraticZeroPad]
  rw [sub_sub]

/-- These values are the four independent masks for an RCB Y table. -/
structure YCoefficientCoin where
  zeroPad : BaseField
  r1 : BaseField
  r4 : BaseField
  r5 : BaseField
deriving Fintype, Inhabited

/-- These values are the four public coefficients of an RCB Y table. -/
structure YCoefficients where
  c0 : BaseField
  c1 : BaseField
  c4 : BaseField
  c5 : BaseField
deriving Fintype, Inhabited

/-- This is the affine map from Y-table masks to public coefficients. -/
def yCoefficientTransport (c0 c1 c4 c5 : BaseField) :
    YCoefficientCoin → YCoefficients :=
  fun coin => {
    c0 := c0 - coin.zeroPad
    c1 := c1 + coin.r1
    c4 := c4 + coin.r4
    c5 := c5 + coin.r5
  }

/-- This map recovers all Y-table masks from the public coefficients. -/
def yCoefficientTransportInverse (c0 c1 c4 c5 : BaseField) :
    YCoefficients → YCoefficientCoin :=
  fun coefficients => {
    zeroPad := c0 - coefficients.c0
    r1 := coefficients.c1 - c1
    r4 := coefficients.c4 - c4
    r5 := coefficients.c5 - c5
  }

theorem yCoefficientTransport_leftInverse (c0 c1 c4 c5 : BaseField) :
    Function.LeftInverse
      (yCoefficientTransportInverse c0 c1 c4 c5)
      (yCoefficientTransport c0 c1 c4 c5) := by
  intro coin
  cases coin
  simp only [yCoefficientTransport, yCoefficientTransportInverse]
  congr <;> ring

theorem yCoefficientTransport_rightInverse (c0 c1 c4 c5 : BaseField) :
    Function.RightInverse
      (yCoefficientTransportInverse c0 c1 c4 c5)
      (yCoefficientTransport c0 c1 c4 c5) := by
  intro coefficients
  cases coefficients
  simp only [yCoefficientTransport, yCoefficientTransportInverse]
  congr <;> ring

/-- The Y-table coefficient transform is a finite equivalence. -/
def yCoefficientEquiv (c0 c1 c4 c5 : BaseField) :
    YCoefficientCoin ≃ YCoefficients := {
  toFun := yCoefficientTransport c0 c1 c4 c5
  invFun := yCoefficientTransportInverse c0 c1 c4 c5
  left_inv := yCoefficientTransport_leftInverse c0 c1 c4 c5
  right_inv := yCoefficientTransport_rightInverse c0 c1 c4 c5
}

/-- Public Y-table coefficients are uniform for each fixed private row. -/
theorem map_uniform_yCoefficientTransport (c0 c1 c4 c5 : BaseField) :
    (PMF.uniformOfFintype YCoefficientCoin).map
        (yCoefficientTransport c0 c1 c4 c5) =
      PMF.uniformOfFintype YCoefficients :=
  map_uniformOfFintype_equivBetween (yCoefficientEquiv c0 c1 c4 c5)

/-- This projection reads the four public Y coefficients. -/
def YCoefficients.ofTable (table : Biquadratic.Table) : YCoefficients := {
  c0 := table.c0.getD 0
  c1 := table.c1.getD 0
  c4 := table.c4.getD 0
  c5 := table.c5.getD 0
}

/-- Real Y garbling uses the public zero-pad affine transport. -/
theorem biquadraticGarbleY_coefficients
    (c0 c1 c4 c5 : BaseField) (randomness : Biquadratic.YRandomness)
    (oracles : Biquadratic.Oracles) (inputKey : InputMacKey) :
    YCoefficients.ofTable
        (Biquadratic.garbleY c0 c1 c4 c5 randomness oracles inputKey) =
      yCoefficientTransport c0 c1 c4 c5 {
        zeroPad := biquadraticZeroPad oracles inputKey
        r1 := randomness.r1
        r4 := randomness.r4
        r5 := randomness.r5
      } := by
  let y8 := DigitAdaptor.garble oracles.y8 (-randomness.r5) inputKey.y
  let r8 := DigitAdaptor.bitsK y8.2
  let y10 := DigitAdaptor.garble oracles.y10 (-r8) inputKey.y
  let r10 := DigitAdaptor.bitsK y10.2
  let x7 := DigitAdaptor.garble oracles.x7 (-randomness.r4) inputKey.x
  let r7 := DigitAdaptor.bitsK x7.2
  let x9 := DigitAdaptor.garble oracles.x9 (-(randomness.r1 + r7)) inputKey.x
  let r9 := DigitAdaptor.bitsK x9.2
  have r10Public : r10 = digitPublicOffset oracles.y10 inputKey.y :=
    digitBitsK_independentOfSlope _ _ _ _
  have r9Public : r9 = digitPublicOffset oracles.x9 inputKey.x :=
    digitBitsK_independentOfSlope _ _ _ _
  change YCoefficients.mk (c0 - r10 - r9) (c1 + randomness.r1)
    (c4 + randomness.r4) (c5 + randomness.r5) = _
  rw [r10Public, r9Public]
  simp only [yCoefficientTransport, biquadraticZeroPad]
  rw [sub_sub]

/-- These values are the five independent masks for an RCB Z table. -/
structure ZCoefficientCoin where
  zeroPad : BaseField
  r2 : BaseField
  r3 : BaseField
  r4 : BaseField
  r5 : BaseField
deriving Fintype, Inhabited

/-- These values are the five public coefficients of an RCB Z table. -/
structure ZCoefficients where
  c0 : BaseField
  c2 : BaseField
  c3 : BaseField
  c4 : BaseField
  c5 : BaseField
deriving Fintype, Inhabited

/-- This is the affine map from Z-table masks to public coefficients. -/
def zCoefficientTransport (c0 c2 c3 c4 c5 : BaseField) :
    ZCoefficientCoin → ZCoefficients :=
  fun coin => {
    c0 := c0 - coin.zeroPad
    c2 := c2 + coin.r2
    c3 := c3 + coin.r3
    c4 := c4 + coin.r4
    c5 := c5 + coin.r5
  }

/-- This map recovers all Z-table masks from the public coefficients. -/
def zCoefficientTransportInverse (c0 c2 c3 c4 c5 : BaseField) :
    ZCoefficients → ZCoefficientCoin :=
  fun coefficients => {
    zeroPad := c0 - coefficients.c0
    r2 := coefficients.c2 - c2
    r3 := coefficients.c3 - c3
    r4 := coefficients.c4 - c4
    r5 := coefficients.c5 - c5
  }

theorem zCoefficientTransport_leftInverse (c0 c2 c3 c4 c5 : BaseField) :
    Function.LeftInverse
      (zCoefficientTransportInverse c0 c2 c3 c4 c5)
      (zCoefficientTransport c0 c2 c3 c4 c5) := by
  intro coin
  cases coin
  simp only [zCoefficientTransport, zCoefficientTransportInverse]
  congr <;> ring

theorem zCoefficientTransport_rightInverse (c0 c2 c3 c4 c5 : BaseField) :
    Function.RightInverse
      (zCoefficientTransportInverse c0 c2 c3 c4 c5)
      (zCoefficientTransport c0 c2 c3 c4 c5) := by
  intro coefficients
  cases coefficients
  simp only [zCoefficientTransport, zCoefficientTransportInverse]
  congr <;> ring

/-- The Z-table coefficient transform is a finite equivalence. -/
def zCoefficientEquiv (c0 c2 c3 c4 c5 : BaseField) :
    ZCoefficientCoin ≃ ZCoefficients := {
  toFun := zCoefficientTransport c0 c2 c3 c4 c5
  invFun := zCoefficientTransportInverse c0 c2 c3 c4 c5
  left_inv := zCoefficientTransport_leftInverse c0 c2 c3 c4 c5
  right_inv := zCoefficientTransport_rightInverse c0 c2 c3 c4 c5
}

/-- Public Z-table coefficients are uniform for each fixed private row. -/
theorem map_uniform_zCoefficientTransport (c0 c2 c3 c4 c5 : BaseField) :
    (PMF.uniformOfFintype ZCoefficientCoin).map
        (zCoefficientTransport c0 c2 c3 c4 c5) =
      PMF.uniformOfFintype ZCoefficients :=
  map_uniformOfFintype_equivBetween (zCoefficientEquiv c0 c2 c3 c4 c5)

/-- This projection reads the five public Z coefficients. -/
def ZCoefficients.ofTable (table : Biquadratic.Table) : ZCoefficients := {
  c0 := table.c0.getD 0
  c2 := table.c2.getD 0
  c3 := table.c3.getD 0
  c4 := table.c4.getD 0
  c5 := table.c5.getD 0
}

/-- Real Z garbling uses the public zero-pad affine transport. -/
theorem biquadraticGarbleZ_coefficients
    (c0 c2 c3 c4 c5 : BaseField) (randomness : Biquadratic.ZRandomness)
    (oracles : Biquadratic.Oracles) (inputKey : InputMacKey) :
    ZCoefficients.ofTable
        (Biquadratic.garbleZ c0 c2 c3 c4 c5 randomness oracles inputKey) =
      zCoefficientTransport c0 c2 c3 c4 c5 {
        zeroPad := biquadraticZeroPad oracles inputKey
        r2 := randomness.r2
        r3 := randomness.r3
        r4 := randomness.r4
        r5 := randomness.r5
      } := by
  let y6 := DigitAdaptor.garble oracles.y6 (-randomness.r3) inputKey.y
  let r6 := DigitAdaptor.bitsK y6.2
  let y8 := DigitAdaptor.garble oracles.y8 (-randomness.r5) inputKey.y
  let r8 := DigitAdaptor.bitsK y8.2
  let y10 := DigitAdaptor.garble oracles.y10 (-(randomness.r2 + r8)) inputKey.y
  let r10 := DigitAdaptor.bitsK y10.2
  let x7 := DigitAdaptor.garble oracles.x7 (-randomness.r4) inputKey.x
  let r7 := DigitAdaptor.bitsK x7.2
  let x9 := DigitAdaptor.garble oracles.x9 (-(r6 + r7)) inputKey.x
  let r9 := DigitAdaptor.bitsK x9.2
  have r10Public : r10 = digitPublicOffset oracles.y10 inputKey.y :=
    digitBitsK_independentOfSlope _ _ _ _
  have r9Public : r9 = digitPublicOffset oracles.x9 inputKey.x :=
    digitBitsK_independentOfSlope _ _ _ _
  change ZCoefficients.mk (c0 - r10 - r9) (c2 + randomness.r2)
    (c3 + randomness.r3) (c4 + randomness.r4) (c5 + randomness.r5) = _
  rw [r10Public, r9Public]
  simp only [zCoefficientTransport, biquadraticZeroPad]
  rw [sub_sub]

/-- Good hash lifts give an exact independent uniform field value. -/
theorem map_uniform_goodHashLiftEquiv :
    (PMF.uniformOfFintype GoodHashLift).map goodHashLiftEquiv =
      PMF.uniformOfFintype (BaseField × HashLiftQuotient) :=
  map_uniformOfFintype_equivBetween goodHashLiftEquiv

/-- Uniform residues and quotients give uniform complete-fiber hash values. -/
theorem map_uniform_goodHashLiftEquiv_symm :
    (PMF.uniformOfFintype (BaseField × HashLiftQuotient)).map
        goodHashLiftEquiv.symm = PMF.uniformOfFintype GoodHashLift :=
  map_uniformOfFintype_equivBetween goodHashLiftEquiv.symm

/-- The rejected 384-bit suffix is smaller than one field fiber. -/
theorem hashLiftRemainder_lt_baseFieldModulus :
    2 ^ 384 % baseFieldModulus < baseFieldModulus := by
  exact Nat.mod_lt _ (by decide)

set_option exponentiation.threshold 400 in
/-- Complete fibers and the rejected suffix partition all 384-bit values. -/
theorem hashLiftFiberCount :
    hashLiftQuotientCount * baseFieldModulus +
        2 ^ 384 % baseFieldModulus = 2 ^ 384 := by
  exact Nat.div_add_mod (2 ^ 384) baseFieldModulus

/-- This type contains the rejected 384-bit suffix. -/
abbrev BadHashLift := Fin (2 ^ 384 % baseFieldModulus)

/-- This type contains each 384-bit integer. -/
abbrev FullHashLift := Fin (2 ^ 384)

set_option exponentiation.threshold 400 in
instance fullHashLiftNonempty : Nonempty FullHashLift :=
  ⟨⟨0, by decide⟩⟩

/-- A full hash lift is exactly three fixed-key blocks. -/
def fullHashLiftBlockEquiv : FullHashLift ≃ (Fin 3 → Block) :=
  BitVec.equivFin.symm.toEquiv.trans hashLiftBlockEquiv

/-- Uniform full hash lifts give three uniform blocks. -/
theorem map_uniform_fullHashLiftBlockEquiv :
    (PMF.uniformOfFintype FullHashLift).map fullHashLiftBlockEquiv =
      PMF.uniformOfFintype (Fin 3 → Block) :=
  map_uniformOfFintype_equivBetween fullHashLiftBlockEquiv

/-- This value is the complete Davies--Meyer hash lift for one fixed gate. -/
def fixedDaviesMeyerHashLift (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) : FullHashLift :=
  BitVec.equivFin (BitAdaptor.hashBytes
    (Pipeline.fixedKeyPermutations oracle location window) label)

theorem fixedDaviesMeyerHashLift_eq (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : Block)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) :
    fixedDaviesMeyerHashLift location window label oracle =
      fullHashLiftBlockEquiv.symm
        (fun slot => oracle.permutation
          (fixedKeyIndex location window (.hash slot)) label ^^^ label) := by
  rfl

/-- One fixed gate has an exact uniform 384-bit Davies--Meyer hash lift. -/
theorem map_uniform_fixedDaviesMeyerHashLift
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block)).map
        (fixedDaviesMeyerHashLift location window label) =
      PMF.uniformOfFintype FullHashLift := by
  rw [show fixedDaviesMeyerHashLift location window label =
      fullHashLiftBlockEquiv.symm ∘
        (fun (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) slot =>
          oracle.permutation (fixedKeyIndex location window (.hash slot)) label ^^^ label) by
        funext oracle
        exact fixedDaviesMeyerHashLift_eq location window label oracle]
  rw [← PMF.map_comp]
  rw [map_uniform_fixedDaviesMeyerBlocks]
  exact map_uniformOfFintype_equivBetween fullHashLiftBlockEquiv.symm

/-- This equivalence separates complete field fibers from the rejected suffix. -/
def hashLiftSplitEquiv : FullHashLift ≃ GoodHashLift ⊕ BadHashLift :=
  (finCongr hashLiftFiberCount.symm).trans finSumFinEquiv.symm

/-- Uniform 384-bit integers split exactly into the good and bad parts. -/
theorem map_uniform_hashLiftSplitEquiv :
    (PMF.uniformOfFintype FullHashLift).map hashLiftSplitEquiv =
      PMF.uniformOfFintype (GoodHashLift ⊕ BadHashLift) :=
  map_uniformOfFintype_equivBetween hashLiftSplitEquiv

/-- One fixed gate has the exact good-or-bad hash-lift distribution. -/
theorem map_uniform_fixedDaviesMeyerHashSplit
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block)).map
        (hashLiftSplitEquiv ∘ fixedDaviesMeyerHashLift location window label) =
      PMF.uniformOfFintype (GoodHashLift ⊕ BadHashLift) := by
  rw [← PMF.map_comp]
  rw [map_uniform_fixedDaviesMeyerHashLift]
  exact map_uniform_hashLiftSplitEquiv

set_option exponentiation.threshold 400 in
/-- A good split exposes the real hash-to-field residue. -/
theorem fixedHashToField_eq_goodResidue
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (good : GoodHashLift)
    (isGood : hashLiftSplitEquiv
      (fixedDaviesMeyerHashLift location window label oracle) = Sum.inl good) :
    (Pipeline.fixedKeyWindow oracle location window).hashToField label =
      (goodHashLiftEquiv good).1 := by
  rw [goodHashLiftEquiv_fst]
  have valueEqual :
      (fixedDaviesMeyerHashLift location window label oracle).val = good.val := by
    have fullEqual :
        fixedDaviesMeyerHashLift location window label oracle =
          hashLiftSplitEquiv.symm (Sum.inl good) := by
      calc
        fixedDaviesMeyerHashLift location window label oracle =
            hashLiftSplitEquiv.symm (hashLiftSplitEquiv
              (fixedDaviesMeyerHashLift location window label oracle)) :=
          (hashLiftSplitEquiv.symm_apply_apply _).symm
        _ = hashLiftSplitEquiv.symm (Sum.inl good) := congrArg _ isGood
    calc
      (fixedDaviesMeyerHashLift location window label oracle).val =
          (hashLiftSplitEquiv.symm (Sum.inl good)).val :=
        congrArg Fin.val fullEqual
      _ = good.val := by rfl
  change ((BitAdaptor.hashBytes
    (Pipeline.fixedKeyPermutations oracle location window) label).toNat : BaseField) =
      (good.val : BaseField)
  simpa [fixedDaviesMeyerHashLift] using
    congrArg (fun value : Nat => (value : BaseField)) valueEqual

/-- A function of product values equals a product of functions. -/
def functionProdEquiv {Index First Second : Type} :
    (Index → First × Second) ≃ ((Index → First) × (Index → Second)) where
  toFun function := (fun index => (function index).1, fun index => (function index).2)
  invFun pair index := (pair.1 index, pair.2 index)
  left_inv function := by
    funext index
    exact Prod.ext rfl rfl
  right_inv pair := by
    apply Prod.ext <;> funext index <;> rfl

/-- This equivalence exposes all accepted residues and quotients. -/
def goodHashVectorEquiv :
    (Fin coordinateBitCount → GoodHashLift) ≃
      ((Fin coordinateBitCount → BaseField) ×
        (Fin coordinateBitCount → HashLiftQuotient)) :=
  (Equiv.piCongrRight fun _ : Fin coordinateBitCount => goodHashLiftEquiv).trans
    functionProdEquiv

theorem goodHashVectorEquiv_fst
    (values : Fin coordinateBitCount → GoodHashLift) :
    (goodHashVectorEquiv values).1 =
      fun index => (goodHashLiftEquiv (values index)).1 := by
  rfl

/-- Accepted hash lifts give a uniform vector of field residues. -/
theorem map_uniform_goodHashResidueVector :
    (PMF.uniformOfFintype (Fin coordinateBitCount → GoodHashLift)).map
        (fun values index => (goodHashLiftEquiv (values index)).1) =
      PMF.uniformOfFintype (Fin coordinateBitCount → BaseField) := by
  rw [show (fun values : Fin coordinateBitCount → GoodHashLift =>
      fun index => (goodHashLiftEquiv (values index)).1) =
      Prod.fst ∘ goodHashVectorEquiv by
    funext values
    exact (goodHashVectorEquiv_fst values).symm]
  rw [← PMF.map_comp]
  rw [map_uniformOfFintype_equivBetween]
  exact map_uniform_prod_fst

set_option maxRecDepth 100000 in
/-- Accepted hash lifts give an exact uniform digit offset. -/
theorem map_uniform_goodHashDigitOffset :
    (PMF.uniformOfFintype (Fin coordinateBitCount → GoodHashLift)).map
        (fun values => DigitAdaptor.fromBits fun index =>
          (goodHashLiftEquiv (values index)).1) =
      PMF.uniformOfFintype BaseField := by
  rw [show (fun values : Fin coordinateBitCount → GoodHashLift =>
      DigitAdaptor.fromBits fun index => (goodHashLiftEquiv (values index)).1) =
      DigitAdaptor.fromBits ∘
        (fun values index => (goodHashLiftEquiv (values index)).1) from rfl]
  rw [← PMF.map_comp]
  rw [map_uniform_goodHashResidueVector]
  exact map_uniform_digitOffset

set_option maxRecDepth 100000 in
/-- Adding a fixed value preserves one accepted-hash digit offset. -/
theorem map_uniform_goodHashDigitOffset_add (offset : BaseField) :
    (PMF.uniformOfFintype (Fin coordinateBitCount → GoodHashLift)).map
        (fun values =>
          DigitAdaptor.fromBits (fun index =>
            (goodHashLiftEquiv (values index)).1) + offset) =
      PMF.uniformOfFintype BaseField := by
  rw [show (fun values : Fin coordinateBitCount → GoodHashLift =>
      DigitAdaptor.fromBits (fun index =>
        (goodHashLiftEquiv (values index)).1) + offset) =
      addFieldEquiv offset ∘
        (fun values => DigitAdaptor.fromBits fun index =>
          (goodHashLiftEquiv (values index)).1) from rfl]
  rw [← PMF.map_comp]
  rw [map_uniform_goodHashDigitOffset]
  exact map_uniformOfFintype_equivBetween (addFieldEquiv offset)

set_option maxRecDepth 100000 in
/-- Two accepted-hash digit offsets give one uniform zero pad. -/
theorem map_uniform_twoGoodHashDigitOffsetSum :
    (PMF.uniformOfFintype
      ((Fin coordinateBitCount → GoodHashLift) ×
        (Fin coordinateBitCount → GoodHashLift))).map
        (fun sample =>
          DigitAdaptor.fromBits (fun index =>
            (goodHashLiftEquiv (sample.1 index)).1) +
          DigitAdaptor.fromBits (fun index =>
            (goodHashLiftEquiv (sample.2 index)).1)) =
      PMF.uniformOfFintype BaseField := by
  exact map_uniform_prod_of_uniform_fiber
    (First := Fin coordinateBitCount → GoodHashLift)
    (Second := Fin coordinateBitCount → GoodHashLift)
    (Output := BaseField)
    (fun first second =>
      DigitAdaptor.fromBits (fun index =>
        (goodHashLiftEquiv (first index)).1) +
      DigitAdaptor.fromBits (fun index =>
        (goodHashLiftEquiv (second index)).1))
    (fun second => map_uniform_goodHashDigitOffset_add
      (DigitAdaptor.fromBits fun index =>
        (goodHashLiftEquiv (second index)).1))

set_option maxRecDepth 100000 in
/-- Good gate hashes expose the real public digit offset. -/
theorem digitPublicOffset_eq_goodHashOffset
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (location : Pipeline.FixedKeyLocation) (key : CoordinateMacKey)
    (good : Fin coordinateBitCount → GoodHashLift)
    (isGood : ∀ index, hashLiftSplitEquiv
      (fixedDaviesMeyerHashLift location
        (BitAdaptor.fixedKeyWindowIndex index.val)
        (key.get index).falseLabel oracle) = Sum.inl (good index)) :
    digitPublicOffset (fun window =>
      Pipeline.fixedKeyWindow oracle location window) key =
      DigitAdaptor.fromBits (fun index =>
        (goodHashLiftEquiv (good index)).1) := by
  rw [digitPublicOffset_eq_fromBits]
  apply congrArg DigitAdaptor.fromBits
  funext index
  exact fixedHashToField_eq_goodResidue location
    (BitAdaptor.fixedKeyWindowIndex index.val)
    (key.get index).falseLabel oracle (good index) (isGood index)

set_option maxRecDepth 100000 in
/-- Good Y10 and X9 hashes expose the real RCB zero pad. -/
theorem biquadraticZeroPad_eq_goodHashSum
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (output : Fin FieldMacToECMac.outputMacCount)
    (coordinate : Pipeline.PointCoordinate) (inputKey : InputMacKey)
    (yGood xGood : Fin coordinateBitCount → GoodHashLift)
    (yIsGood : ∀ index, hashLiftSplitEquiv
      (fixedDaviesMeyerHashLift (.point output coordinate .y10)
        (BitAdaptor.fixedKeyWindowIndex index.val)
        (inputKey.y.get index).falseLabel oracle) = Sum.inl (yGood index))
    (xIsGood : ∀ index, hashLiftSplitEquiv
      (fixedDaviesMeyerHashLift (.point output coordinate .x9)
        (BitAdaptor.fixedKeyWindowIndex index.val)
        (inputKey.x.get index).falseLabel oracle) = Sum.inl (xGood index)) :
    biquadraticZeroPad (Pipeline.biquadraticOracles oracle output coordinate) inputKey =
      DigitAdaptor.fromBits (fun index => (goodHashLiftEquiv (yGood index)).1) +
        DigitAdaptor.fromBits (fun index => (goodHashLiftEquiv (xGood index)).1) := by
  change digitPublicOffset (fun window => Pipeline.fixedKeyWindow oracle
      (.point output coordinate .y10) window) inputKey.y +
    digitPublicOffset (fun window => Pipeline.fixedKeyWindow oracle
      (.point output coordinate .x9) window) inputKey.x = _
  rw [digitPublicOffset_eq_goodHashOffset oracle
    (.point output coordinate .y10) inputKey.y yGood yIsGood]
  rw [digitPublicOffset_eq_goodHashOffset oracle
    (.point output coordinate .x9) inputKey.x xGood xIsGood]

/-- A gate hash stays uniform in the fixed-oracle product tape. -/
theorem map_uniform_fixedOracleProduct_fixedDaviesMeyerHashSplit
    (restWitness : GarblingRandomnessRest)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : GarblingRandomnessRest → Block) :
    letI : Nonempty GarblingRandomnessRest := ⟨restWitness⟩
    (PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block × GarblingRandomnessRest)).map
        (fun sample => hashLiftSplitEquiv
          (fixedDaviesMeyerHashLift location window (label sample.2) sample.1)) =
      PMF.uniformOfFintype (GoodHashLift ⊕ BadHashLift) := by
  letI : Nonempty GarblingRandomnessRest := ⟨restWitness⟩
  exact map_uniform_prod_of_uniform_fiber
    (First := PermutationOracle Pipeline.FixedKeyIndex Block)
    (Second := GarblingRandomnessRest)
    (Output := GoodHashLift ⊕ BadHashLift)
    (fun oracle rest => hashLiftSplitEquiv
      (fixedDaviesMeyerHashLift location window (label rest) oracle))
    (fun rest => map_uniform_fixedDaviesMeyerHashSplit
      location window (label rest))

/-- A gate hash stays uniform when its label depends on non-oracle randomness. -/
theorem map_uniform_garblingRandomness_fixedDaviesMeyerHashSplit
    (witness : Garbling.Randomness) (location : Pipeline.FixedKeyLocation)
    (window : Nat) (label : GarblingRandomnessRest → Block) :
    letI : Nonempty Garbling.Randomness := ⟨witness⟩
    (PMF.uniformOfFintype Garbling.Randomness).map
        (fun randomness => hashLiftSplitEquiv
          (fixedDaviesMeyerHashLift location window
            (label (garblingRandomnessRest randomness)) randomness.fixedKeyOracle)) =
      PMF.uniformOfFintype (GoodHashLift ⊕ BadHashLift) := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  letI : Nonempty GarblingRandomnessRest := ⟨garblingRandomnessRest witness⟩
  rw [show (fun randomness : Garbling.Randomness => hashLiftSplitEquiv
      (fixedDaviesMeyerHashLift location window
        (label (garblingRandomnessRest randomness)) randomness.fixedKeyOracle)) =
      (fun sample => hashLiftSplitEquiv
        (fixedDaviesMeyerHashLift location window (label sample.2) sample.1)) ∘
        garblingRandomnessFixedOracleEquiv by rfl]
  rw [← PMF.map_comp]
  rw [map_uniformOfFintype_equivBetween]
  exact map_uniform_fixedOracleProduct_fixedDaviesMeyerHashSplit
    (garblingRandomnessRest witness) location window label

/-- A gate hash stays uniform when all gate metadata depends on the rest tape. -/
theorem map_uniform_garblingRandomness_dependentDaviesMeyerHashSplit
    (witness : Garbling.Randomness)
    (location : GarblingRandomnessRest → Pipeline.FixedKeyLocation)
    (window : GarblingRandomnessRest → Nat)
    (label : GarblingRandomnessRest → Block) :
    letI : Nonempty Garbling.Randomness := ⟨witness⟩
    (PMF.uniformOfFintype Garbling.Randomness).map
        (fun randomness =>
          let rest := garblingRandomnessRest randomness
          hashLiftSplitEquiv
            (fixedDaviesMeyerHashLift (location rest) (window rest)
              (label rest) randomness.fixedKeyOracle)) =
      PMF.uniformOfFintype (GoodHashLift ⊕ BadHashLift) := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  letI : Nonempty GarblingRandomnessRest := ⟨garblingRandomnessRest witness⟩
  rw [show (fun randomness : Garbling.Randomness =>
      let rest := garblingRandomnessRest randomness
      hashLiftSplitEquiv
        (fixedDaviesMeyerHashLift (location rest) (window rest)
          (label rest) randomness.fixedKeyOracle)) =
      (fun sample => hashLiftSplitEquiv
        (fixedDaviesMeyerHashLift (location sample.2) (window sample.2)
          (label sample.2) sample.1)) ∘ garblingRandomnessFixedOracleEquiv by rfl]
  rw [← PMF.map_comp]
  rw [map_uniformOfFintype_equivBetween]
  exact map_uniform_prod_of_uniform_fiber
    (First := PermutationOracle Pipeline.FixedKeyIndex Block)
    (Second := GarblingRandomnessRest)
    (Output := GoodHashLift ⊕ BadHashLift)
    (fun oracle rest => hashLiftSplitEquiv
      (fixedDaviesMeyerHashLift (location rest) (window rest) (label rest) oracle))
    (fun rest => map_uniform_fixedDaviesMeyerHashSplit
      (location rest) (window rest) (label rest))

/-- One gate in the complete security tape has the exact hash-lift law. -/
theorem map_randomTape_fixedDaviesMeyerHashSplit
    (witness : Garbling.Randomness) (parameter : Nat)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    (randomTape witness parameter).map
        ((hashLiftSplitEquiv ∘ fixedDaviesMeyerHashLift location window label) ∘
          Garbling.Randomness.fixedKeyOracle) =
      PMF.uniformOfFintype (GoodHashLift ⊕ BadHashLift) := by
  rw [← PMF.map_comp]
  rw [map_randomTape_fixedKeyOracle]
  exact map_uniform_fixedDaviesMeyerHashSplit location window label

/-- The security-tape gate hash stays uniform for a non-oracle-dependent label. -/
theorem map_randomTape_dependentDaviesMeyerHashSplit
    (witness : Garbling.Randomness) (parameter : Nat)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : GarblingRandomnessRest → Block) :
    (randomTape witness parameter).map
        (fun randomness => hashLiftSplitEquiv
          (fixedDaviesMeyerHashLift location window
            (label (garblingRandomnessRest randomness)) randomness.fixedKeyOracle)) =
      PMF.uniformOfFintype (GoodHashLift ⊕ BadHashLift) := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  rw [randomTape]
  exact map_uniform_garblingRandomness_fixedDaviesMeyerHashSplit
    witness location window label

/-- A complete-tape gate hash stays uniform for dependent gate metadata. -/
theorem map_randomTape_dependentGateDaviesMeyerHashSplit
    (witness : Garbling.Randomness) (parameter : Nat)
    (location : GarblingRandomnessRest → Pipeline.FixedKeyLocation)
    (window : GarblingRandomnessRest → Nat)
    (label : GarblingRandomnessRest → Block) :
    (randomTape witness parameter).map
        (fun randomness =>
          let rest := garblingRandomnessRest randomness
          hashLiftSplitEquiv
            (fixedDaviesMeyerHashLift (location rest) (window rest)
              (label rest) randomness.fixedKeyOracle)) =
      PMF.uniformOfFintype (GoodHashLift ⊕ BadHashLift) := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  rw [randomTape]
  exact map_uniform_garblingRandomness_dependentDaviesMeyerHashSplit
    witness location window label

/-- This event selects the rejected suffix after the exact split. -/
def hashLiftBadSet : Set (GoodHashLift ⊕ BadHashLift) :=
  fun sample => match sample with
    | .inl _ => False
    | .inr _ => True

/-- The rejected suffix is equivalent to the bad-event subtype. -/
def badHashLiftEquiv : BadHashLift ≃ hashLiftBadSet where
  toFun value := ⟨.inr value, trivial⟩
  invFun value := by
    rcases value with ⟨sample, bad⟩
    cases sample with
    | inl _ => exact False.elim bad
    | inr rejected => exact rejected
  left_inv _ := rfl
  right_inv value := by
    rcases value with ⟨sample, bad⟩
    cases sample with
    | inl _ => exact False.elim bad
    | inr _ => rfl

noncomputable instance hashLiftBadSetFintype : Fintype hashLiftBadSet :=
  Fintype.ofEquiv BadHashLift badHashLiftEquiv

set_option exponentiation.threshold 400 in
set_option maxRecDepth 100000 in
/-- The exact bad mass is the rejected suffix divided by the hash domain. -/
theorem uniform_hashLiftBadSet_mass :
    (PMF.uniformOfFintype (GoodHashLift ⊕ BadHashLift)).toOuterMeasure
        hashLiftBadSet =
      ((2 ^ 384 % baseFieldModulus : Nat) : ENNReal) /
        ((2 ^ 384 : Nat) : ENNReal) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have badCard : Fintype.card hashLiftBadSet =
      2 ^ 384 % baseFieldModulus := by
    simpa using (Fintype.card_congr badHashLiftEquiv).symm
  have totalCard : Fintype.card (GoodHashLift ⊕ BadHashLift) = 2 ^ 384 := by
    simpa using (Fintype.card_congr hashLiftSplitEquiv).symm
  rw [badCard, totalCard]

/-- One real fixed-gate hash has the exact rejected-suffix mass. -/
theorem fixedDaviesMeyerHashSplit_badMass
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    ((PMF.uniformOfFintype
      (PermutationOracle Pipeline.FixedKeyIndex Block)).map
        (hashLiftSplitEquiv ∘ fixedDaviesMeyerHashLift location window label)).toOuterMeasure
          hashLiftBadSet =
      ((2 ^ 384 % baseFieldModulus : Nat) : ENNReal) /
        ((2 ^ 384 : Nat) : ENNReal) := by
  rw [map_uniform_fixedDaviesMeyerHashSplit]
  exact uniform_hashLiftBadSet_mass

/-- One complete-tape gate has the exact rejected-suffix mass. -/
theorem randomTape_fixedDaviesMeyerHashSplit_badMass
    (witness : Garbling.Randomness) (parameter : Nat)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block) :
    ((randomTape witness parameter).map
        ((hashLiftSplitEquiv ∘ fixedDaviesMeyerHashLift location window label) ∘
          Garbling.Randomness.fixedKeyOracle)).toOuterMeasure hashLiftBadSet =
      ((2 ^ 384 % baseFieldModulus : Nat) : ENNReal) /
        ((2 ^ 384 : Nat) : ENNReal) := by
  rw [map_randomTape_fixedDaviesMeyerHashSplit]
  exact uniform_hashLiftBadSet_mass

/-- A dependent-label security-tape gate has the exact rejected-suffix mass. -/
theorem randomTape_dependentDaviesMeyerHashSplit_badMass
    (witness : Garbling.Randomness) (parameter : Nat)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : GarblingRandomnessRest → Block) :
    ((randomTape witness parameter).map
        (fun randomness => hashLiftSplitEquiv
          (fixedDaviesMeyerHashLift location window
            (label (garblingRandomnessRest randomness))
            randomness.fixedKeyOracle))).toOuterMeasure hashLiftBadSet =
      ((2 ^ 384 % baseFieldModulus : Nat) : ENNReal) /
        ((2 ^ 384 : Nat) : ENNReal) := by
  rw [map_randomTape_dependentDaviesMeyerHashSplit]
  exact uniform_hashLiftBadSet_mass

/-- Dependent gate metadata keeps the exact complete-tape suffix mass. -/
theorem randomTape_dependentGateDaviesMeyerHashSplit_badMass
    (witness : Garbling.Randomness) (parameter : Nat)
    (location : GarblingRandomnessRest → Pipeline.FixedKeyLocation)
    (window : GarblingRandomnessRest → Nat)
    (label : GarblingRandomnessRest → Block) :
    ((randomTape witness parameter).map
        (fun randomness =>
          let rest := garblingRandomnessRest randomness
          hashLiftSplitEquiv
            (fixedDaviesMeyerHashLift (location rest) (window rest)
              (label rest) randomness.fixedKeyOracle))).toOuterMeasure hashLiftBadSet =
      ((2 ^ 384 % baseFieldModulus : Nat) : ENNReal) /
        ((2 ^ 384 : Nat) : ENNReal) := by
  rw [map_randomTape_dependentGateDaviesMeyerHashSplit]
  exact uniform_hashLiftBadSet_mass

/-- The rejected mass is at most one field modulus over the hash domain. -/
theorem uniform_hashLiftBadSet_mass_le :
    (PMF.uniformOfFintype (GoodHashLift ⊕ BadHashLift)).toOuterMeasure
        hashLiftBadSet ≤
      (baseFieldModulus : ENNReal) / ((2 ^ 384 : Nat) : ENNReal) := by
  rw [uniform_hashLiftBadSet_mass]
  apply ENNReal.div_le_div_right
  exact_mod_cast hashLiftRemainder_lt_baseFieldModulus.le

end

end Kriterion.ArgoMAC.Security
