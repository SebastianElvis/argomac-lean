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
