/-
This file proves scalar-independent distribution transport for public values.
-/

import Proof.PublicSample

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

universe uSource uTarget

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

/-- This is the number of complete base-field fibers in 384 bits. -/
def hashLiftQuotientCount : Nat :=
  2 ^ 384 / baseFieldModulus

/-- This type indexes the complete base-field fibers in 384 bits. -/
abbrev HashLiftQuotient := Fin hashLiftQuotientCount

/-- This type contains the 384-bit integers in complete field fibers. -/
abbrev GoodHashLift := Fin (baseFieldModulus * hashLiftQuotientCount)

set_option exponentiation.threshold 400 in
instance hashLiftQuotientNonempty : Nonempty HashLiftQuotient :=
  ⟨⟨0, by decide⟩⟩

set_option exponentiation.threshold 400 in
instance goodHashLiftNonempty : Nonempty GoodHashLift :=
  ⟨⟨0, by decide⟩⟩

/-- A good 384-bit value is one field value and one quotient value. -/
def goodHashLiftEquiv : GoodHashLift ≃ BaseField × HashLiftQuotient :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (ZMod.finEquiv baseFieldModulus).toEquiv (Equiv.refl _))

/-- Good hash lifts give an exact independent uniform field value. -/
theorem map_uniform_goodHashLiftEquiv :
    (PMF.uniformOfFintype GoodHashLift).map goodHashLiftEquiv =
      PMF.uniformOfFintype (BaseField × HashLiftQuotient) :=
  map_uniformOfFintype_equivBetween goodHashLiftEquiv

/-- The rejected 384-bit suffix is smaller than one field fiber. -/
theorem hashLiftRemainder_lt_baseFieldModulus :
    2 ^ 384 % baseFieldModulus < baseFieldModulus := by
  exact Nat.mod_lt _ (by decide)

set_option exponentiation.threshold 400 in
/-- Complete fibers and the rejected suffix partition all 384-bit values. -/
theorem hashLiftFiberCount :
    baseFieldModulus * hashLiftQuotientCount +
        2 ^ 384 % baseFieldModulus = 2 ^ 384 := by
  exact Nat.div_add_mod (2 ^ 384) baseFieldModulus

/-- This type contains the rejected 384-bit suffix. -/
abbrev BadHashLift := Fin (2 ^ 384 % baseFieldModulus)

/-- This type contains each 384-bit integer. -/
abbrev FullHashLift := Fin (2 ^ 384)

set_option exponentiation.threshold 400 in
instance fullHashLiftNonempty : Nonempty FullHashLift :=
  ⟨⟨0, by decide⟩⟩

/-- This equivalence separates complete field fibers from the rejected suffix. -/
def hashLiftSplitEquiv : FullHashLift ≃ GoodHashLift ⊕ BadHashLift :=
  (finCongr hashLiftFiberCount.symm).trans finSumFinEquiv.symm

/-- Uniform 384-bit integers split exactly into the good and bad parts. -/
theorem map_uniform_hashLiftSplitEquiv :
    (PMF.uniformOfFintype FullHashLift).map hashLiftSplitEquiv =
      PMF.uniformOfFintype (GoodHashLift ⊕ BadHashLift) :=
  map_uniformOfFintype_equivBetween hashLiftSplitEquiv

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
