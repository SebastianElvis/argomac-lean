/-
This file defines the optimized BN254 coordinate polynomials.
The active paper defines the rows at `eq:c2_coeffs_X` through `eq:c2_coeffs_Z`.
-/

import BN254
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Kriterion.ArgoMAC.Coordinates

/-- `Coefficients` contains the coefficients for the six input monomials. -/
structure Coefficients where
  constant : BN254.BaseField
  x : BN254.BaseField
  y : BN254.BaseField
  xy : BN254.BaseField
  xSquared : BN254.BaseField
  ySquared : BN254.BaseField
deriving DecidableEq

/-- `evaluate` computes one coordinate from the six input monomials. -/
def evaluate (coefficients : Coefficients) (input : BN254.AffineInput) :
    BN254.BaseField :=
  coefficients.constant + coefficients.x * input.x + coefficients.y * input.y +
    coefficients.xy * (input.x * input.y) + coefficients.xSquared * input.x ^ 2 +
    coefficients.ySquared * input.y ^ 2

/-- `xCoefficients` defines `eq:c2_coeffs_X`. -/
def xCoefficients (key : BN254.AffineInput) : Coefficients :=
  { constant := 6
    x := key.x ^ 2
    y := -(2 * key.y)
    xy := 0
    xSquared := key.x
    ySquared := 0 }

/-- `yCoefficients` defines `eq:c2_coeffs_Y`. -/
def yCoefficients (key : BN254.AffineInput) : Coefficients :=
  { constant := 9 * key.y
    x := 0
    y := -(key.y ^ 2 + 9)
    xy := -(3 * key.x ^ 2)
    xSquared := 3 * key.x * key.y
    ySquared := key.y }

/-- `zCoefficients` defines `eq:c2_coeffs_Z`. -/
def zCoefficients (key : BN254.AffineInput) : Coefficients :=
  { constant := -key.x
    x := 1
    y := 0
    xy := 0
    xSquared := 0
    ySquared := 0 }

/-- The X-coordinate row has the required polynomial. -/
theorem evaluateX (key input : BN254.AffineInput) :
    evaluate (xCoefficients key) input =
      6 + key.x ^ 2 * input.x - 2 * key.y * input.y + key.x * input.x ^ 2 := by
  simp [evaluate, xCoefficients]
  ring

/-- The Y-coordinate row has the required polynomial. -/
theorem evaluateY (key input : BN254.AffineInput) :
    evaluate (yCoefficients key) input =
      9 * key.y - (key.y ^ 2 + 9) * input.y +
        3 * key.x * key.y * input.x ^ 2 + key.y * input.y ^ 2 -
        3 * key.x ^ 2 * (input.x * input.y) := by
  simp [evaluate, yCoefficients]
  ring

/-- The Z-coordinate row has the required polynomial. -/
theorem evaluateZ (key input : BN254.AffineInput) :
    evaluate (zCoefficients key) input = input.x - key.x := by
  simp [evaluate, zCoefficients]
  ring

/-- The three coordinate polynomials form a Jacobian curve point. -/
theorem evaluatedOnCurve (key input : BN254.AffineInput)
    (keyOnCurve : BN254.OnCurve key) (inputOnCurve : BN254.OnCurve input) :
    let x := evaluate (xCoefficients key) input
    let y := evaluate (yCoefficients key) input
    let z := evaluate (zCoefficients key) input
    y ^ 2 = x ^ 3 + 3 * z ^ 6 := by
  simp only [evaluateX, evaluateY, evaluateZ, BN254.OnCurve] at keyOnCurve inputOnCurve ⊢
  linear_combination
    (input.x ^ 3 * key.y ^ 2 + 9 * input.x ^ 2 * key.x ^ 4 - 6 * input.x ^ 2 * key.x * key.y ^ 2 - 6 * input.x * input.y * key.x ^ 2 * key.y - 6 * input.x * key.x ^ 2 * key.y ^ 2 + 54 * input.x * key.x ^ 2 + input.y ^ 2 * key.y ^ 2 + 6 * input.y * key.y ^ 3 - 18 * input.y * key.y + key.y ^ 4 - 33 * key.y ^ 2 + 81) * inputOnCurve +
    (input.x ^ 6 - 6 * input.x ^ 5 * key.x + 3 * input.x ^ 4 * key.x ^ 2 + 6 * input.x ^ 3 * input.y * key.y + input.x ^ 3 * key.x ^ 3 + input.x ^ 3 * key.y ^ 2 - 27 * input.x ^ 3 - 6 * input.x ^ 2 * input.y * key.x * key.y + 36 * input.x ^ 2 * key.x - 18 * input.x * key.x ^ 2 + 3 * key.x ^ 3 + 3 * key.y ^ 2 - 9) * keyOnCurve

/-- The recovered X coordinate equals the Mathlib point-addition coordinate. -/
theorem recoveredX [BN254.FieldCertificate] (key input : BN254.AffineInput)
    (keyOnCurve : BN254.OnCurve key) (inputOnCurve : BN254.OnCurve input)
    (xNe : input.x ≠ key.x) :
    evaluate (xCoefficients key) input / evaluate (zCoefficients key) input ^ 2 =
      BN254.curve.toAffine.addX input.x key.x
        (BN254.curve.toAffine.slope input.x key.x input.y key.y) := by
  rw [evaluateX, evaluateZ, WeierstrassCurve.Affine.slope_of_X_ne xNe]
  simp only [WeierstrassCurve.Affine.addX, BN254.curve, zero_mul, add_zero, sub_zero]
  field_simp [sub_ne_zero.mpr xNe]
  simp only [BN254.OnCurve] at keyOnCurve inputOnCurve
  linear_combination -inputOnCurve - keyOnCurve

/-- The recovered Y coordinate equals the Mathlib point-addition coordinate. -/
theorem recoveredY [BN254.FieldCertificate] (key input : BN254.AffineInput)
    (keyOnCurve : BN254.OnCurve key) (inputOnCurve : BN254.OnCurve input)
    (xNe : input.x ≠ key.x) :
    evaluate (yCoefficients key) input / evaluate (zCoefficients key) input ^ 3 =
      BN254.curve.toAffine.addY input.x key.x input.y
        (BN254.curve.toAffine.slope input.x key.x input.y key.y) := by
  rw [evaluateY, evaluateZ, WeierstrassCurve.Affine.slope_of_X_ne xNe]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, BN254.curve,
    zero_mul, add_zero, sub_zero]
  field_simp [sub_ne_zero.mpr xNe]
  simp only [BN254.OnCurve] at keyOnCurve inputOnCurve
  linear_combination (input.y - 2 * key.y) * inputOnCurve +
    (2 * input.y - key.y) * keyOnCurve

/-- `scale` applies one digit endomorphism and one Jacobian randomizer. -/
def scale (endomorphismBase : Option BN254.BaseField) (randomizer fallback : BN254.BaseField)
    (coefficients : Coefficients) : Coefficients :=
  match endomorphismBase with
  | none => {
      constant := fallback * randomizer
      x := 0
      y := 0
      xy := 0
      xSquared := 0
      ySquared := 0 }
  | some phi =>
      let phiSquared := phi ^ 2
      let xScale := phiSquared ^ 2
      let yScale := phiSquared * phi
      { constant := coefficients.constant * randomizer
        x := coefficients.x * xScale * randomizer
        y := coefficients.y * yScale * randomizer
        xy := coefficients.xy * (xScale * yScale) * randomizer
        xSquared := coefficients.xSquared * xScale ^ 2 * randomizer
        ySquared := coefficients.ySquared * yScale ^ 2 * randomizer }

/-- The nonzero digit branch applies the endomorphism and one coordinate randomizer. -/
theorem evaluateScaleSome (phi randomizer fallback : BN254.BaseField)
    (coefficients : Coefficients) (input : BN254.AffineInput) :
    evaluate (scale (some phi) randomizer fallback coefficients) input =
      randomizer * evaluate coefficients
        { x := phi ^ 4 * input.x, y := phi ^ 3 * input.y } := by
  simp [scale, evaluate]
  ring

/-- The zero digit branch returns the randomized offset coordinate. -/
theorem evaluateScaleNone (randomizer fallback : BN254.BaseField)
    (coefficients : Coefficients) (input : BN254.AffineInput) :
    evaluate (scale none randomizer fallback coefficients) input =
      fallback * randomizer := by
  simp [scale, evaluate]

/-- `Rows` contains the three rows for one digit and one point offset. -/
structure Rows where
  x : Coefficients
  y : Coefficients
  z : Coefficients

/-- `rows` defines the `x_aux`, `y_aux`, and `z_aux` coordinate functions. -/
def rows (offset : BN254.AffineInput) (endomorphismBase : Option BN254.BaseField)
    (randomizer : BN254.BaseField) : Rows := {
  x := scale endomorphismBase (randomizer ^ 2) offset.x (xCoefficients offset)
  y := scale endomorphismBase (randomizer ^ 3) offset.y (yCoefficients offset)
  z := scale endomorphismBase randomizer 1 (zCoefficients offset)
}

/-- The three rows use the Jacobian powers of one randomizer. -/
theorem evaluateRowsSome (offset input : BN254.AffineInput)
    (phi randomizer : BN254.BaseField) :
    let transformed : BN254.AffineInput :=
      { x := phi ^ 4 * input.x, y := phi ^ 3 * input.y }
    evaluate (rows offset (some phi) randomizer).x input =
        randomizer ^ 2 * evaluate (xCoefficients offset) transformed ∧
      evaluate (rows offset (some phi) randomizer).y input =
        randomizer ^ 3 * evaluate (yCoefficients offset) transformed ∧
      evaluate (rows offset (some phi) randomizer).z input =
        randomizer * evaluate (zCoefficients offset) transformed := by
  simp [rows, evaluateScaleSome]

/-- A sixth-root endomorphism preserves the affine curve equation. -/
theorem transformedOnCurve (phi : BN254.BaseField) (phiSix : phi ^ 6 = 1)
    (input : BN254.AffineInput) (inputOnCurve : BN254.OnCurve input) :
    BN254.OnCurve { x := phi ^ 4 * input.x, y := phi ^ 3 * input.y } := by
  have phiTwelve : phi ^ 12 = 1 := by
    calc
      phi ^ 12 = (phi ^ 6) ^ 2 := by ring
      _ = 1 := by rw [phiSix]; simp
  simp only [BN254.OnCurve, mul_pow]
  rw [show (phi ^ 3) ^ 2 = phi ^ 6 by ring,
    show (phi ^ 4) ^ 3 = phi ^ 12 by ring, phiSix, phiTwelve]
  simpa [BN254.OnCurve] using inputOnCurve

/-- The scaled rows form a Jacobian curve point. -/
theorem evaluatedRowsOnCurve (offset input : BN254.AffineInput)
    (phi randomizer : BN254.BaseField) (phiSix : phi ^ 6 = 1)
    (offsetOnCurve : BN254.OnCurve offset) (inputOnCurve : BN254.OnCurve input) :
    let rows := rows offset (some phi) randomizer
    let x := evaluate rows.x input
    let y := evaluate rows.y input
    let z := evaluate rows.z input
    y ^ 2 = x ^ 3 + 3 * z ^ 6 := by
  have transformedOnCurve := transformedOnCurve phi phiSix input inputOnCurve
  have base := evaluatedOnCurve offset
    { x := phi ^ 4 * input.x, y := phi ^ 3 * input.y }
    offsetOnCurve transformedOnCurve
  obtain ⟨xRow, yRow, zRow⟩ := evaluateRowsSome offset input phi randomizer
  simp only
  rw [xRow, yRow, zRow]
  linear_combination randomizer ^ 6 * base

end Kriterion.ArgoMAC.Coordinates
