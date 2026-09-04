/-
This file defines the complete BN254 homogeneous addition rows.
The rows use Algorithm 7 from Renes, Costello, and Batina.
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

/-- `algorithmX` is the factored RCB X formula for an affine offset. -/
def algorithmX (offset input : BN254.AffineInput) : BN254.BaseField :=
  (offset.x * input.y + offset.y * input.x) * (offset.y * input.y - 9) -
    9 * (offset.y + input.y) * (offset.x + input.x)

/-- `algorithmY` is the factored RCB Y formula for an affine offset. -/
def algorithmY (offset input : BN254.AffineInput) : BN254.BaseField :=
  (offset.y * input.y + 9) * (offset.y * input.y - 9) +
    27 * offset.x * input.x * (offset.x + input.x)

/-- `algorithmZ` is the factored RCB Z formula for an affine offset. -/
def algorithmZ (offset input : BN254.AffineInput) : BN254.BaseField :=
  (offset.y + input.y) * (offset.y * input.y + 9) +
    3 * offset.x * input.x *
      (offset.x * input.y + offset.y * input.x)

/-- `xCoefficients` is the expanded RCB X formula. -/
def xCoefficients (offset : BN254.AffineInput) : Coefficients := {
  constant := -9 * offset.x * offset.y
  x := -18 * offset.y
  y := -18 * offset.x
  xy := offset.y ^ 2 - 9
  xSquared := 0
  ySquared := offset.x * offset.y
}

/-- `yCoefficients` is the expanded RCB Y formula. -/
def yCoefficients (offset : BN254.AffineInput) : Coefficients := {
  constant := -81
  x := 27 * offset.x ^ 2
  y := 0
  xy := 0
  xSquared := 27 * offset.x
  ySquared := offset.y ^ 2
}

/-- `zCoefficients` is the expanded RCB Z formula. -/
def zCoefficients (offset : BN254.AffineInput) : Coefficients := {
  constant := 9 * offset.y
  x := 0
  y := offset.y ^ 2 + 9
  xy := 3 * offset.x ^ 2
  xSquared := 3 * offset.x * offset.y
  ySquared := offset.y
}

/-- The expanded X row equals RCB Algorithm 7. -/
theorem evaluateX (offset input : BN254.AffineInput) :
    evaluate (xCoefficients offset) input = algorithmX offset input := by
  simp only [evaluate, xCoefficients, algorithmX]
  ring

/-- The expanded Y row equals RCB Algorithm 7. -/
theorem evaluateY (offset input : BN254.AffineInput) :
    evaluate (yCoefficients offset) input = algorithmY offset input := by
  simp only [evaluate, yCoefficients, algorithmY]
  ring

/-- The expanded Z row equals RCB Algorithm 7. -/
theorem evaluateZ (offset input : BN254.AffineInput) :
    evaluate (zCoefficients offset) input = algorithmZ offset input := by
  simp only [evaluate, zCoefficients, algorithmZ]
  ring

private theorem curveYPowers (x y : BN254.BaseField) (onCurve : y ^ 2 = x ^ 3 + 3) :
    y ^ 3 = y * (x ^ 3 + 3) ∧
      y ^ 4 = (x ^ 3 + 3) ^ 2 ∧
      y ^ 5 = y * (x ^ 3 + 3) ^ 2 ∧
      y ^ 6 = (x ^ 3 + 3) ^ 3 := by
  constructor
  · calc
      y ^ 3 = y * y ^ 2 := by ring
      _ = y * (x ^ 3 + 3) := by rw [onCurve]
  constructor
  · calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (x ^ 3 + 3) ^ 2 := by rw [onCurve]
  constructor
  · calc
      y ^ 5 = y * (y ^ 2) ^ 2 := by ring
      _ = y * (x ^ 3 + 3) ^ 2 := by rw [onCurve]
  · calc
      y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ = (x ^ 3 + 3) ^ 3 := by rw [onCurve]

/-- The three RCB rows satisfy the homogeneous curve equation. -/
theorem evaluatedOnCurve (offset input : BN254.AffineInput)
    (offsetOnCurve : BN254.OnCurve offset) (inputOnCurve : BN254.OnCurve input) :
    let x := evaluate (xCoefficients offset) input
    let y := evaluate (yCoefficients offset) input
    let z := evaluate (zCoefficients offset) input
    y ^ 2 * z = x ^ 3 + 3 * z ^ 3 := by
  obtain ⟨offsetY3, offsetY4, offsetY5, offsetY6⟩ :=
    curveYPowers offset.x offset.y offsetOnCurve
  obtain ⟨inputY3, inputY4, inputY5, inputY6⟩ :=
    curveYPowers input.x input.y inputOnCurve
  simp only [evaluate, xCoefficients, yCoefficients, zCoefficients]
  ring_nf
  rw [offsetY6, offsetY5, offsetY4, offsetY3, offsetOnCurve,
    inputY6, inputY5, inputY4, inputY3, inputOnCurve]
  ring

/-- `scale` applies one digit endomorphism and one homogeneous randomizer. -/
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

/-- A nonzero digit applies the endomorphism and one homogeneous randomizer. -/
theorem evaluateScaleSome (phi randomizer fallback : BN254.BaseField)
    (coefficients : Coefficients) (input : BN254.AffineInput) :
    evaluate (scale (some phi) randomizer fallback coefficients) input =
      randomizer * evaluate coefficients
        { x := phi ^ 4 * input.x, y := phi ^ 3 * input.y } := by
  simp [scale, evaluate]
  ring

/-- A zero digit returns one randomized offset coordinate. -/
theorem evaluateScaleNone (randomizer fallback : BN254.BaseField)
    (coefficients : Coefficients) (input : BN254.AffineInput) :
    evaluate (scale none randomizer fallback coefficients) input =
      fallback * randomizer := by
  simp [scale, evaluate]

/-- `Rows` contains the three homogeneous rows for one output MAC. -/
structure Rows where
  x : Coefficients
  y : Coefficients
  z : Coefficients

/-- `rows` applies the digit endomorphism and a common homogeneous scale. -/
def rows (offset : BN254.AffineInput) (endomorphismBase : Option BN254.BaseField)
    (randomizer : BN254.BaseField) : Rows := {
  x := scale endomorphismBase randomizer offset.x (xCoefficients offset)
  y := scale endomorphismBase randomizer offset.y (yCoefficients offset)
  z := scale endomorphismBase randomizer 1 (zCoefficients offset)
}

/-- The three nonzero-digit rows use one common homogeneous scale. -/
theorem evaluateRowsSome (offset input : BN254.AffineInput)
    (phi randomizer : BN254.BaseField) :
    let transformed : BN254.AffineInput :=
      { x := phi ^ 4 * input.x, y := phi ^ 3 * input.y }
    evaluate (rows offset (some phi) randomizer).x input =
        randomizer * evaluate (xCoefficients offset) transformed ∧
      evaluate (rows offset (some phi) randomizer).y input =
        randomizer * evaluate (yCoefficients offset) transformed ∧
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

/-- The scaled RCB rows satisfy the homogeneous curve equation. -/
theorem evaluatedRowsOnCurve (offset input : BN254.AffineInput)
    (phi randomizer : BN254.BaseField) (phiSix : phi ^ 6 = 1)
    (offsetOnCurve : BN254.OnCurve offset) (inputOnCurve : BN254.OnCurve input) :
    let rows := rows offset (some phi) randomizer
    let x := evaluate rows.x input
    let y := evaluate rows.y input
    let z := evaluate rows.z input
    y ^ 2 * z = x ^ 3 + 3 * z ^ 3 := by
  have transformedOnCurve := transformedOnCurve phi phiSix input inputOnCurve
  have base := evaluatedOnCurve offset
    { x := phi ^ 4 * input.x, y := phi ^ 3 * input.y }
    offsetOnCurve transformedOnCurve
  obtain ⟨xRow, yRow, zRow⟩ := evaluateRowsSome offset input phi randomizer
  simp only
  rw [xRow, yRow, zRow]
  linear_combination randomizer ^ 3 * base

end Kriterion.ArgoMAC.Coordinates
