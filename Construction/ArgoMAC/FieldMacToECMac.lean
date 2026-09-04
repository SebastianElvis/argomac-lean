/-
This file defines the observable `C_23` table operation.
-/

import Construction.ArgoMAC.Biquadratic
import Construction.ArgoMAC.Coordinates
import Construction.ArgoMAC.RandomizedEncoding

namespace Kriterion.ArgoMAC.FieldMacToECMac

open BN254

def outputMacCount : Nat := 92

/-- The evaluator computes one Jacobian row before batch inversion. -/
structure JacobianValue where
  x : BaseField
  y : BaseField
  z : BaseField
deriving DecidableEq

/-- This operation creates an unchecked affine value after batch inversion. -/
def JacobianValue.toUncheckedAffine [FieldCertificate] (value : JacobianValue) : AffineInput := {
  x := value.x / value.z ^ 2
  y := value.y / value.z ^ 3
}

/-- Each output MAC uses three biquadratic tables. -/
structure RowTable where
  x : Biquadratic.Table
  y : Biquadratic.Table
  z : Biquadratic.Table

/-- This is the logical `field_mac_to_ec_mac::Table` shape. -/
structure Table where
  x : Vector Biquadratic.Table outputMacCount
  y : Vector Biquadratic.Table outputMacCount
  z : Vector Biquadratic.Table outputMacCount

structure RowRandomness where
  rho : NonZeroBase
  x : Biquadratic.XRandomness
  y : Biquadratic.YRandomness
  z : Biquadratic.ZRandomness

structure RowOracles where
  x : Biquadratic.Oracles
  y : Biquadratic.Oracles
  z : Biquadratic.Oracles

abbrev Randomness := Vector RowRandomness outputMacCount
abbrev Oracles := Vector RowOracles outputMacCount
abbrev Rows := Vector Coordinates.Rows outputMacCount

/-- This is a non-identity affine output offset. -/
structure AffineOffset where
  coordinates : AffineInput
  onCurve : OnCurve coordinates

def AffineOffset.point [FieldCertificate] (offset : AffineOffset) : Point :=
  (decodePoint offset.coordinates).get (by
    have defined : decodePoint offset.coordinates ≠ none :=
      (decodePoint_defined offset.coordinates).mpr offset.onCurve
    cases decoded : decodePoint offset.coordinates with
    | none => exact (defined decoded).elim
    | some point => rfl)

def freeOffsetPoints [FieldCertificate] (free : Vector AffineOffset 91) : List Point :=
  free.toList.map fun offset => AffineOffset.point offset

def clampedFirst [FieldCertificate] [GroupCertificate]
    (free : Vector AffineOffset 91) : Point :=
  -(radix • pointHorner radix (freeOffsetPoints free))

/-- This contains the affine offsets from one successful garbling run. -/
structure SuccessfulOffsets where
  first : AffineOffset
  free : Vector AffineOffset 91

def SuccessfulOffsets.IsClamped [FieldCertificate] [GroupCertificate]
    (offsets : SuccessfulOffsets) : Prop :=
  AffineOffset.point offsets.first = clampedFirst offsets.free

def SuccessfulOffsets.values (offsets : SuccessfulOffsets) :
    Vector AffineOffset outputMacCount :=
  ⟨(offsets.first :: offsets.free.toList).toArray, by simp [outputMacCount]⟩

/-- This is one successful `EndoMacKey`. -/
structure OutputKey where
  digit : Digit
  offset : AffineOffset

abbrev OutputKeys := Vector OutputKey outputMacCount

def outputKeys (construction : Construction) (scalar : ScalarField)
    (offsets : SuccessfulOffsets) : OutputKeys :=
  let digits : Vector Digit outputMacCount :=
    ⟨(construction.digits scalar).toArray,
      by simpa [outputMacCount] using construction.digitCount scalar⟩
  Vector.ofFn fun index => {
    digit := digits.get index
    offset := offsets.values.get index
  }

def rowsForOutputKeys (keys : OutputKeys) (randomness : Randomness) : Rows :=
  Vector.ofFn fun index =>
    Coordinates.rows (keys.get index).offset.coordinates
      (digitEndomorphismBase (keys.get index).digit)
      (randomness.get index).rho.value

def SparseRow (rows : Coordinates.Rows) : Prop :=
  rows.x.xy = 0 ∧ rows.x.ySquared = 0 ∧ rows.y.x = 0 ∧
    rows.z.y = 0 ∧ rows.z.xy = 0 ∧ rows.z.xSquared = 0 ∧
    rows.z.ySquared = 0

theorem coordinatesRowsSparse (offset : AffineInput)
    (endomorphismBase : Option BaseField) (randomizer : BaseField) :
    SparseRow (Coordinates.rows offset endomorphismBase randomizer) := by
  cases endomorphismBase <;> simp [SparseRow, Coordinates.rows, Coordinates.scale,
    Coordinates.xCoefficients, Coordinates.yCoefficients, Coordinates.zCoefficients]

theorem rowsForOutputKeysSparse (keys : OutputKeys) (randomness : Randomness) :
    ∀ index, SparseRow ((rowsForOutputKeys keys randomness).get index) := by
  intro index
  simp [rowsForOutputKeys, coordinatesRowsSparse]

def garbleRow (rows : Coordinates.Rows) (randomness : RowRandomness)
    (oracles : RowOracles) (inputKey : InputMacKey) : RowTable := {
  x := Biquadratic.garbleX rows.x.constant rows.x.x rows.x.y rows.x.xSquared
    randomness.x oracles.x inputKey
  y := Biquadratic.garbleY rows.y.constant rows.y.y rows.y.xy rows.y.xSquared
    rows.y.ySquared randomness.y oracles.y inputKey
  z := Biquadratic.garbleZ rows.z.constant rows.z.x randomness.z oracles.z inputKey
}

def garble (rows : Rows) (randomness : Randomness)
    (oracles : Oracles) (inputKey : InputMacKey) : Table := {
  x := Vector.ofFn fun index =>
    (garbleRow (rows.get index) (randomness.get index)
      (oracles.get index) inputKey).x
  y := Vector.ofFn fun index =>
    (garbleRow (rows.get index) (randomness.get index)
      (oracles.get index) inputKey).y
  z := Vector.ofFn fun index =>
    (garbleRow (rows.get index) (randomness.get index)
      (oracles.get index) inputKey).z
}

def evaluateJacobian (table : Table) (oracles : Oracles)
    (input : AffineInput) (inputMac : InputMac) : Vector JacobianValue outputMacCount :=
  Vector.ofFn fun index => {
    x := Biquadratic.evaluate (oracles.get index).x (table.x.get index) input inputMac
    y := Biquadratic.evaluate (oracles.get index).y (table.y.get index) input inputMac
    z := Biquadratic.evaluate (oracles.get index).z (table.z.get index) input inputMac
  }

/-- The result contains the input and 92 unchecked affine MAC values. -/
structure Result where
  point : AffineInput
  pointMacs : Vector AffineInput outputMacCount

def evaluate [FieldCertificate] (table : Table) (oracles : Oracles)
    (input : AffineInput) (inputMac : InputMac) : Result := {
  point := input
  pointMacs := (evaluateJacobian table oracles input inputMac).map
    JacobianValue.toUncheckedAffine
}

def evaluateRow (rows : Coordinates.Rows) (input : AffineInput) : JacobianValue := {
  x := Coordinates.evaluate rows.x input
  y := Coordinates.evaluate rows.y input
  z := Coordinates.evaluate rows.z input
}

def evaluateRows (rows : Rows) (input : AffineInput) :
    Vector JacobianValue outputMacCount :=
  Vector.ofFn fun index => evaluateRow (rows.get index) input

theorem evaluateRowsNone [FieldCertificate] (offset input : AffineInput)
    (randomizer : BaseField) (randomizerNonzero : randomizer ≠ 0) :
    (evaluateRow (Coordinates.rows offset none randomizer) input).toUncheckedAffine =
      offset := by
  cases offset with
  | mk offsetX offsetY =>
      simp [evaluateRow, JacobianValue.toUncheckedAffine, Coordinates.rows,
        Coordinates.scale, Coordinates.evaluate]
      constructor <;> field_simp

def transformedInput (phi : BaseField) (input : AffineInput) : AffineInput := {
  x := phi ^ 4 * input.x
  y := phi ^ 3 * input.y
}

/-- This condition excludes a zero Jacobian `Z` in every nonzero digit row. -/
def EvaluationSafe (keys : OutputKeys) (input : AffineInput) : Prop :=
  ∀ index phi, digitEndomorphismBase (keys.get index).digit = some phi →
    (transformedInput phi input).x ≠ (keys.get index).offset.coordinates.x

def addedCoordinates [FieldCertificate] (offset input : AffineInput) : AffineInput := {
  x := curve.toAffine.addX input.x offset.x
    (curve.toAffine.slope input.x offset.x input.y offset.y)
  y := curve.toAffine.addY input.x offset.x input.y
    (curve.toAffine.slope input.x offset.x input.y offset.y)
}

theorem evaluateRowsSome [FieldCertificate] (offset input : AffineInput)
    (phi randomizer : BaseField) (phiSix : phi ^ 6 = 1)
    (offsetOnCurve : OnCurve offset) (inputOnCurve : OnCurve input)
    (xDifferent : (transformedInput phi input).x ≠ offset.x)
    (randomizerNonzero : randomizer ≠ 0) :
    (evaluateRow (Coordinates.rows offset (some phi) randomizer) input).toUncheckedAffine =
      addedCoordinates offset (transformedInput phi input) := by
  have transformedOnCurve : OnCurve (transformedInput phi input) :=
    Coordinates.transformedOnCurve phi phiSix input inputOnCurve
  have rows := Coordinates.evaluateRowsSome offset input phi randomizer
  obtain ⟨xRow, yRow, zRow⟩ := rows
  change Coordinates.evaluate (Coordinates.rows offset (some phi) randomizer).x input =
    randomizer ^ 2 * Coordinates.evaluate (Coordinates.xCoefficients offset)
      (transformedInput phi input) at xRow
  change Coordinates.evaluate (Coordinates.rows offset (some phi) randomizer).y input =
    randomizer ^ 3 * Coordinates.evaluate (Coordinates.yCoefficients offset)
      (transformedInput phi input) at yRow
  change Coordinates.evaluate (Coordinates.rows offset (some phi) randomizer).z input =
    randomizer * Coordinates.evaluate (Coordinates.zCoefficients offset)
      (transformedInput phi input) at zRow
  have zNonzero : Coordinates.evaluate (Coordinates.zCoefficients offset)
      (transformedInput phi input) ≠ 0 := by
    rw [Coordinates.evaluateZ]
    exact sub_ne_zero.mpr xDifferent
  rw [JacobianValue.toUncheckedAffine]
  congr 1
  · change Coordinates.evaluate (Coordinates.rows offset (some phi) randomizer).x input /
        Coordinates.evaluate (Coordinates.rows offset (some phi) randomizer).z input ^ 2 = _
    rw [xRow, zRow]
    rw [show randomizer ^ 2 *
          Coordinates.evaluate (Coordinates.xCoefficients offset) (transformedInput phi input) /
          (randomizer * Coordinates.evaluate (Coordinates.zCoefficients offset)
            (transformedInput phi input)) ^ 2 =
        Coordinates.evaluate (Coordinates.xCoefficients offset) (transformedInput phi input) /
          Coordinates.evaluate (Coordinates.zCoefficients offset)
            (transformedInput phi input) ^ 2 by field_simp]
    exact Coordinates.recoveredX offset (transformedInput phi input)
      offsetOnCurve transformedOnCurve xDifferent
  · change Coordinates.evaluate (Coordinates.rows offset (some phi) randomizer).y input /
        Coordinates.evaluate (Coordinates.rows offset (some phi) randomizer).z input ^ 3 = _
    rw [yRow, zRow]
    rw [show randomizer ^ 3 *
          Coordinates.evaluate (Coordinates.yCoefficients offset) (transformedInput phi input) /
          (randomizer * Coordinates.evaluate (Coordinates.zCoefficients offset)
            (transformedInput phi input)) ^ 3 =
        Coordinates.evaluate (Coordinates.yCoefficients offset) (transformedInput phi input) /
          Coordinates.evaluate (Coordinates.zCoefficients offset)
            (transformedInput phi input) ^ 3 by field_simp]
    exact Coordinates.recoveredY offset (transformedInput phi input)
      offsetOnCurve transformedOnCurve xDifferent

def expectedResult [FieldCertificate] (rows : Rows)
    (input : AffineInput) : Result := {
  point := input
  pointMacs := (evaluateRows rows input).map JacobianValue.toUncheckedAffine
}

theorem evaluateJacobianEncoded (rows : Rows) (randomness : Randomness)
    (oracles : Oracles) (inputKey : InputMacKey) (input : AffineInput) :
    (∀ index, SparseRow (rows.get index)) →
    evaluateJacobian (garble rows randomness oracles inputKey) oracles
        input (inputKey.encodeAffine input) =
      evaluateRows rows input := by
  intro sparse
  apply Vector.ext
  intro index inRange
  have rowSparse := sparse ⟨index, inRange⟩
  rcases rowSparse with ⟨xXY, xY2, yX, zY, zXY, zX2, zY2⟩
  simp only [evaluateJacobian, garble, garbleRow, Vector.getElem_ofFn,
    Vector.get_ofFn]
  rw [Biquadratic.evaluateEncodedX, Biquadratic.evaluateEncodedY,
    Biquadratic.evaluateEncodedZ]
  simp [evaluateRows, evaluateRow, Coordinates.evaluate, xXY, xY2, yX, zY, zXY,
    zX2, zY2]
  ring

theorem evaluateEncoded [FieldCertificate]
    (rows : Rows) (randomness : Randomness)
    (oracles : Oracles) (inputKey : InputMacKey) (input : AffineInput) :
    (∀ index, SparseRow (rows.get index)) →
    evaluate (garble rows randomness oracles inputKey) oracles
        input (inputKey.encodeAffine input) = expectedResult rows input := by
  intro sparse
  rw [evaluate, evaluateJacobianEncoded rows randomness oracles inputKey input sparse]
  rfl

end Kriterion.ArgoMAC.FieldMacToECMac
