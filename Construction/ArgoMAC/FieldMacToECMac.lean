/-
This file defines the observable `C_23` table operation.
-/

import Construction.ArgoMAC.Biquadratic
import Construction.ArgoMAC.Coordinates
import Construction.ArgoMAC.RandomizedEncoding

namespace Kriterion.ArgoMAC.FieldMacToECMac

open BN254

def outputMacCount : Nat := 91

/-- The evaluator computes one homogeneous row before batch inversion. -/
structure HomogeneousValue where
  x : BaseField
  y : BaseField
  z : BaseField
deriving DecidableEq

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

def freeOffsetPoints [FieldCertificate] (free : Vector AffineOffset 90) : List Point :=
  free.toList.map fun offset => AffineOffset.point offset

def clampedFirst [FieldCertificate] [GroupCertificate]
    (free : Vector AffineOffset 90) : Point :=
  -(radix • pointHorner radix (freeOffsetPoints free))

/-- This contains the affine offsets from one successful garbling run. -/
structure SuccessfulOffsets where
  first : AffineOffset
  free : Vector AffineOffset 90

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
  let offsetValues := offsets.values
  Vector.ofFn fun index => {
    digit := digits.get index
    offset := offsetValues.get index
  }

def rowsForOutputKeys (keys : OutputKeys) (randomness : Randomness) : Rows :=
  Vector.ofFn fun index =>
    Coordinates.rows (keys.get index).offset.coordinates
      (digitEndomorphismBase (keys.get index).digit)
      (randomness.get index).rho.value

def SparseRow (rows : Coordinates.Rows) : Prop :=
  rows.x.xSquared = 0 ∧ rows.y.y = 0 ∧ rows.y.xy = 0 ∧ rows.z.x = 0

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
  x := Biquadratic.garbleX rows.x.constant rows.x.x rows.x.y rows.x.xy rows.x.ySquared
    randomness.x oracles.x inputKey
  y := Biquadratic.garbleY rows.y.constant rows.y.x rows.y.xSquared rows.y.ySquared
    randomness.y oracles.y inputKey
  z := Biquadratic.garbleZ rows.z.constant rows.z.y rows.z.xy rows.z.xSquared
    rows.z.ySquared randomness.z oracles.z inputKey
}

def garble (rows : Rows) (randomness : Randomness)
    (oracles : Oracles) (inputKey : InputMacKey) : Table :=
  let tables := Vector.ofFn fun index =>
    garbleRow (rows.get index) (randomness.get index) (oracles.get index) inputKey
  { x := tables.map RowTable.x
    y := tables.map RowTable.y
    z := tables.map RowTable.z }

def evaluateHomogeneous (table : Table) (oracles : Oracles)
    (input : AffineInput) (inputMac : InputMac) : Vector HomogeneousValue outputMacCount :=
  Vector.ofFn fun index => {
    x := Biquadratic.evaluate (oracles.get index).x (table.x.get index) input inputMac
    y := Biquadratic.evaluate (oracles.get index).y (table.y.get index) input inputMac
    z := Biquadratic.evaluate (oracles.get index).z (table.z.get index) input inputMac
  }

/-- The result keeps 91 homogeneous MAC values for checked decode. -/
structure Result where
  point : AffineInput
  pointMacs : Vector HomogeneousValue outputMacCount

def evaluate (table : Table) (oracles : Oracles)
    (input : AffineInput) (inputMac : InputMac) : Result := {
  point := input
  pointMacs := evaluateHomogeneous table oracles input inputMac
}

def evaluateRow (rows : Coordinates.Rows) (input : AffineInput) : HomogeneousValue := {
  x := Coordinates.evaluate rows.x input
  y := Coordinates.evaluate rows.y input
  z := Coordinates.evaluate rows.z input
}

def evaluateRows (rows : Rows) (input : AffineInput) :
    Vector HomogeneousValue outputMacCount :=
  Vector.ofFn fun index => evaluateRow (rows.get index) input

theorem evaluateRowsNone (offset input : AffineInput) (randomizer : BaseField) :
    evaluateRow (Coordinates.rows offset none randomizer) input = {
      x := randomizer * offset.x
      y := randomizer * offset.y
      z := randomizer } := by
  cases offset with
  | mk offsetX offsetY =>
      simp [evaluateRow, Coordinates.rows, Coordinates.scale, Coordinates.evaluate]
      constructor <;> ring

def transformedInput (phi : BaseField) (input : AffineInput) : AffineInput := {
  x := phi ^ 4 * input.x
  y := phi ^ 3 * input.y
}

/-- A nonzero-digit row evaluates the complete law with one common scale. -/
theorem evaluateRowsSome (offset input : AffineInput) (phi randomizer : BaseField) :
    evaluateRow (Coordinates.rows offset (some phi) randomizer) input = {
      x := randomizer * Coordinates.algorithmX offset (transformedInput phi input)
      y := randomizer * Coordinates.algorithmY offset (transformedInput phi input)
      z := randomizer * Coordinates.algorithmZ offset (transformedInput phi input) } := by
  have rows := Coordinates.evaluateRowsSome offset input phi randomizer
  obtain ⟨xRow, yRow, zRow⟩ := rows
  simp only [evaluateRow]
  rw [xRow, yRow, zRow, Coordinates.evaluateX, Coordinates.evaluateY,
    Coordinates.evaluateZ]
  simp [transformedInput]

def expectedResult (rows : Rows)
    (input : AffineInput) : Result := {
  point := input
  pointMacs := evaluateRows rows input
}

theorem evaluateHomogeneousEncoded (rows : Rows) (randomness : Randomness)
    (oracles : Oracles) (inputKey : InputMacKey) (input : AffineInput) :
    (∀ index, SparseRow (rows.get index)) →
    evaluateHomogeneous (garble rows randomness oracles inputKey) oracles
        input (inputKey.encodeAffine input) =
      evaluateRows rows input := by
  intro sparse
  apply Vector.ext
  intro index inRange
  have rowSparse := sparse ⟨index, inRange⟩
  rcases rowSparse with ⟨xX2, yY, yXY, zX⟩
  simp only [evaluateHomogeneous, garble, garbleRow, Vector.getElem_ofFn,
    Vector.get_map, Vector.get_ofFn]
  rw [Biquadratic.evaluateEncodedX, Biquadratic.evaluateEncodedY,
    Biquadratic.evaluateEncodedZ]
  simp [evaluateRows, evaluateRow, Coordinates.evaluate, xX2, yY, yXY, zX]
  ring_nf
  constructor <;> trivial

theorem evaluateEncoded
    (rows : Rows) (randomness : Randomness)
    (oracles : Oracles) (inputKey : InputMacKey) (input : AffineInput) :
    (∀ index, SparseRow (rows.get index)) →
    evaluate (garble rows randomness oracles inputKey) oracles
        input (inputKey.encodeAffine input) = expectedResult rows input := by
  intro sparse
  rw [evaluate, evaluateHomogeneousEncoded rows randomness oracles inputKey input sparse]
  rfl

end Kriterion.ArgoMAC.FieldMacToECMac
