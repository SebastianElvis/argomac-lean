/-
This file defines three sparse biquadratic tables.
-/

import Construction.ArgoMAC.DigitAdaptor
import Construction.ArgoMAC.Input

namespace Kriterion.ArgoMAC.Biquadratic

open BN254

/-- Each possible adaptor has one fixed-key window family. -/
structure Oracles where
  y6 : Nat → BitAdaptor.FixedKeyOracle
  y8 : Nat → BitAdaptor.FixedKeyOracle
  y10 : Nat → BitAdaptor.FixedKeyOracle
  x7 : Nat → BitAdaptor.FixedKeyOracle
  x9 : Nat → BitAdaptor.FixedKeyOracle

/-- This is the logical table shape. -/
structure Table where
  c0 : Option BaseField
  c1 : Option BaseField
  c2 : Option BaseField
  c3 : Option BaseField
  c4 : Option BaseField
  c5 : Option BaseField
  x7 : Option (Vector BitAdaptor.Table coordinateBitCount)
  x9 : Option (Vector BitAdaptor.Table coordinateBitCount)
  y6 : Option (Vector BitAdaptor.Table coordinateBitCount)
  y8 : Option (Vector BitAdaptor.Table coordinateBitCount)
  y10 : Option (Vector BitAdaptor.Table coordinateBitCount)

structure XRandomness where
  r1 : BaseField
  r2 : BaseField
  r4 : BaseField

structure YRandomness where
  r2 : BaseField
  r3 : BaseField
  r4 : BaseField
  r5 : BaseField

structure ZRandomness where
  r1 : BaseField

def evaluateDigit (windows : Nat → BitAdaptor.FixedKeyOracle)
    (table : Option (Vector BitAdaptor.Table coordinateBitCount))
    (value : BaseField) (inputMac : CoordinateMac) : BaseField :=
  match table with
  | none => 0
  | some rows =>
      DigitAdaptor.fromBits fun index =>
        (DigitAdaptor.evaluate windows (coordinateValues value) rows inputMac).get index

@[simp] theorem evaluateDigitNone (windows : Nat → BitAdaptor.FixedKeyOracle)
    (value : BaseField) (inputMac : CoordinateMac) :
    evaluateDigit windows none value inputMac = 0 := rfl

def coefficient (value : Option BaseField) : BaseField := value.getD 0

def evaluate (oracles : Oracles) (table : Table) (input : AffineInput)
    (inputMac : InputMac) : BaseField :=
  let c6 := evaluateDigit oracles.y6 table.y6 input.y inputMac.y
  let c7 := evaluateDigit oracles.x7 table.x7 input.x inputMac.x
  let c8 := evaluateDigit oracles.y8 table.y8 input.y inputMac.y
  let c9 := evaluateDigit oracles.x9 table.x9 input.x inputMac.x
  let c10 := evaluateDigit oracles.y10 table.y10 input.y inputMac.y
  coefficient table.c0 + coefficient table.c1 * input.x +
    coefficient table.c2 * input.y + coefficient table.c3 * input.x * input.y +
    coefficient table.c4 * input.x ^ 2 + coefficient table.c5 * input.y ^ 2 +
    c6 * input.x + c7 * input.x + c8 * input.y + c9 + c10

/-- This is the sparse X-coordinate table. -/
def garbleX (c0 c1 c2 c4 : BaseField) (randomness : XRandomness)
    (oracles : Oracles) (inputKey : InputMacKey) : Table :=
  let y10 := DigitAdaptor.garble oracles.y10 (-randomness.r2) inputKey.y
  let r10 := DigitAdaptor.bitsK y10.2
  let x7 := DigitAdaptor.garble oracles.x7 (-randomness.r4) inputKey.x
  let r7 := DigitAdaptor.bitsK x7.2
  let x9 := DigitAdaptor.garble oracles.x9 (-(randomness.r1 + r7)) inputKey.x
  let r9 := DigitAdaptor.bitsK x9.2
  { c0 := some (c0 - r10 - r9)
    c1 := some (c1 + randomness.r1)
    c2 := some (c2 + randomness.r2)
    c3 := none
    c4 := some (c4 + randomness.r4)
    c5 := none
    x7 := some x7.1
    x9 := some x9.1
    y6 := none
    y8 := none
    y10 := some y10.1 }

/-- This is the sparse Y-coordinate table. -/
def garbleY (c0 c2 c3 c4 c5 : BaseField) (randomness : YRandomness)
    (oracles : Oracles) (inputKey : InputMacKey) : Table :=
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
  { c0 := some (c0 - r10 - r9)
    c1 := none
    c2 := some (c2 + randomness.r2)
    c3 := some (c3 + randomness.r3)
    c4 := some (c4 + randomness.r4)
    c5 := some (c5 + randomness.r5)
    x7 := some x7.1
    x9 := some x9.1
    y6 := some y6.1
    y8 := some y8.1
    y10 := some y10.1 }

/-- This is the sparse Z-coordinate table. -/
def garbleZ (c0 c1 : BaseField) (randomness : ZRandomness)
    (oracles : Oracles) (inputKey : InputMacKey) : Table :=
  let x9 := DigitAdaptor.garble oracles.x9 (-randomness.r1) inputKey.x
  let r9 := DigitAdaptor.bitsK x9.2
  { c0 := some (c0 - r9)
    c1 := some (c1 + randomness.r1)
    c2 := none
    c3 := none
    c4 := none
    c5 := none
    x7 := none
    x9 := some x9.1
    y6 := none
    y8 := none
    y10 := none }

theorem evaluateDigitGarbleEncode (windows : Nat → BitAdaptor.FixedKeyOracle)
    (slope : BaseField) (key : CoordinateMacKey) (value : BaseField) :
    evaluateDigit windows (some (DigitAdaptor.garble windows slope key).1) value
        (encodeCoordinate key (coordinateBits value)) =
      slope * value + DigitAdaptor.bitsK (DigitAdaptor.garble windows slope key).2 := by
  rw [evaluateDigit, show encodeCoordinate key (coordinateBits value) =
    DigitAdaptor.encode key (coordinateValues value) from rfl]
  rw [DigitAdaptor.evaluateValueGarbleEncode, coordinateBitValue]

theorem evaluateEncodedX (c0 c1 c2 c4 : BaseField) (randomness : XRandomness)
    (oracles : Oracles) (inputKey : InputMacKey) (input : AffineInput) :
    evaluate oracles (garbleX c0 c1 c2 c4 randomness oracles inputKey)
        input (inputKey.encodeAffine input) =
      c0 + c1 * input.x + c2 * input.y + c4 * input.x ^ 2 := by
  simp only [evaluate, garbleX, InputMacKey.encodeAffine, InputMacKey.encode,
    BitInput.ofAffine, coefficient, evaluateDigitNone, Option.getD_some, Option.getD_none]
  rw [evaluateDigitGarbleEncode, evaluateDigitGarbleEncode,
    evaluateDigitGarbleEncode]
  ring

theorem evaluateEncodedY (c0 c2 c3 c4 c5 : BaseField) (randomness : YRandomness)
    (oracles : Oracles) (inputKey : InputMacKey) (input : AffineInput) :
    evaluate oracles (garbleY c0 c2 c3 c4 c5 randomness oracles inputKey)
        input (inputKey.encodeAffine input) =
      c0 + c2 * input.y + c3 * input.x * input.y + c4 * input.x ^ 2 +
        c5 * input.y ^ 2 := by
  simp only [evaluate, garbleY, InputMacKey.encodeAffine, InputMacKey.encode,
    BitInput.ofAffine, coefficient, Option.getD_some, Option.getD_none]
  rw [evaluateDigitGarbleEncode, evaluateDigitGarbleEncode,
    evaluateDigitGarbleEncode, evaluateDigitGarbleEncode,
    evaluateDigitGarbleEncode]
  ring

theorem evaluateEncodedZ (c0 c1 : BaseField) (randomness : ZRandomness)
    (oracles : Oracles) (inputKey : InputMacKey) (input : AffineInput) :
    evaluate oracles (garbleZ c0 c1 randomness oracles inputKey)
        input (inputKey.encodeAffine input) = c0 + c1 * input.x := by
  simp only [evaluate, garbleZ, InputMacKey.encodeAffine, InputMacKey.encode,
    BitInput.ofAffine, coefficient, evaluateDigitNone, Option.getD_some, Option.getD_none]
  rw [evaluateDigitGarbleEncode]
  ring

end Kriterion.ArgoMAC.Biquadratic
