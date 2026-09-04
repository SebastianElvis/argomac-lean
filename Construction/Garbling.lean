/-
This file defines the ArgoMAC garbling scheme.
-/

import Construction.ArgoMAC
import GarbledCircuit

namespace Kriterion.ArgoMAC.Garbling

open BN254 Cryptography

/-- This structure contains every explicit garbling input. -/
structure Randomness where
  offsets : FieldMacToECMac.SuccessfulOffsets
  offsetsClamped : ∀ [FieldCertificate] [GroupCertificate], offsets.IsClamped
  pointRandomness : FieldMacToECMac.Randomness
  bridgeKey : BaseField
  curveMask : NonZeroBase
  curveR1 : BaseField
  curveR2 : BaseField
  fixedKeyOracle : PermutationOracle Pipeline.FixedKeyIndex Block
  inputMacKey : InputMacKey
  encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block
  hashOracle : EncPRF.HashOracle

structure EncodingKey where
  scalar : NonZeroScalar
  randomness : Randomness

structure Labels where
  input : BitInput
  inputMac : InputMac

abbrev PublicCircuit := Pipeline.Table

abbrev EvaluationOracle := PermutationOracle Pipeline.FixedKeyIndex Block × PermutationOracle EncPRF.PermutationIndex Block × EncPRF.HashOracle
/-- This query type exposes each public oracle in both permutation directions. -/
inductive OracleQuery
  | fixedForward (index : Pipeline.FixedKeyIndex) (input : Block)
  | fixedInverse (index : Pipeline.FixedKeyIndex) (output : Block)
  | encForward (index : EncPRF.PermutationIndex) (input : Block)
  | encInverse (index : EncPRF.PermutationIndex) (output : Block)
  | hash (input : BaseField)

/-- This function fixes the answer type for each ArgoMAC oracle query. -/
def OracleAnswer : OracleQuery → Type
  | .fixedForward _ _ | .fixedInverse _ _ => Block
  | .encForward _ _ | .encInverse _ _ => Block
  | .hash _ => Block × Block

/-- This specification is the public ArgoMAC oracle surface. -/
def oracleSpec : OracleSpec := {
  Query := OracleQuery
  Answer := OracleAnswer
}

/-- The real handler uses the exact oracles in the garbling random tape. -/
def oracleHandler : OracleHandler oracleSpec Randomness
  | .fixedForward index input, randomness => (randomness.fixedKeyOracle.permutation index input, randomness)
  | .fixedInverse index output, randomness => ((randomness.fixedKeyOracle.permutation index).symm output, randomness)
  | .encForward index input, randomness => (randomness.encPRFOracle.permutation index input, randomness)
  | .encInverse index output, randomness => ((randomness.encPRFOracle.permutation index).symm output, randomness)
  | .hash input, randomness => (randomness.hashOracle input, randomness)

structure Topology where
  coordinateBits : Nat
  outputDigits : Nat

def garble (construction : Construction) (scalar : NonZeroScalar)
    (randomness : Randomness) : PublicCircuit × EncodingKey :=
  (Pipeline.garble
      (FieldMacToECMac.outputKeys construction scalar.value randomness.offsets)
      randomness.pointRandomness randomness.bridgeKey
      randomness.curveMask randomness.curveR1 randomness.curveR2
      randomness.fixedKeyOracle randomness.encPRFOracle randomness.hashOracle
      randomness.inputMacKey,
    { scalar, randomness })

def encode (key : EncodingKey) (input : BitInput) : Labels := {
  input
  inputMac := key.randomness.inputMacKey.encode input
}

def decodeHomogeneous [FieldCertificate]
    (value : FieldMacToECMac.HomogeneousValue) : Option Point :=
  if value.z = 0 then
    if value.x = 0 ∧ value.y ≠ 0 then some 0 else none
  else
    decodePoint { x := value.x / value.z, y := value.y / value.z }

def decodePointMacs [FieldCertificate]
    (values : Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount) :
    Option (List Point) :=
  values.toList.mapM decodeHomogeneous

def decodeResult [FieldCertificate] [GroupCertificate]
    (result : FieldMacToECMac.Result) : Option Point :=
  (decodePointMacs result.pointMacs).map (pointHorner radix)

def evaluate [FieldCertificate] [GroupCertificate] (oracle : EvaluationOracle)
    (table : PublicCircuit) (labels : Labels) : Option Point :=
  (Pipeline.evaluate oracle.1 oracle.2.1 oracle.2.2
    table labels.input labels.inputMac).bind decodeResult

/-- Correct labels evaluate all table rows. -/
theorem evaluateEncodeRows [FieldCertificate] (construction : Construction)
    (key : EncodingKey) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    Pipeline.evaluate key.randomness.fixedKeyOracle key.randomness.encPRFOracle
        key.randomness.hashOracle (garble construction key.scalar key.randomness).1
        (BitInput.ofAffine input) (encode key (BitInput.ofAffine input)).inputMac =
      some (FieldMacToECMac.expectedResult
        (FieldMacToECMac.rowsForOutputKeys
          (FieldMacToECMac.outputKeys construction key.scalar.value key.randomness.offsets)
          key.randomness.pointRandomness) input) := by
  exact Pipeline.evaluateEncoded
    (FieldMacToECMac.outputKeys construction key.scalar.value key.randomness.offsets)
    key.randomness.pointRandomness
    key.randomness.bridgeKey key.randomness.curveMask
    key.randomness.curveR1 key.randomness.curveR2 key.randomness.fixedKeyOracle
    key.randomness.encPRFOracle key.randomness.hashOracle
    key.randomness.inputMacKey input point decoded

def garbledCircuit [FieldCertificate] [GroupCertificate] (construction : Construction) :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness PublicCircuit
      EncodingKey Labels EvaluationOracle := {
  function := fun scalar input => checkedScalarMultiplication scalar.value input
  garble := fun _ scalar randomness => garble construction scalar randomness
  encode := fun key input => encode key (BitInput.ofAffine input)
  evaluate := fun oracle table labels => some (evaluate oracle table labels)
}

def topology (_scalar : NonZeroScalar) : Topology := {
  coordinateBits := 508
  outputDigits := 91
}

end Kriterion.ArgoMAC.Garbling
