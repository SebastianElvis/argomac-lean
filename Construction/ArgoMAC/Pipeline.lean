/-
This file connects `C_1`, `C_23`, and `C_45`.
The active paper shows this pipeline at `fig:garbled_c_with_cm_opt`.
-/

import Construction.ArgoMAC.CurveMembership
import Construction.ArgoMAC.EncPRF
import Construction.ArgoMAC.FieldMacToECMac

namespace Kriterion.ArgoMAC.Pipeline

open BN254 Cryptography

def curveDigitAdaptorCount : Nat := 5
def pointDigitAdaptorsPerOutput : Nat := 13

def digitAdaptorCount : Nat :=
  curveDigitAdaptorCount + FieldMacToECMac.outputMacCount * pointDigitAdaptorsPerOutput

def fixedKeyWindowCount : Nat :=
  digitAdaptorCount * BitAdaptor.fixedKeyWindowCount

def permutationCount : Nat :=
  fixedKeyWindowCount * BitAdaptor.fixedKeyPermutationsPerWindow

def hashPermutationCount : Nat :=
  fixedKeyWindowCount * 3

def padPermutationCount : Nat :=
  fixedKeyWindowCount * 2

theorem fixedKeyWindowCountValue : fixedKeyWindowCount = 3564 := by decide
theorem permutationCountValue : permutationCount = 17820 := by decide
theorem hashPermutationCountValue : hashPermutationCount = 10692 := by decide
theorem padPermutationCountValue : padPermutationCount = 7128 := by decide

inductive CurveAdaptor
  | y4 | y6 | x3 | x5 | x7
deriving DecidableEq, Fintype

inductive PointCoordinate
  | x | y | z
deriving DecidableEq, Fintype

inductive PointAdaptor
  | y6 | y8 | y10 | x7 | x9
deriving DecidableEq, Fintype

inductive FixedKeyLocation
  | curve (adaptor : CurveAdaptor)
  | point (output : Fin FieldMacToECMac.outputMacCount)
      (coordinate : PointCoordinate) (adaptor : PointAdaptor)
deriving DecidableEq, Fintype

inductive FixedKeySlot
  | hash (slot : Fin 3)
  | pad (slot : Fin 2)
deriving DecidableEq, Fintype

/-- This index selects one public fixed-key permutation. -/
structure FixedKeyIndex where
  location : FixedKeyLocation
  window : Fin BitAdaptor.fixedKeyWindowCount
  slot : FixedKeySlot
deriving DecidableEq, Fintype

def fixedKeyPermutations
    (oracle : PermutationOracle FixedKeyIndex Block)
    (location : FixedKeyLocation) (window : Nat) : BitAdaptor.FixedKeyPermutations := {
  hash := fun slot => oracle.permutation {
    location
    window := ⟨window % BitAdaptor.fixedKeyWindowCount, by
      exact Nat.mod_lt _ (by decide)⟩
    slot := .hash slot
  }
  pad := fun slot => oracle.permutation {
    location
    window := ⟨window % BitAdaptor.fixedKeyWindowCount, by
      exact Nat.mod_lt _ (by decide)⟩
    slot := .pad slot
  }
}

def fixedKeyWindow (oracle : PermutationOracle FixedKeyIndex Block)
    (location : FixedKeyLocation) (window : Nat) : BitAdaptor.FixedKeyOracle :=
  BitAdaptor.fixedKeyOracle (fixedKeyPermutations oracle location window)

def curveOracles (oracle : PermutationOracle FixedKeyIndex Block) :
    CurveMembership.Oracles := {
  y4 := fixedKeyWindow oracle (.curve .y4)
  y6 := fixedKeyWindow oracle (.curve .y6)
  x3 := fixedKeyWindow oracle (.curve .x3)
  x5 := fixedKeyWindow oracle (.curve .x5)
  x7 := fixedKeyWindow oracle (.curve .x7)
}

def biquadraticOracles (oracle : PermutationOracle FixedKeyIndex Block)
    (output : Fin FieldMacToECMac.outputMacCount) (coordinate : PointCoordinate) :
    Biquadratic.Oracles := {
  y6 := fixedKeyWindow oracle (.point output coordinate .y6)
  y8 := fixedKeyWindow oracle (.point output coordinate .y8)
  y10 := fixedKeyWindow oracle (.point output coordinate .y10)
  x7 := fixedKeyWindow oracle (.point output coordinate .x7)
  x9 := fixedKeyWindow oracle (.point output coordinate .x9)
}

def pointOracles (oracle : PermutationOracle FixedKeyIndex Block) :
    FieldMacToECMac.Oracles :=
  Vector.ofFn fun output => {
    x := biquadraticOracles oracle output .x
    y := biquadraticOracles oracle output .y
    z := biquadraticOracles oracle output .z
  }

/-- This table contains the logical `PublicCircuitState`. -/
structure Table where
  curve : CurveMembership.Table
  pointMAC : FieldMacToECMac.Table

def garble (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey : BaseField) (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (fixedKeyOracle : PermutationOracle FixedKeyIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (inputKey : InputMacKey) : Table :=
  let pointInputKey := EncPRF.transformKey encPRFOracle
    (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey
  { curve := CurveMembership.garble bridgeKey curveMask.value curveR1 curveR2
      (curveOracles fixedKeyOracle) inputKey
    pointMAC := FieldMacToECMac.garble
      (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness)
      pointRandomness (pointOracles fixedKeyOracle) pointInputKey }

def evaluate [FieldCertificate]
    (fixedKeyOracle : PermutationOracle FixedKeyIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (table : Table)
    (input : BitInput) (inputMac : InputMac) : Option FieldMacToECMac.Result :=
  let affineInput := input.toAffine
  match decodePoint affineInput with
  | none => none
  | some _ =>
      let bridgeKey := CurveMembership.evaluate (curveOracles fixedKeyOracle)
        table.curve affineInput inputMac
      let pointInputMac := EncPRF.transformMac encPRFOracle
        (EncPRF.whiteningKeys hashOracle bridgeKey) input inputMac
      some (FieldMacToECMac.evaluate table.pointMAC (pointOracles fixedKeyOracle)
        affineInput pointInputMac)

theorem evaluateEncoded [FieldCertificate]
    (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey : BaseField) (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (fixedKeyOracle : PermutationOracle FixedKeyIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (inputKey : InputMacKey)
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point) :
    evaluate fixedKeyOracle encPRFOracle hashOracle
        (garble outputKeys pointRandomness bridgeKey curveMask
          curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle inputKey)
        (BitInput.ofAffine input) (inputKey.encode (BitInput.ofAffine input)) =
      some (FieldMacToECMac.expectedResult
        (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) input) := by
  have inputOnCurve : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
  simp only [evaluate, BitInput.toAffineOfAffine, decoded, garble]
  rw [InputMacKey.encodeOfAffine]
  rw [CurveMembership.evaluateEncodedOnCurve bridgeKey curveMask.value curveR1 curveR2
    (curveOracles fixedKeyOracle) inputKey input inputOnCurve]
  rw [← InputMacKey.encodeOfAffine inputKey input]
  rw [EncPRF.transformEncode]
  rw [InputMacKey.encodeOfAffine]
  rw [FieldMacToECMac.evaluateEncoded]
  exact FieldMacToECMac.rowsForOutputKeysSparse outputKeys pointRandomness

end Kriterion.ArgoMAC.Pipeline
