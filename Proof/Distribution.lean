/-
This file defines the complete uniform ArgoMAC security tape.
-/

import Proof.ProgrammingBridge

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-- Finite vectors are equivalent to finite-index functions. -/
def vectorFunctionEquiv {Value : Type} {count : Nat} :
    (Fin count → Value) ≃ Vector Value count where
  toFun := Vector.ofFn
  invFun := fun values index => values.get index
  left_inv function := by
    funext index
    change (Vector.ofFn function).get index = function index
    rw [Vector.get_ofFn]
  right_inv values := by
    apply Vector.ext
    intro index inRange
    simp only [Vector.getElem_ofFn]
    rfl

local instance vectorFintype {Value : Type} {count : Nat} [Fintype Value] :
    Fintype (Vector Value count) :=
  Fintype.ofEquiv (Fin count → Value) vectorFunctionEquiv

local instance nonZeroBaseFintype : Fintype NonZeroBase :=
  Fintype.ofInjective NonZeroBase.value (by
    intro first second equal
    cases first
    cases second
    simp_all)

local instance affineInputFintype : Fintype AffineInput :=
  Fintype.ofInjective (fun input => (input.x, input.y)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

local instance bitAdaptorKeyFintype : Fintype BitAdaptor.Key :=
  Fintype.ofInjective (fun key => (key.falseLabel, key.trueLabel)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

local instance inputMacKeyFintype : Fintype InputMacKey :=
  Fintype.ofInjective (fun key => (key.x, key.y)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

local instance xRandomnessFintype : Fintype Biquadratic.XRandomness :=
  Fintype.ofInjective (fun value => (value.r1, value.r2, value.r3, value.r5)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

local instance yRandomnessFintype : Fintype Biquadratic.YRandomness :=
  Fintype.ofInjective (fun value => (value.r1, value.r4, value.r5)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

local instance zRandomnessFintype : Fintype Biquadratic.ZRandomness :=
  Fintype.ofInjective
    (fun value => (value.r2, value.r3, value.r4, value.r5)) (by
      intro first second equal
      cases first
      cases second
      simp_all)

local instance rowRandomnessFintype : Fintype FieldMacToECMac.RowRandomness :=
  Fintype.ofInjective (fun value => (value.rho, value.x, value.y, value.z)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

local instance affineOffsetFintype : Fintype FieldMacToECMac.AffineOffset :=
  Fintype.ofInjective FieldMacToECMac.AffineOffset.coordinates (by
    intro first second equal
    cases first
    cases second
    simp_all)

local instance successfulOffsetsFintype :
    Fintype FieldMacToECMac.SuccessfulOffsets :=
  Fintype.ofInjective (fun value => (value.first, value.free)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

/-- This type contains the point data in one garbling tape. -/
structure GarblingPointData where
  offsets : FieldMacToECMac.SuccessfulOffsets
  pointRandomness : FieldMacToECMac.Randomness
deriving Fintype

/-- This type contains the field data in one garbling tape. -/
structure GarblingFieldData where
  bridgeKey : BaseField
  curveMask : NonZeroBase
  curveR1 : BaseField
  curveR2 : BaseField
deriving Fintype

/-- This type contains the algebraic data in one garbling tape. -/
structure GarblingAlgebraicData where
  point : GarblingPointData
  field : GarblingFieldData
deriving Fintype

/-- This type contains the oracle and label data in one garbling tape. -/
structure GarblingOracleData where
  fixedKeyOracle : PermutationOracle Pipeline.FixedKeyIndex Block
  inputMacKey : InputMacKey
  encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block
  hashOracle : EncPRF.HashOracle
deriving Fintype

/-- This type removes the proof-only field from one garbling tape. -/
structure GarblingRandomnessData where
  algebraic : GarblingAlgebraicData
  oracles : GarblingOracleData
deriving Fintype

def Garbling.Randomness.data (randomness : Garbling.Randomness) :
    GarblingRandomnessData := {
  algebraic := {
    point := {
      offsets := randomness.offsets
      pointRandomness := randomness.pointRandomness
    }
    field := {
      bridgeKey := randomness.bridgeKey
      curveMask := randomness.curveMask
      curveR1 := randomness.curveR1
      curveR2 := randomness.curveR2
    }
  }
  oracles := {
    fixedKeyOracle := randomness.fixedKeyOracle
    inputMacKey := randomness.inputMacKey
    encPRFOracle := randomness.encPRFOracle
    hashOracle := randomness.hashOracle
  }
}

theorem Garbling.Randomness.data_injective :
    Function.Injective Garbling.Randomness.data := by
  intro first second equal
  cases first
  cases second
  cases equal
  rfl

/-- This type contains every garbling value except the fixed-key oracle. -/
structure GarblingRandomnessRest where
  algebraic : GarblingAlgebraicData
  offsetsClamped : ∀ [FieldCertificate] [GroupCertificate],
    algebraic.point.offsets.IsClamped
  inputMacKey : InputMacKey
  encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block
  hashOracle : EncPRF.HashOracle

noncomputable def GarblingRandomnessRest.data
    (rest : GarblingRandomnessRest) : GarblingRandomnessData := {
  algebraic := rest.algebraic
  oracles := {
    fixedKeyOracle := Classical.choice inferInstance
    inputMacKey := rest.inputMacKey
    encPRFOracle := rest.encPRFOracle
    hashOracle := rest.hashOracle
  }
}

theorem GarblingRandomnessRest.data_injective :
    Function.Injective GarblingRandomnessRest.data := by
  intro first second equal
  cases first
  cases second
  cases equal
  rfl

noncomputable instance garblingRandomnessRestFintype :
    Fintype GarblingRandomnessRest :=
  Fintype.ofInjective GarblingRandomnessRest.data
    GarblingRandomnessRest.data_injective

def garblingRandomnessRest (randomness : Garbling.Randomness) :
    GarblingRandomnessRest := {
  algebraic := {
    point := {
      offsets := randomness.offsets
      pointRandomness := randomness.pointRandomness
    }
    field := {
      bridgeKey := randomness.bridgeKey
      curveMask := randomness.curveMask
      curveR1 := randomness.curveR1
      curveR2 := randomness.curveR2
    }
  }
  offsetsClamped := randomness.offsetsClamped
  inputMacKey := randomness.inputMacKey
  encPRFOracle := randomness.encPRFOracle
  hashOracle := randomness.hashOracle
}

/-- A garbling tape is one fixed-key oracle and all remaining values. -/
def garblingRandomnessFixedOracleEquiv :
    Garbling.Randomness ≃
      PermutationOracle Pipeline.FixedKeyIndex Block × GarblingRandomnessRest where
  toFun randomness := (randomness.fixedKeyOracle, garblingRandomnessRest randomness)
  invFun sample := {
    offsets := sample.2.algebraic.point.offsets
    offsetsClamped := sample.2.offsetsClamped
    pointRandomness := sample.2.algebraic.point.pointRandomness
    bridgeKey := sample.2.algebraic.field.bridgeKey
    curveMask := sample.2.algebraic.field.curveMask
    curveR1 := sample.2.algebraic.field.curveR1
    curveR2 := sample.2.algebraic.field.curveR2
    fixedKeyOracle := sample.1
    inputMacKey := sample.2.inputMacKey
    encPRFOracle := sample.2.encPRFOracle
    hashOracle := sample.2.hashOracle
  }
  left_inv randomness := by
    cases randomness
    rfl
  right_inv sample := by
    rcases sample with ⟨oracle, rest⟩
    cases rest
    rfl

noncomputable instance garblingRandomnessFintype : Fintype Garbling.Randomness :=
  Fintype.ofInjective Garbling.Randomness.data Garbling.Randomness.data_injective

/-- The security tape samples every complete ArgoMAC tape uniformly. -/
def randomTape (witness : Garbling.Randomness) (_parameter : Nat) :
    PMF Garbling.Randomness :=
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  PMF.uniformOfFintype Garbling.Randomness

theorem randomTape_fullSupport (witness randomness : Garbling.Randomness)
    (parameter : Nat) :
    randomness ∈ (randomTape witness parameter).support := by
  simp [randomTape]

end

end Kriterion.ArgoMAC.Security
