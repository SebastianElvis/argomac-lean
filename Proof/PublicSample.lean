/-
This file defines the scalar-independent public simulator sample.
-/

import Proof.ConcreteSimulator
import Proof.Distribution

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

local instance publicVectorFintype {Value : Type} {count : Nat} [Fintype Value] :
    Fintype (Vector Value count) :=
  Fintype.ofEquiv (Fin count → Value) vectorFunctionEquiv

local instance ciphertextFintype : Fintype BitAdaptor.Ciphertext :=
  Fintype.ofEquiv (Fin (2 ^ 256)) BitVec.equivFin.symm.toEquiv

local instance bitAdaptorTableFintype : Fintype BitAdaptor.Table :=
  Fintype.ofInjective BitAdaptor.Table.trueRow (by
    intro first second equal
    cases first
    cases second
    simp_all)

local instance publicBitAdaptorKeyFintype : Fintype BitAdaptor.Key :=
  Fintype.ofInjective (fun key => (key.falseLabel, key.trueLabel)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

local instance publicInputMacKeyFintype : Fintype InputMacKey :=
  Fintype.ofInjective (fun key => (key.x, key.y)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

/-- This sample contains one scalar-independent curve table. -/
structure CurvePublicSample where
  coefficients : Fin 3 → BaseField
  tables : Fin 5 → Vector BitAdaptor.Table coordinateBitCount
  quotients : Fin 5 → Fin coordinateBitCount → HashLiftQuotient
deriving Fintype

def CurvePublicSample.request (sample : CurvePublicSample) : CurveGateRequest := {
  c0 := sample.coefficients 0
  c1 := sample.coefficients 1
  c2 := sample.coefficients 2
  x3Table := sample.tables 0
  x5Table := sample.tables 1
  x7Table := sample.tables 2
  y4Table := sample.tables 3
  y6Table := sample.tables 4
  x3Targets := fun _ => 0
  x5Targets := fun _ => 0
  x7Targets := fun _ => 0
  y4Targets := fun _ => 0
  y6Targets := fun _ => 0
  x3Quotients := sample.quotients 0
  x5Quotients := sample.quotients 1
  x7Quotients := sample.quotients 2
  y4Quotients := sample.quotients 3
  y6Quotients := sample.quotients 4
  x3Lifts := fun index => goodHashLift 0 (sample.quotients 0 index)
  x5Lifts := fun index => goodHashLift 0 (sample.quotients 1 index)
  x7Lifts := fun index => goodHashLift 0 (sample.quotients 2 index)
  y4Lifts := fun index => goodHashLift 0 (sample.quotients 3 index)
  y6Lifts := fun index => goodHashLift 0 (sample.quotients 4 index)
}

/-- This sample contains one scalar-independent RCB X table. -/
structure XPublicSample where
  coefficients : Fin 5 → BaseField
  tables : Fin 4 → Vector BitAdaptor.Table coordinateBitCount
  quotients : Fin 4 → Fin coordinateBitCount → HashLiftQuotient
deriving Fintype

def XPublicSample.request (sample : XPublicSample) : BiquadraticXRequest := {
  c0 := sample.coefficients 0
  c1 := sample.coefficients 1
  c2 := sample.coefficients 2
  c3 := sample.coefficients 3
  c5 := sample.coefficients 4
  y6Table := sample.tables 0
  y8Table := sample.tables 1
  y10Table := sample.tables 2
  x9Table := sample.tables 3
  y6Targets := fun _ => 0
  y8Targets := fun _ => 0
  y10Targets := fun _ => 0
  x9Targets := fun _ => 0
  y6Quotients := sample.quotients 0
  y8Quotients := sample.quotients 1
  y10Quotients := sample.quotients 2
  x9Quotients := sample.quotients 3
  y6Lifts := fun index => goodHashLift 0 (sample.quotients 0 index)
  y8Lifts := fun index => goodHashLift 0 (sample.quotients 1 index)
  y10Lifts := fun index => goodHashLift 0 (sample.quotients 2 index)
  x9Lifts := fun index => goodHashLift 0 (sample.quotients 3 index)
}

/-- This sample contains one scalar-independent RCB Y table. -/
structure YPublicSample where
  coefficients : Fin 4 → BaseField
  tables : Fin 4 → Vector BitAdaptor.Table coordinateBitCount
  quotients : Fin 4 → Fin coordinateBitCount → HashLiftQuotient
deriving Fintype

def YPublicSample.request (sample : YPublicSample) : BiquadraticYRequest := {
  c0 := sample.coefficients 0
  c1 := sample.coefficients 1
  c4 := sample.coefficients 2
  c5 := sample.coefficients 3
  y8Table := sample.tables 0
  y10Table := sample.tables 1
  x7Table := sample.tables 2
  x9Table := sample.tables 3
  y8Targets := fun _ => 0
  y10Targets := fun _ => 0
  x7Targets := fun _ => 0
  x9Targets := fun _ => 0
  y8Quotients := sample.quotients 0
  y10Quotients := sample.quotients 1
  x7Quotients := sample.quotients 2
  x9Quotients := sample.quotients 3
  y8Lifts := fun index => goodHashLift 0 (sample.quotients 0 index)
  y10Lifts := fun index => goodHashLift 0 (sample.quotients 1 index)
  x7Lifts := fun index => goodHashLift 0 (sample.quotients 2 index)
  x9Lifts := fun index => goodHashLift 0 (sample.quotients 3 index)
}

/-- This sample contains one scalar-independent RCB Z table. -/
structure ZPublicSample where
  coefficients : Fin 5 → BaseField
  tables : Fin 5 → Vector BitAdaptor.Table coordinateBitCount
  quotients : Fin 5 → Fin coordinateBitCount → HashLiftQuotient
deriving Fintype

def ZPublicSample.request (sample : ZPublicSample) : BiquadraticZRequest := {
  c0 := sample.coefficients 0
  c2 := sample.coefficients 1
  c3 := sample.coefficients 2
  c4 := sample.coefficients 3
  c5 := sample.coefficients 4
  y6Table := sample.tables 0
  y8Table := sample.tables 1
  y10Table := sample.tables 2
  x7Table := sample.tables 3
  x9Table := sample.tables 4
  y6Targets := fun _ => 0
  y8Targets := fun _ => 0
  y10Targets := fun _ => 0
  x7Targets := fun _ => 0
  x9Targets := fun _ => 0
  y6Quotients := sample.quotients 0
  y8Quotients := sample.quotients 1
  y10Quotients := sample.quotients 2
  x7Quotients := sample.quotients 3
  x9Quotients := sample.quotients 4
  y6Lifts := fun index => goodHashLift 0 (sample.quotients 0 index)
  y8Lifts := fun index => goodHashLift 0 (sample.quotients 1 index)
  y10Lifts := fun index => goodHashLift 0 (sample.quotients 2 index)
  x7Lifts := fun index => goodHashLift 0 (sample.quotients 3 index)
  x9Lifts := fun index => goodHashLift 0 (sample.quotients 4 index)
}

/-- This sample groups the three public tables of one complete RCB row. -/
structure RowPublicSample where
  x : XPublicSample
  y : YPublicSample
  z : ZPublicSample
deriving Fintype

def RowPublicSample.request (sample : RowPublicSample) : BiquadraticRowRequest := {
  x := sample.x.request
  y := sample.y.request
  z := sample.z.request
}

/-- This sample contains every public coefficient and ciphertext row. -/
structure PublicSample where
  curve : CurvePublicSample
  points : Vector RowPublicSample FieldMacToECMac.outputMacCount
deriving Fintype

def PublicSample.curveRequest (sample : PublicSample) : CurveGateRequest :=
  sample.curve.request

def PublicSample.pointRequests (sample : PublicSample) : PointGateRequests :=
  sample.points.map RowPublicSample.request

/-- This sample contains the three independent public oracle families. -/
structure SimulatorOracleCoin where
  fixedOracle : PermutationOracle Pipeline.FixedKeyIndex Block
  encOracle : PermutationOracle EncPRF.PermutationIndex Block
  hashOracle : EncPRF.HashOracle
deriving Fintype

/-- This is the complete scalar-independent offline simulator coin. -/
structure SimulatorCoin where
  tableSample : PublicSample
  oracles : SimulatorOracleCoin
  inputKey : InputMacKey
deriving Fintype

def SimulatorCoin.state (coin : SimulatorCoin) : CircuitSimulatorState := {
  oracle := {
    fixedOracle := coin.oracles.fixedOracle
    encOracle := coin.oracles.encOracle
    hashOracle := coin.oracles.hashOracle
    fixedTranscript := []
    encTranscript := []
    hashTranscript := []
    commitments := []
    linking := none
    bad := false
  }
  curve := coin.tableSample.curveRequest
  points := coin.tableSample.pointRequests
  inputKey := coin.inputKey
}

/-- This public table is a witness for the finite simulator sample. -/
def defaultBitAdaptorTable : BitAdaptor.Table := {
  trueRow := 0
}

/-- This RCB row is a witness for the finite simulator sample. -/
def defaultRowPublicSample : RowPublicSample := {
  x := {
    coefficients := fun _ => 0
    tables := fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable
    quotients := fun _ _ => defaultHashLiftQuotient
  }
  y := {
    coefficients := fun _ => 0
    tables := fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable
    quotients := fun _ _ => defaultHashLiftQuotient
  }
  z := {
    coefficients := fun _ => 0
    tables := fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable
    quotients := fun _ _ => defaultHashLiftQuotient
  }
}

/-- This value is an explicit witness for the complete simulator coin. -/
def defaultSimulatorCoin : SimulatorCoin := {
  tableSample := {
    curve := {
      coefficients := fun _ => 0
      tables := fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable
      quotients := fun _ _ => defaultHashLiftQuotient
    }
    points := Vector.replicate FieldMacToECMac.outputMacCount defaultRowPublicSample
  }
  oracles := {
    fixedOracle := ⟨fun _ => Equiv.refl Block⟩
    encOracle := ⟨fun _ => Equiv.refl Block⟩
    hashOracle := fun _ => (0, 0)
  }
  inputKey := {
    x := Vector.replicate coordinateBitCount { falseLabel := 0, trueLabel := 0 }
    y := Vector.replicate coordinateBitCount { falseLabel := 0, trueLabel := 0 }
  }
}

/-- The offline simulator samples its complete scalar-independent coin uniformly. -/
def simulatorStateTape
    (_parameter : Nat) (_topology : Garbling.Topology) : PMF CircuitSimulatorState :=
  letI : Nonempty SimulatorCoin := ⟨defaultSimulatorCoin⟩
  (PMF.uniformOfFintype SimulatorCoin).map SimulatorCoin.state

/-- This value connects the finite offline sample to the online simulator. -/
noncomputable def concreteCircuitSimulator [FieldCertificate] :=
  circuitSimulator simulatorStateTape

end

end Kriterion.ArgoMAC.Security
