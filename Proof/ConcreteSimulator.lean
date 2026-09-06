/-
This file defines the concrete online ArgoMAC simulator.
-/

import Proof.IdealEncoding

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

/-- This state keeps the hidden public sample and its programmable oracles. -/
structure CircuitSimulatorState where
  oracle : SimulatorState
  curve : CurveGateRequest
  points : PointGateRequests
  inputKey : InputMacKey

def CircuitSimulatorState.table (state : CircuitSimulatorState) : Pipeline.Table := {
  curve := state.curve.table
  pointMAC := pointGateTable state.points
}

def CircuitSimulatorState.labels (state : CircuitSimulatorState)
    (input : AffineInput) : Garbling.Labels := {
  input := BitInput.ofAffine input
  inputMac := state.inputKey.encodeAffine input
}

def CircuitSimulatorState.selectedCurve (state : CircuitSimulatorState)
    (input : AffineInput) : CurveGateRequest :=
  state.curve.retarget input 0

def CircuitSimulatorState.selectedPoints [FieldCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Point) :
    PointGateRequests :=
  retargetPointGateRequests state.points input (outputTargets output)

def CircuitSimulatorState.selectedSchedule [FieldCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Point) :
    List GateDirective :=
  linkedPipelineGateSchedule state.oracle (state.selectedCurve input)
    (state.selectedPoints input output) input (state.labels input).inputMac

/-- This operation programs the selected rows for one requested output. -/
def CircuitSimulatorState.programForOutput [FieldCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Point) :
    CircuitSimulatorState :=
  { state with oracle := programGateSchedule state.oracle (state.selectedSchedule input output) }

/-- The ideal handler updates only the programmable oracle state. -/
def circuitSimulatorOracleHandler :
    OracleHandler Garbling.oracleSpec CircuitSimulatorState
  | query, state =>
      let answered := idealOracleHandler query state.oracle
      (answered.1, { state with oracle := answered.2 })

/-- This simulator samples a public state and programs the online selected path. -/
noncomputable def circuitSimulator [FieldCertificate]
    (stateTape : Nat → Garbling.Topology → PMF CircuitSimulatorState) :
    GarbledCircuit.Simulator AffineInput (Option Point) Pipeline.Table Garbling.Labels
      Garbling.Topology CircuitSimulatorState := {
  simulateGarble := fun parameter topology =>
    (stateTape parameter topology).map fun state => (state.table, state)
  simulateEncode := fun state input output =>
    PMF.pure (state.labels input, match output with
      | none => state
      | some point => state.programForOutput input point)
}

end Kriterion.ArgoMAC.Security
