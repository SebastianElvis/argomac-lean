/-
This file builds the selected-row programming bridge.
The bridge keeps the public table and changes only selected oracle points.
-/

import Proof.Gate

namespace Kriterion.ArgoMAC.Security

open BN254

/-- One target in the low bit position represents one field value. -/
def lowTarget {count : Nat} (target : BaseField) (index : Fin (count + 1)) : BaseField :=
  if index = 0 then target else 0

theorem fromBits_lowTarget {count : Nat} (target : BaseField) :
    DigitAdaptor.fromBits (lowTarget (count := count) target) = target := by
  have zeroFold : ∀ size, Fin.foldr size (fun _ (value : BaseField) => 2 * value) 0 = 0 := by
    intro size
    induction size with
    | zero => rfl
    | succ size inductionHypothesis =>
        rw [Fin.foldr_succ]
        simp [inductionHypothesis]
  rw [DigitAdaptor.fromBits, Fin.foldr_succ]
  simp [lowTarget, zeroFold count]

/-- This function puts one target in the low coordinate-bit position. -/
def coordinateLowTarget (target : BaseField) : Fin coordinateBitCount → BaseField :=
  lowTarget (count := 253) target

theorem fromBits_coordinateLowTarget (target : BaseField) :
    DigitAdaptor.fromBits (coordinateLowTarget target) = target :=
  fromBits_lowTarget (count := 253) target

/-- This request keeps one curve table and selects one bridge-key result. -/
def CurveGateRequest.retarget (request : CurveGateRequest)
    (input : AffineInput) (target : BaseField) : CurveGateRequest :=
  let residual := target -
    (request.c0 + request.c1 * input.x ^ 3 + request.c2 * input.y ^ 2)
  {
    c0 := request.c0
    c1 := request.c1
    c2 := request.c2
    x3Table := request.x3Table
    x5Table := request.x5Table
    x7Table := request.x7Table
    y4Table := request.y4Table
    y6Table := request.y6Table
    x3Targets := coordinateLowTarget 0
    x5Targets := coordinateLowTarget 0
    x7Targets := coordinateLowTarget residual
    y4Targets := coordinateLowTarget 0
    y6Targets := coordinateLowTarget 0
    x3Quotients := request.x3Quotients
    x5Quotients := request.x5Quotients
    x7Quotients := request.x7Quotients
    y4Quotients := request.y4Quotients
    y6Quotients := request.y6Quotients
    x3Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.x3Quotients index)
    x5Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.x5Quotients index)
    x7Lifts := fun index => goodHashLift ((coordinateLowTarget residual) index)
      (request.x7Quotients index)
    y4Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.y4Quotients index)
    y6Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.y6Quotients index)
  }

@[simp] theorem CurveGateRequest.retarget_table (request : CurveGateRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).table = request.table := by
  rfl

@[simp] theorem CurveGateRequest.retarget_result (request : CurveGateRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).result input = target := by
  simp [CurveGateRequest.retarget, CurveGateRequest.result,
    fromBits_coordinateLowTarget]

/-- This request keeps one X table and selects one coordinate result. -/
def BiquadraticXRequest.retarget (request : BiquadraticXRequest)
    (input : AffineInput) (target : BaseField) : BiquadraticXRequest :=
  let residual := target -
    (request.c0 + request.c1 * input.x + request.c2 * input.y +
      request.c3 * input.x * input.y + request.c5 * input.y ^ 2)
  {
    c0 := request.c0
    c1 := request.c1
    c2 := request.c2
    c3 := request.c3
    c5 := request.c5
    y6Table := request.y6Table
    y8Table := request.y8Table
    y10Table := request.y10Table
    x9Table := request.x9Table
    y6Targets := coordinateLowTarget 0
    y8Targets := coordinateLowTarget 0
    y10Targets := coordinateLowTarget 0
    x9Targets := coordinateLowTarget residual
    y6Quotients := request.y6Quotients
    y8Quotients := request.y8Quotients
    y10Quotients := request.y10Quotients
    x9Quotients := request.x9Quotients
    y6Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.y6Quotients index)
    y8Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.y8Quotients index)
    y10Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.y10Quotients index)
    x9Lifts := fun index => goodHashLift ((coordinateLowTarget residual) index)
      (request.x9Quotients index)
  }

@[simp] theorem BiquadraticXRequest.retarget_table (request : BiquadraticXRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).table = request.table := by
  rfl

@[simp] theorem BiquadraticXRequest.retarget_result (request : BiquadraticXRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).result input = target := by
  simp [BiquadraticXRequest.retarget, BiquadraticXRequest.result,
    fromBits_coordinateLowTarget]

/-- This request keeps one Y table and selects one coordinate result. -/
def BiquadraticYRequest.retarget (request : BiquadraticYRequest)
    (input : AffineInput) (target : BaseField) : BiquadraticYRequest :=
  let residual := target -
    (request.c0 + request.c1 * input.x + request.c4 * input.x ^ 2 +
      request.c5 * input.y ^ 2)
  {
    c0 := request.c0
    c1 := request.c1
    c4 := request.c4
    c5 := request.c5
    y8Table := request.y8Table
    y10Table := request.y10Table
    x7Table := request.x7Table
    x9Table := request.x9Table
    y8Targets := coordinateLowTarget 0
    y10Targets := coordinateLowTarget 0
    x7Targets := coordinateLowTarget 0
    x9Targets := coordinateLowTarget residual
    y8Quotients := request.y8Quotients
    y10Quotients := request.y10Quotients
    x7Quotients := request.x7Quotients
    x9Quotients := request.x9Quotients
    y8Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.y8Quotients index)
    y10Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.y10Quotients index)
    x7Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.x7Quotients index)
    x9Lifts := fun index => goodHashLift ((coordinateLowTarget residual) index)
      (request.x9Quotients index)
  }

@[simp] theorem BiquadraticYRequest.retarget_table (request : BiquadraticYRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).table = request.table := by
  rfl

@[simp] theorem BiquadraticYRequest.retarget_result (request : BiquadraticYRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).result input = target := by
  simp [BiquadraticYRequest.retarget, BiquadraticYRequest.result,
    fromBits_coordinateLowTarget]

/-- This request keeps one Z table and selects one coordinate result. -/
def BiquadraticZRequest.retarget (request : BiquadraticZRequest)
    (input : AffineInput) (target : BaseField) : BiquadraticZRequest :=
  let residual := target -
    (request.c0 + request.c2 * input.y + request.c3 * input.x * input.y +
      request.c4 * input.x ^ 2 + request.c5 * input.y ^ 2)
  {
    c0 := request.c0
    c2 := request.c2
    c3 := request.c3
    c4 := request.c4
    c5 := request.c5
    y6Table := request.y6Table
    y8Table := request.y8Table
    y10Table := request.y10Table
    x7Table := request.x7Table
    x9Table := request.x9Table
    y6Targets := coordinateLowTarget 0
    y8Targets := coordinateLowTarget 0
    y10Targets := coordinateLowTarget 0
    x7Targets := coordinateLowTarget 0
    x9Targets := coordinateLowTarget residual
    y6Quotients := request.y6Quotients
    y8Quotients := request.y8Quotients
    y10Quotients := request.y10Quotients
    x7Quotients := request.x7Quotients
    x9Quotients := request.x9Quotients
    y6Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.y6Quotients index)
    y8Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.y8Quotients index)
    y10Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.y10Quotients index)
    x7Lifts := fun index => goodHashLift ((coordinateLowTarget 0) index)
      (request.x7Quotients index)
    x9Lifts := fun index => goodHashLift ((coordinateLowTarget residual) index)
      (request.x9Quotients index)
  }

@[simp] theorem BiquadraticZRequest.retarget_table (request : BiquadraticZRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).table = request.table := by
  rfl

@[simp] theorem BiquadraticZRequest.retarget_result (request : BiquadraticZRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).result input = target := by
  simp [BiquadraticZRequest.retarget, BiquadraticZRequest.result,
    fromBits_coordinateLowTarget]

/-- This request keeps one row table and selects one homogeneous result. -/
def BiquadraticRowRequest.retarget (request : BiquadraticRowRequest)
    (input : AffineInput) (target : FieldMacToECMac.HomogeneousValue) :
    BiquadraticRowRequest := {
  x := request.x.retarget input target.x
  y := request.y.retarget input target.y
  z := request.z.retarget input target.z
}

@[simp] theorem BiquadraticRowRequest.retarget_table
    (request : BiquadraticRowRequest) (input : AffineInput)
    (target : FieldMacToECMac.HomogeneousValue) :
    (request.retarget input target).table = request.table := by
  rfl

@[simp] theorem BiquadraticRowRequest.retarget_result
    (request : BiquadraticRowRequest) (input : AffineInput)
    (target : FieldMacToECMac.HomogeneousValue) :
    (request.retarget input target).result input = target := by
  simp [BiquadraticRowRequest.retarget, BiquadraticRowRequest.result]

/-- These requests keep all row tables and select all homogeneous results. -/
def retargetPointGateRequests (requests : PointGateRequests)
    (input : AffineInput)
    (targets : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount) : PointGateRequests :=
  Vector.ofFn fun output => (requests.get output).retarget input (targets.get output)

@[simp] theorem retargetPointGateRequests_get (requests : PointGateRequests)
    (input : AffineInput)
    (targets : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount)
    (output : Fin FieldMacToECMac.outputMacCount) :
    (retargetPointGateRequests requests input targets).get output =
      (requests.get output).retarget input (targets.get output) := by
  rw [retargetPointGateRequests, Vector.get_ofFn]

@[simp] theorem retargetPointGateRequests_result_get (requests : PointGateRequests)
    (input : AffineInput)
    (targets : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount)
    (output : Fin FieldMacToECMac.outputMacCount) :
    (pointGateResults (retargetPointGateRequests requests input targets) input).get output =
      targets.get output := by
  rw [pointGateResults, Vector.get_ofFn, retargetPointGateRequests_get,
    BiquadraticRowRequest.retarget_result]

@[simp] theorem retargetPointGateRequests_table_get (requests : PointGateRequests)
    (input : AffineInput)
    (targets : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount)
    (output : Fin FieldMacToECMac.outputMacCount) :
    ((retargetPointGateRequests requests input targets).get output).table =
      (requests.get output).table := by
  rw [retargetPointGateRequests_get, BiquadraticRowRequest.retarget_table]

/-- Collision-free row programming returns the selected homogeneous value. -/
theorem programRetargetedBiquadraticRow_evaluate
    (state : SimulatorState) (output : Fin FieldMacToECMac.outputMacCount)
    (request : BiquadraticRowRequest) (input : AffineInput)
    (inputMac : InputMac) (target : FieldMacToECMac.HomogeneousValue)
    (invariant : SimulatorInvariant state)
    (notBad : (programGateSchedule state
      ((request.retarget input target).schedule output input inputMac)).bad = false) :
    let final := programGateSchedule state
      ((request.retarget input target).schedule output input inputMac)
    Biquadratic.evaluate (Pipeline.biquadraticOracles final.fixedOracle output .x)
        request.table.x input inputMac = target.x ∧
      Biquadratic.evaluate (Pipeline.biquadraticOracles final.fixedOracle output .y)
        request.table.y input inputMac = target.y ∧
      Biquadratic.evaluate (Pipeline.biquadraticOracles final.fixedOracle output .z)
        request.table.z input inputMac = target.z := by
  have evaluated := programBiquadraticRowGateSchedule_evaluate state output input inputMac
    (request.retarget input target).x (request.retarget input target).y
    (request.retarget input target).z invariant notBad
  dsimp only at evaluated ⊢
  rcases evaluated with ⟨xValue, yValue, zValue⟩
  constructor
  · simpa only [BiquadraticRowRequest.retarget,
      BiquadraticXRequest.retarget_table,
      BiquadraticXRequest.retarget_result] using xValue
  · constructor
    · simpa only [BiquadraticRowRequest.retarget,
        BiquadraticYRequest.retarget_table,
        BiquadraticYRequest.retarget_result] using yValue
    · simpa only [BiquadraticRowRequest.retarget,
        BiquadraticZRequest.retarget_table,
        BiquadraticZRequest.retarget_result] using zValue

/-- A satisfied retargeted point schedule returns each selected row value. -/
theorem retargetPointGateSchedule_evaluate_get
    (requests : PointGateRequests) (state : SimulatorState)
    (input : AffineInput) (inputMac : InputMac)
    (targets : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount)
    (satisfied : GateScheduleSatisfied state
      (pointGateSchedule (retargetPointGateRequests requests input targets)
        input inputMac))
    (output : Fin FieldMacToECMac.outputMacCount) :
    (FieldMacToECMac.evaluateHomogeneous
      (pointGateTable (retargetPointGateRequests requests input targets))
      (Pipeline.pointOracles state.fixedOracle) input inputMac).get output =
        targets.get output := by
  have evaluated := pointGateSchedule_evaluate
    (retargetPointGateRequests requests input targets) state input inputMac satisfied
  have selected := congrArg (fun values => values.get output) evaluated
  exact selected.trans (retargetPointGateRequests_result_get requests input targets output)

end Kriterion.ArgoMAC.Security
