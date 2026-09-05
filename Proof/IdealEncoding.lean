/-
This file builds the simulator output rows.
-/

import Proof.ProgrammingBridge

namespace Kriterion.ArgoMAC.Security

open BN254

/-- This value represents one affine curve point in homogeneous coordinates. -/
def homogeneousOfPoint [FieldCertificate] : Point → FieldMacToECMac.HomogeneousValue
  | .zero => { x := 0, y := 1, z := 0 }
  | .some (x := x) (y := y) _ => { x, y, z := 1 }

theorem decodeHomogeneous_homogeneousOfPoint [FieldCertificate] (point : Point) :
    Garbling.decodeHomogeneous (homogeneousOfPoint point) = some point := by
  induction point with
  | zero =>
      simp [homogeneousOfPoint, Garbling.decodeHomogeneous,
        show (0 : Point) = WeierstrassCurve.Affine.Point.zero from rfl]
  | @some x y valid =>
      have onCurve : OnCurve ({ x, y } : AffineInput) :=
        (equation_iff_onCurve _).mp
          ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
            discriminantNeZero).mpr valid)
      simp only [homogeneousOfPoint, Garbling.decodeHomogeneous, if_false,
        one_ne_zero]
      simp [decodePoint, (validate_eq_true_iff _).mpr onCurve]

/-- The first row contains the output. All other rows contain the identity. -/
def outputTargets [FieldCertificate]
    (point : Point) : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount :=
  ⟨(homogeneousOfPoint point :: List.replicate 90 (homogeneousOfPoint 0)).toArray,
    by simp [FieldMacToECMac.outputMacCount]⟩

theorem outputTargets_toList [FieldCertificate] (point : Point) :
    (outputTargets point).toList = homogeneousOfPoint point ::
      List.replicate 90 (homogeneousOfPoint 0) := by
  simp [outputTargets]

set_option maxRecDepth 10000 in
theorem decodePointMacs_outputTargets [FieldCertificate] (point : Point) :
    Garbling.decodePointMacs (outputTargets point) =
      some (point :: List.replicate 90 0) := by
  rw [Garbling.decodePointMacs, outputTargets_toList]
  simp [decodeHomogeneous_homogeneousOfPoint]

theorem pointHorner_cons_replicate_zero [FieldCertificate] [GroupCertificate]
    (point : Point) (count : Nat) :
    pointHorner radix (point :: List.replicate count 0) = point := by
  have zeroTail : pointHorner radix (List.replicate count 0) = 0 := by
    induction count with
    | zero => rfl
    | succ count inductionHypothesis =>
        simp only [List.replicate_succ, pointHorner]
        rw [inductionHypothesis]
        simp
  simp only [pointHorner, zeroTail]
  simp

/-- The 91 simulator rows decode to the requested output. -/
theorem decodeResult_outputTargets [FieldCertificate] [GroupCertificate]
    (input : AffineInput) (point : Point) :
    Garbling.decodeResult { point := input, pointMacs := outputTargets point } = some point := by
  rw [Garbling.decodeResult, decodePointMacs_outputTargets]
  change some (pointHorner radix (point :: List.replicate 90 0)) = some point
  rw [pointHorner_cons_replicate_zero]

@[simp] theorem retargetPointGateRequests_table
    (requests : PointGateRequests) (input : AffineInput)
    (targets : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount) :
    pointGateTable (retargetPointGateRequests requests input targets) =
      pointGateTable requests := by
  have row (output : Fin FieldMacToECMac.outputMacCount) :=
    retargetPointGateRequests_table_get requests input targets output
  have x : (Vector.ofFn fun output =>
      ((retargetPointGateRequests requests input targets).get output).table.x) =
      Vector.ofFn fun output => (requests.get output).table.x := by
    apply Vector.ext
    intro index inRange
    simpa only [Vector.getElem_ofFn] using congrArg FieldMacToECMac.RowTable.x
      (row ⟨index, inRange⟩)
  have y : (Vector.ofFn fun output =>
      ((retargetPointGateRequests requests input targets).get output).table.y) =
      Vector.ofFn fun output => (requests.get output).table.y := by
    apply Vector.ext
    intro index inRange
    simpa only [Vector.getElem_ofFn] using congrArg FieldMacToECMac.RowTable.y
      (row ⟨index, inRange⟩)
  have z : (Vector.ofFn fun output =>
      ((retargetPointGateRequests requests input targets).get output).table.z) =
      Vector.ofFn fun output => (requests.get output).table.z := by
    apply Vector.ext
    intro index inRange
    simpa only [Vector.getElem_ofFn] using congrArg FieldMacToECMac.RowTable.z
      (row ⟨index, inRange⟩)
  simp only [pointGateTable]
  rw [x, y, z]

theorem retargetedPointGateResults_eq_outputTargets [FieldCertificate]
    (requests : PointGateRequests) (input : AffineInput) (point : Point) :
    pointGateResults
      (retargetPointGateRequests requests input (outputTargets point)) input =
      outputTargets point := by
  apply Vector.ext
  intro index inRange
  exact retargetPointGateRequests_result_get requests input (outputTargets point)
    ⟨index, inRange⟩

/-- Retargeted point rows decode to the requested simulator output. -/
theorem decodeResult_retargetPointGateResults [FieldCertificate] [GroupCertificate]
    (requests : PointGateRequests) (input : AffineInput) (point : Point) :
    Garbling.decodeResult {
      point := input
      pointMacs := pointGateResults
        (retargetPointGateRequests requests input (outputTargets point)) input
    } = some point := by
  rw [retargetedPointGateResults_eq_outputTargets]
  exact decodeResult_outputTargets input point

end Kriterion.ArgoMAC.Security
