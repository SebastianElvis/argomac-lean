import Construction

open Kriterion Kriterion.BN254

theorem argoMACGarbleEncodeEvaluateE2E [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (randomness : ArgoMAC.Garbling.Randomness)
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point) :
    let garbled := ArgoMAC.Garbling.garble ArgoMAC.construction scalar randomness
    ArgoMAC.Garbling.evaluate (randomness.fixedKeyOracle,
      randomness.encPRFOracle, randomness.hashOracle) garbled.1
        (ArgoMAC.Garbling.encode garbled.2 (ArgoMAC.BitInput.ofAffine input)) =
      ArgoMAC.Garbling.decodeResult (ArgoMAC.FieldMacToECMac.expectedResult
        (ArgoMAC.FieldMacToECMac.rowsForOutputKeys
          (ArgoMAC.FieldMacToECMac.outputKeys ArgoMAC.construction scalar.value
            randomness.offsets) randomness.pointRandomness) input) := by
  dsimp only
  unfold ArgoMAC.Garbling.evaluate
  change (ArgoMAC.Pipeline.evaluate
      randomness.fixedKeyOracle randomness.encPRFOracle randomness.hashOracle
      (ArgoMAC.Garbling.garble ArgoMAC.construction scalar randomness).1
      (ArgoMAC.BitInput.ofAffine input)
      (randomness.inputMacKey.encode (ArgoMAC.BitInput.ofAffine input))).bind
        ArgoMAC.Garbling.decodeResult = _
  have evaluated := ArgoMAC.Garbling.evaluateEncodeRows ArgoMAC.construction
    { scalar, randomness } input point decoded
  simp only [ArgoMAC.Garbling.encode] at evaluated
  rw [evaluated]
  apply Option.bind_some

#print axioms argoMACGarbleEncodeEvaluateE2E
