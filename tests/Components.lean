import Construction

open Kriterion Kriterion.BN254

theorem generatorIsOnCurve : OnCurve ({ x := 1, y := 2 } : AffineInput) := by
  exact generatorOnCurve

theorem zeroIsNotOnCurve : ¬OnCurve ({ x := 0, y := 0 } : AffineInput) := by
  intro onCurve
  have accepted := (validate_eq_true_iff _).mpr onCurve
  have rejected : validate ({ x := 0, y := 0 } : AffineInput) = false := by decide
  simp [rejected] at accepted

theorem endomorphismRoot : ArgoMAC.omega ^ 3 = 1 ∧ ArgoMAC.omega ≠ 1 :=
  ⟨ArgoMAC.omegaCube, ArgoMAC.omegaNeOne⟩

theorem digitEndomorphismsMatchScalar [FieldCertificate] [GroupCertificate]
    (digit : ArgoMAC.Digit) (point : Point) :
    ArgoMAC.digitEndomorphism digit point = ArgoMAC.digitScalar digit • point :=
  ArgoMAC.digitEndomorphismAction digit point

theorem base7StepCorrect (state : ArgoMAC.DecompositionState) :
    ArgoMAC.stateValue state =
      ArgoMAC.digitScalar (ArgoMAC.nextRound state).digit +
        ArgoMAC.radix * ArgoMAC.stateValue (ArgoMAC.nextState state) :=
  ArgoMAC.nextStateCorrect state

theorem coordinateRowsMatchPointAddition [FieldCertificate] (key input : AffineInput)
    (keyOnCurve : OnCurve key) (inputOnCurve : OnCurve input) (xNe : input.x ≠ key.x) :
    ArgoMAC.Coordinates.evaluate (ArgoMAC.Coordinates.xCoefficients key) input /
        ArgoMAC.Coordinates.evaluate (ArgoMAC.Coordinates.zCoefficients key) input ^ 2 =
          curve.toAffine.addX input.x key.x (curve.toAffine.slope input.x key.x input.y key.y) ∧
      ArgoMAC.Coordinates.evaluate (ArgoMAC.Coordinates.yCoefficients key) input /
        ArgoMAC.Coordinates.evaluate (ArgoMAC.Coordinates.zCoefficients key) input ^ 3 =
          curve.toAffine.addY input.x key.x input.y
            (curve.toAffine.slope input.x key.x input.y key.y) :=
  ⟨ArgoMAC.Coordinates.recoveredX key input keyOnCurve inputOnCurve xNe,
    ArgoMAC.Coordinates.recoveredY key input keyOnCurve inputOnCurve xNe⟩

theorem digitAdaptorCorrect {count : Nat}
    (windows : Nat → ArgoMAC.BitAdaptor.FixedKeyOracle)
    (slope : BaseField) (keys : Vector ArgoMAC.BitAdaptor.Key count)
    (values : Fin count → Bool) :
    ArgoMAC.DigitAdaptor.evaluate windows values
        (ArgoMAC.DigitAdaptor.garble windows slope keys).1
        (ArgoMAC.DigitAdaptor.encode keys values) =
      ArgoMAC.DigitAdaptor.selectedOutputs
        (ArgoMAC.DigitAdaptor.garble windows slope keys).2 values :=
  ArgoMAC.DigitAdaptor.evaluateGarbleEncode windows slope keys values

theorem fixedKeyRowCorrect (permutations : ArgoMAC.BitAdaptor.FixedKeyPermutations)
    (slope : BaseField) (key : ArgoMAC.BitAdaptor.Key) (value : Bool) :
    ArgoMAC.BitAdaptor.evaluate (ArgoMAC.BitAdaptor.fixedKeyOracle permutations)
        (ArgoMAC.BitAdaptor.garble
          (ArgoMAC.BitAdaptor.fixedKeyOracle permutations) slope key).1
        value (ArgoMAC.BitAdaptor.encode key value) =
      (ArgoMAC.BitAdaptor.garble
        (ArgoMAC.BitAdaptor.fixedKeyOracle permutations) slope key).2.encode value :=
  ArgoMAC.BitAdaptor.evaluateEncode
    (ArgoMAC.BitAdaptor.fixedKeyOracle permutations) slope key value

theorem encPRFRoundTrip (pad label : Cryptography.Block) :
    ArgoMAC.EncPRF.inverse pad (ArgoMAC.EncPRF.transform pad label) = label :=
  ArgoMAC.EncPRF.inverseTransform pad label

theorem fixedOracleRoundTrip (randomness : ArgoMAC.Garbling.Randomness)
    (index : ArgoMAC.Pipeline.FixedKeyIndex) (input : Cryptography.Block) :
    let forward := ArgoMAC.Garbling.oracleHandler (.fixedForward index input) randomness
    ArgoMAC.Garbling.oracleHandler (.fixedInverse index forward.1) forward.2 =
      (input, randomness) := by
  simp [ArgoMAC.Garbling.oracleHandler]

theorem encPRFTransformsSelectedLabels
    (oracle : Cryptography.PermutationOracle ArgoMAC.EncPRF.PermutationIndex
      Cryptography.Block)
    (keys : Cryptography.WhiteningKeys) (inputKey : ArgoMAC.InputMacKey)
    (input : ArgoMAC.BitInput) :
    ArgoMAC.EncPRF.transformMac oracle keys input (inputKey.encode input) =
      (ArgoMAC.EncPRF.transformKey oracle keys inputKey).encode input :=
  ArgoMAC.EncPRF.transformEncode oracle keys inputKey input

theorem curveMembershipReleasesBridge
    (bridgeKey mask r1 r2 : BaseField) (oracles : ArgoMAC.CurveMembership.Oracles)
    (inputKey : ArgoMAC.InputMacKey) (input : AffineInput) (inputOnCurve : OnCurve input) :
    ArgoMAC.CurveMembership.evaluate oracles
      (ArgoMAC.CurveMembership.garble bridgeKey mask r1 r2 oracles inputKey)
      input (inputKey.encodeAffine input) = bridgeKey :=
  ArgoMAC.CurveMembership.evaluateEncodedOnCurve
    bridgeKey mask r1 r2 oracles inputKey input inputOnCurve

theorem biquadraticXCorrect
    (c0 c1 c2 c4 : BaseField) (randomness : ArgoMAC.Biquadratic.XRandomness)
    (oracles : ArgoMAC.Biquadratic.Oracles) (inputKey : ArgoMAC.InputMacKey)
    (input : AffineInput) :
    ArgoMAC.Biquadratic.evaluate oracles
        (ArgoMAC.Biquadratic.garbleX c0 c1 c2 c4 randomness oracles inputKey)
        input (inputKey.encodeAffine input) =
      c0 + c1 * input.x + c2 * input.y + c4 * input.x ^ 2 :=
  ArgoMAC.Biquadratic.evaluateEncodedX c0 c1 c2 c4 randomness oracles inputKey input

theorem fieldLayerMatchesRows [FieldCertificate]
    (rows : ArgoMAC.FieldMacToECMac.Rows)
    (randomness : ArgoMAC.FieldMacToECMac.Randomness)
    (oracles : ArgoMAC.FieldMacToECMac.Oracles)
    (inputKey : ArgoMAC.InputMacKey) (input : AffineInput)
    (sparse : ∀ index, ArgoMAC.FieldMacToECMac.SparseRow (rows.get index)) :
    ArgoMAC.FieldMacToECMac.evaluate
        (ArgoMAC.FieldMacToECMac.garble rows randomness oracles inputKey)
        oracles input (inputKey.encodeAffine input) =
      ArgoMAC.FieldMacToECMac.expectedResult rows input :=
  ArgoMAC.FieldMacToECMac.evaluateEncoded
    rows randomness oracles inputKey input sparse

theorem pipelineMatchesRows [FieldCertificate]
    (outputKeys : ArgoMAC.FieldMacToECMac.OutputKeys)
    (pointRandomness : ArgoMAC.FieldMacToECMac.Randomness)
    (bridgeKey : BaseField) (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (fixedKeyOracle : Cryptography.PermutationOracle
      ArgoMAC.Pipeline.FixedKeyIndex Cryptography.Block)
    (encPRFOracle : Cryptography.PermutationOracle
      ArgoMAC.EncPRF.PermutationIndex Cryptography.Block)
    (hashOracle : ArgoMAC.EncPRF.HashOracle)
    (inputKey : ArgoMAC.InputMacKey) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    ArgoMAC.Pipeline.evaluate fixedKeyOracle encPRFOracle hashOracle
        (ArgoMAC.Pipeline.garble outputKeys pointRandomness
          bridgeKey curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle inputKey)
        (ArgoMAC.BitInput.ofAffine input)
        (inputKey.encode (ArgoMAC.BitInput.ofAffine input)) =
      some (ArgoMAC.FieldMacToECMac.expectedResult
        (ArgoMAC.FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) input) :=
  ArgoMAC.Pipeline.evaluateEncoded outputKeys pointRandomness
    bridgeKey curveMask curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle inputKey
    input point decoded

theorem fixedKeyCounts :
    ArgoMAC.Pipeline.fixedKeyWindowCount = 2472 ∧
      ArgoMAC.Pipeline.permutationCount = 12360 ∧
      ArgoMAC.Pipeline.hashPermutationCount = 7416 ∧
      ArgoMAC.Pipeline.padPermutationCount = 4944 :=
  ⟨ArgoMAC.Pipeline.fixedKeyWindowCountValue,
    ArgoMAC.Pipeline.permutationCountValue,
    ArgoMAC.Pipeline.hashPermutationCountValue,
    ArgoMAC.Pipeline.padPermutationCountValue⟩

theorem fixedKeyWindowLoads :
    ArgoMAC.BitAdaptor.fixedKeyWindowLoad ⟨0, by decide⟩ = 91 ∧
      ArgoMAC.BitAdaptor.fixedKeyWindowLoad ⟨1, by decide⟩ = 91 ∧
        ArgoMAC.BitAdaptor.fixedKeyWindowLoad ⟨2, by decide⟩ = 72 :=
  ArgoMAC.BitAdaptor.fixedKeyWindowLoads

#print axioms generatorIsOnCurve
#print axioms zeroIsNotOnCurve
#print axioms endomorphismRoot
#print axioms digitEndomorphismsMatchScalar
#print axioms base7StepCorrect
#print axioms coordinateRowsMatchPointAddition
#print axioms digitAdaptorCorrect
#print axioms fixedKeyRowCorrect
#print axioms encPRFRoundTrip
#print axioms encPRFTransformsSelectedLabels
#print axioms curveMembershipReleasesBridge
#print axioms biquadraticXCorrect
#print axioms fieldLayerMatchesRows
#print axioms pipelineMatchesRows
#print axioms fixedKeyCounts
#print axioms fixedKeyWindowLoads
