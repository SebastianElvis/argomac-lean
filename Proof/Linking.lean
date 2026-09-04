/-
This file proves the non-black-box encoding-key link.
The paper states the link in `eq:linking_encoding_keys` in `gc_optimizations.tex`.
The paper source is https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/gc_optimizations.tex.
-/

import Construction.Garbling

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

/-- This function is the exact encoding-key link in the construction. -/
def linkedInputKey
    (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (bridgeKey : BaseField)
    (inputKey : InputMacKey) : InputMacKey :=
  EncPRF.transformKey oracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey

/-- The point layer uses the linked input key. -/
theorem pointLayerUsesLinkedInputKey
    (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey : BaseField) (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (fixedKeyOracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (inputKey : InputMacKey) :
    (Pipeline.garble outputKeys pointRandomness bridgeKey curveMask curveR1 curveR2
      fixedKeyOracle encPRFOracle hashOracle inputKey).pointMAC =
      FieldMacToECMac.garble
        (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness)
        pointRandomness (Pipeline.pointOracles fixedKeyOracle)
        (linkedInputKey encPRFOracle hashOracle bridgeKey inputKey) := by
  rfl

end Kriterion.ArgoMAC.Security
