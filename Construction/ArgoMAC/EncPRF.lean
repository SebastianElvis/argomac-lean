/-
This file defines the EncPRF label link.
-/

import Construction.ArgoMAC.Input

namespace Kriterion.ArgoMAC.EncPRF

open BN254 Cryptography

inductive Coordinate
  | x
  | y
deriving DecidableEq, Fintype

structure Counter where
  coordinate : Coordinate
  index : Fin coordinateBitCount
  bit : Bool

abbrev PermutationIndex := Coordinate × Fin coordinateBitCount
abbrev HashOracle := BaseField → Block × Block

def whiteningKeys (oracle : HashOracle) (value : BaseField) : WhiteningKeys :=
  let keys := oracle value
  { first := keys.1, second := keys.2 }

/-- This is the fixed-key AES pad. -/
def evenMansourPad (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (counter : Counter) : Block :=
  evenMansour (oracle.permutation (counter.coordinate, counter.index)) keys counter.bit

/-- This is `EncPRF(t, counter) xor label` from the paper. -/
def transformAt (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (counter : Counter) (label : Block) : Block :=
  encrypt (evenMansourPad oracle keys counter) label

theorem transformAtSelfInverse (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (counter : Counter) (label : Block) :
    transformAt oracle keys counter (transformAt oracle keys counter label) = label :=
  decryptEncrypt _ _

def transformCoordinateKey (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : Coordinate) (key : CoordinateMacKey) :
    CoordinateMacKey :=
  Vector.ofFn fun index =>
    let source := key[index.val]
    { falseLabel := transformAt oracle keys { coordinate, index, bit := false }
        source.falseLabel
      trueLabel := transformAt oracle keys { coordinate, index, bit := true }
        source.trueLabel }

/-- This operation transforms all label pairs. -/
def transformKey (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (key : InputMacKey) : InputMacKey := {
  x := transformCoordinateKey oracle keys .x key.x
  y := transformCoordinateKey oracle keys .y key.y
}

def transformCoordinateMac (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : Coordinate)
    (bits : BitVec coordinateBitCount) (mac : CoordinateMac) : CoordinateMac :=
  Vector.ofFn fun index =>
    let bit := bits.getLsb index
    let source := mac[index.val]
    transformAt oracle keys { coordinate, index, bit } source

/-- This operation transforms all selected labels. -/
def transformMac (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (input : BitInput) (mac : InputMac) : InputMac := {
  x := transformCoordinateMac oracle keys .x input.xBits mac.x
  y := transformCoordinateMac oracle keys .y input.yBits mac.y
}

theorem transformCoordinateEncode (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : Coordinate) (key : CoordinateMacKey)
    (bits : BitVec coordinateBitCount) :
    transformCoordinateMac oracle keys coordinate bits (encodeCoordinate key bits) =
      encodeCoordinate (transformCoordinateKey oracle keys coordinate key) bits := by
  apply Vector.ext
  intro index indexValid
  let finiteIndex : Fin coordinateBitCount := ⟨index, indexValid⟩
  change (transformCoordinateMac oracle keys coordinate bits
    (encodeCoordinate key bits))[index] =
      (encodeCoordinate (transformCoordinateKey oracle keys coordinate key) bits)[index]
  simp only [transformCoordinateMac, transformCoordinateKey, encodeCoordinate,
    Vector.getElem_ofFn]
  cases bits.getLsb finiteIndex <;> simp [BitAdaptor.encode]

theorem transformEncode (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (key : InputMacKey) (input : BitInput) :
    transformMac oracle keys input (key.encode input) =
      (transformKey oracle keys key).encode input := by
  apply InputMac.ext
  · exact transformCoordinateEncode oracle keys .x key.x input.xBits
  · exact transformCoordinateEncode oracle keys .y key.y input.yBits

theorem transformCoordinateMacSelfInverse
    (oracle : PermutationOracle PermutationIndex Block) (keys : WhiteningKeys)
    (coordinate : Coordinate) (bits : BitVec coordinateBitCount) (mac : CoordinateMac) :
    transformCoordinateMac oracle keys coordinate bits
        (transformCoordinateMac oracle keys coordinate bits mac) = mac := by
  apply Vector.ext
  intro index indexValid
  let finiteIndex : Fin coordinateBitCount := ⟨index, indexValid⟩
  change (transformCoordinateMac oracle keys coordinate bits
    (transformCoordinateMac oracle keys coordinate bits mac))[index] = mac[index]
  simp only [transformCoordinateMac, Vector.getElem_ofFn]
  exact transformAtSelfInverse oracle keys
    { coordinate, index := finiteIndex, bit := bits.getLsb finiteIndex } mac[index]

/-- Applying the selected-label transform twice restores the input labels. -/
theorem transformMacSelfInverse (oracle : PermutationOracle PermutationIndex Block)
    (keys : WhiteningKeys) (input : BitInput) (mac : InputMac) :
    transformMac oracle keys input (transformMac oracle keys input mac) = mac := by
  apply InputMac.ext
  · exact transformCoordinateMacSelfInverse oracle keys .x input.xBits mac.x
  · exact transformCoordinateMacSelfInverse oracle keys .y input.yBits mac.y

def transform (pad label : Block) : Block := encrypt pad label

def inverse (pad label : Block) : Block := encrypt pad label

theorem inverseTransform (pad label : Block) :
    inverse pad (transform pad label) = label :=
  decryptEncrypt pad label

end Kriterion.ArgoMAC.EncPRF
