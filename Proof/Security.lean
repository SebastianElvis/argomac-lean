/-
This file defines the hybrid chain from the active BaBe paper.
The paper proof is in `gc_rpm_proof.tex` and `gc_optimizations.tex`.
The paper source is https://github.com/babylonlabs-io/BaBe.latex/tree/e2dcf4d540b2708e13cd21090df759051119a116.
-/

import Construction.Garbling
import Cryptography.Assumptions

namespace Kriterion.ArgoMAC.Security

open GarbledCircuit
open Cryptography
open Cryptography.Assumptions

universe uKey uCounter uCTPRFIndex uEncPRFIndex uHashInput uCPAAux

/-- These are the standard assumptions in `thm:gc_opt_final`. -/
abbrev BaBeAssumptions
    (CTPRFIndex : Type uCTPRFIndex) (EncPRFIndex : Type uEncPRFIndex)
    (HashInput : Type uHashInput)
    (Key : Type uKey) (Counter : Type uCounter)
    (CPAAux : Type uCPAAux)
    [Fintype CTPRFIndex] [Fintype EncPRFIndex] [Fintype HashInput]
    [DecidableEq HashInput] :=
  StandardAssumptions CTPRFIndex EncPRFIndex Block HashInput (Block × Block)
    Key Block Block Counter CPAAux

/-- The fixed AES block size in the paper is 128 bits. -/
def blockBits : Nat := 128

/-- The block type has exactly 2^128 values. -/
theorem blockCard : Fintype.card Block = 2 ^ blockBits := by
  calc
    Fintype.card Block = Fintype.card (Fin (2 ^ 128)) :=
      Fintype.card_congr BitVec.equivFin.toEquiv
    _ = 2 ^ blockBits := by simp [blockBits]

/-- One value has exact mass 2^-128 under the uniform block tape. -/
theorem uniformBlockMass (value : Block) :
    PMF.uniformOfFintype Block value =
      Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal) := by
  rw [PMF.uniformOfFintype_apply, blockCard]

/-- Two forbidden block values have this union-bound mass. -/
theorem uniformBlockTwoPointUnionBound (first second : Block) :
    PMF.uniformOfFintype Block first + PMF.uniformOfFintype Block second =
      2 * Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal) := by
  rw [uniformBlockMass, uniformBlockMass]
  ring

/-- A finite forbidden set has its exact cardinality divided by 2^128 as mass. -/
theorem uniformBlockFinsetMass (forbidden : Finset Block) :
    (PMF.uniformOfFintype Block).toOuterMeasure (forbidden : Set Block) =
      (forbidden.card : ENNReal) * Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, blockCard]
  simp [div_eq_mul_inv]

/-- A set of at most `count` forbidden blocks has at most `count / 2^128` mass. -/
theorem uniformBlockFinsetMass_le (forbidden : Finset Block) (count : Nat)
    (cardBound : forbidden.card ≤ count) :
    (PMF.uniformOfFintype Block).toOuterMeasure (forbidden : Set Block) ≤
      (count : ENNReal) * Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal) := by
  rw [uniformBlockFinsetMass]
  exact mul_le_mul_right' (by exact_mod_cast cardBound) _

/-- The event for either of two forbidden blocks has at most `2 / 2^128` mass. -/
theorem uniformBlockTwoPointEvent_le (first second : Block) :
    (PMF.uniformOfFintype Block).toOuterMeasure
        ({first, second} : Finset Block) ≤
      2 * Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal) := by
  apply uniformBlockFinsetMass_le _ 2
  exact Finset.card_le_two

/-- The paper base-`(2 - omega)` case uses 92 active inputs per bucket. -/
def paperActiveInputsPerBucket : Nat := 92

/-- The paper proof uses 6858 independent permutation buckets. -/
def paperBucketCount : Nat := 6858

noncomputable def paperCTPRFError (securityParameter oracleQueries : Nat) : ℝ :=
  ((3 * paperBucketCount * paperActiveInputsPerBucket ^ 2 +
      4 * paperActiveInputsPerBucket * oracleQueries : Nat) : ℝ) /
    (2 : ℝ) ^ securityParameter

/-- This is the paper bound at the 128-bit AES block size. -/
noncomputable def paperConcreteCTPRFError (oracleQueries : Nat) : ℝ :=
  paperCTPRFError blockBits oracleQueries

/-- Every permutation query costs at least one unit of work. -/
def permutationWork (oracleQueries : Nat) : Nat := max oracleQueries 1

/-- The paper CTPRF bound gives at least 100 bits of concrete security. -/
theorem paperConcreteCTPRFHas100Bits :
    ConcreteBound 100 permutationWork paperConcreteCTPRFError := by
  intro queries
  have countBound :
      3 * paperBucketCount * paperActiveInputsPerBucket ^ 2 +
          4 * paperActiveInputsPerBucket * queries ≤ permutationWork queries * 2 ^ 28 := by
    cases queries with
    | zero => norm_num [paperBucketCount, paperActiveInputsPerBucket, permutationWork]
    | succ queries =>
        rw [permutationWork, Nat.max_eq_left (by omega : 1 ≤ queries + 1)]
        norm_num [paperBucketCount, paperActiveInputsPerBucket]
        omega
  rw [WorkPerAdvantage]
  change (((3 * paperBucketCount * paperActiveInputsPerBucket ^ 2 +
      4 * paperActiveInputsPerBucket * queries : Nat) : ℝ) /
      (2 : ℝ) ^ 128) * (2 : ℝ) ^ 100 ≤ ((permutationWork queries : Nat) : ℝ)
  calc
    (((3 * paperBucketCount * paperActiveInputsPerBucket ^ 2 +
        4 * paperActiveInputsPerBucket * queries : Nat) : ℝ) /
        (2 : ℝ) ^ 128) * (2 : ℝ) ^ 100 =
      ((3 * paperBucketCount * paperActiveInputsPerBucket ^ 2 +
        4 * paperActiveInputsPerBucket * queries : Nat) : ℝ) / (2 : ℝ) ^ 28 := by
        norm_num [div_eq_mul_inv]
        ring
    _ ≤ ((permutationWork queries : Nat) : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 28)).2
      norm_num
      exact_mod_cast countBound

/-- This formula applies the paper shape to all full-schedule fixed-key permutations. -/
noncomputable def fullScheduleTransferredCTPRFError (oracleQueries : Nat) : ℝ :=
  ((3 * Pipeline.permutationCount * BitAdaptor.fixedKeyMaxUsesPerBucket ^ 2 +
      4 * BitAdaptor.fixedKeyMaxUsesPerBucket * oracleQueries : Nat) : ℝ) /
    (2 : ℝ) ^ blockBits

/-- The direct transfer of the paper formula gives less than 100 bits. -/
theorem fullScheduleTransferredCTPRFDoesNotHave100Bits :
    ¬ConcreteBound 100 permutationWork fullScheduleTransferredCTPRFError := by
  intro transferred
  have zeroQuery := transferred 0
  rw [WorkPerAdvantage] at zeroQuery
  norm_num [fullScheduleTransferredCTPRFError, Pipeline.permutationCount,
    Pipeline.fixedKeyWindowCount, Pipeline.digitAdaptorCount,
    Pipeline.curveDigitAdaptorCount, Pipeline.pointDigitAdaptorsPerOutput,
    FieldMacToECMac.outputMacCount, BitAdaptor.fixedKeyWindowCount,
    BitAdaptor.fixedKeyPermutationsPerWindow, BitAdaptor.fixedKeyMaxUsesPerBucket,
    blockBits, permutationWork] at zeroQuery

/-- This is the bound shape for one programmable permutation schedule. -/
noncomputable def programmedScheduleError (permutationCount oracleQueries : Nat) : ℝ :=
  ((3 * permutationCount * BitAdaptor.fixedKeyMaxUsesPerBucket ^ 2 +
      4 * BitAdaptor.fixedKeyMaxUsesPerBucket * oracleQueries : Nat) : ℝ) /
    (2 : ℝ) ^ blockBits

/-- Each schedule below the hash schedule retains 100-bit arithmetic. -/
theorem programmedScheduleArithmeticHas100Bits (permutationCount : Nat)
    (scheduleBound : permutationCount ≤ Pipeline.hashPermutationCount) :
    ConcreteBound 100 permutationWork (programmedScheduleError permutationCount) := by
  intro queries
  have countBound :
      3 * permutationCount * BitAdaptor.fixedKeyMaxUsesPerBucket ^ 2 +
          4 * BitAdaptor.fixedKeyMaxUsesPerBucket * queries ≤
        permutationWork queries * 2 ^ 28 := by
    cases queries with
    | zero =>
        norm_num [Pipeline.hashPermutationCount, Pipeline.fixedKeyWindowCount,
          Pipeline.digitAdaptorCount, Pipeline.curveDigitAdaptorCount,
          Pipeline.pointDigitAdaptorsPerOutput, FieldMacToECMac.outputMacCount,
          BitAdaptor.fixedKeyWindowCount, BitAdaptor.fixedKeyMaxUsesPerBucket,
          permutationWork] at scheduleBound ⊢
        omega
    | succ queries =>
        rw [permutationWork, Nat.max_eq_left (by omega : 1 ≤ queries + 1)]
        norm_num [Pipeline.hashPermutationCount, Pipeline.fixedKeyWindowCount,
          Pipeline.digitAdaptorCount, Pipeline.curveDigitAdaptorCount,
          Pipeline.pointDigitAdaptorsPerOutput, FieldMacToECMac.outputMacCount,
          BitAdaptor.fixedKeyWindowCount, BitAdaptor.fixedKeyMaxUsesPerBucket]
          at scheduleBound ⊢
        omega
  rw [WorkPerAdvantage]
  change (((3 * permutationCount * BitAdaptor.fixedKeyMaxUsesPerBucket ^ 2 +
      4 * BitAdaptor.fixedKeyMaxUsesPerBucket * queries : Nat) : ℝ) /
      (2 : ℝ) ^ 128) * (2 : ℝ) ^ 100 ≤ ((permutationWork queries : Nat) : ℝ)
  calc
    (((3 * permutationCount * BitAdaptor.fixedKeyMaxUsesPerBucket ^ 2 +
        4 * BitAdaptor.fixedKeyMaxUsesPerBucket * queries : Nat) : ℝ) /
        (2 : ℝ) ^ 128) * (2 : ℝ) ^ 100 =
      ((3 * permutationCount * BitAdaptor.fixedKeyMaxUsesPerBucket ^ 2 +
        4 * BitAdaptor.fixedKeyMaxUsesPerBucket * queries : Nat) : ℝ) /
        (2 : ℝ) ^ 28 := by
      norm_num [div_eq_mul_inv]
      ring
    _ ≤ ((permutationWork queries : Nat) : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 28)).2
      norm_num
      exact_mod_cast countBound

noncomputable def programmedHashError : Nat → ℝ :=
  programmedScheduleError Pipeline.hashPermutationCount

noncomputable def programmedPadError : Nat → ℝ :=
  programmedScheduleError Pipeline.padPermutationCount

/-- The programmable hash schedule retains 100-bit arithmetic. -/
theorem programmedHashArithmeticHas100Bits :
    ConcreteBound 100 permutationWork programmedHashError :=
  programmedScheduleArithmeticHas100Bits Pipeline.hashPermutationCount (by simp)

/-- The programmable pad schedule retains 100-bit arithmetic. -/
theorem programmedPadArithmeticHas100Bits :
    ConcreteBound 100 permutationWork programmedPadError :=
  programmedScheduleArithmeticHas100Bits Pipeline.padPermutationCount (by decide)

/-- One selected branch pays for its active schedule only. -/
noncomputable def selectedBranchProgrammedError (bit : Bool) : Nat → ℝ :=
  if bit then programmedPadError else programmedHashError

/-- Each selected branch retains 100-bit arithmetic without a five-slot sum. -/
theorem selectedBranchProgrammingArithmeticHas100Bits (bit : Bool) :
    ConcreteBound 100 permutationWork (selectedBranchProgrammedError bit) := by
  cases bit
  · exact programmedHashArithmeticHas100Bits
  · exact programmedPadArithmeticHas100Bits

/-- This value counts all bit-adaptor evaluations in one circuit. -/
def bitAdaptorEvaluationCount : Nat :=
  Pipeline.digitAdaptorCount * coordinateBitCount

theorem bitAdaptorEvaluationCountValue : bitAdaptorEvaluationCount = 301752 := by decide

/-- This is the bound shape for the total 384-bit lift rounding term. -/
noncomputable def hashLiftRoundingError : ℝ :=
  ((bitAdaptorEvaluationCount * BN254.baseFieldModulus : Nat) : ℝ) / (2 : ℝ) ^ 384

set_option exponentiation.threshold 400 in
/-- The total lift rounding term retains 100-bit arithmetic. -/
theorem hashLiftRoundingArithmeticHas100Bits :
    WorkPerAdvantage 100 1 hashLiftRoundingError := by
  rw [WorkPerAdvantage]
  norm_num [hashLiftRoundingError, bitAdaptorEvaluationCount,
    Pipeline.digitAdaptorCount, Pipeline.curveDigitAdaptorCount,
    Pipeline.pointDigitAdaptorsPerOutput, FieldMacToECMac.outputMacCount,
    coordinateBitCount, BN254.baseFieldModulus]

end Kriterion.ArgoMAC.Security
