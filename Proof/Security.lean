/-
This file defines the hybrid chain from the active BaBe paper.
The paper proof is in `gc_rpm_proof.tex` and `gc_optimizations.tex`.
The paper source is https://github.com/babylonlabs-io/BaBe.latex/tree/e2dcf4d540b2708e13cd21090df759051119a116.
-/

import Construction.Garbling
import Cryptography.Assumptions
import Proof.Simulator
import Security.AdaptivePrivacy

namespace Kriterion.ArgoMAC.Security

open GarbledCircuit
open Cryptography
open Cryptography.Assumptions

universe uKey uCounter uCTPRFIndex uEncPRFIndex uHashInput uCPAAux uSample
  uQuery uAnswer uResult uState

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

/-- A list of local forbidden sets has the sum of its per-step cardinality bounds. -/
theorem uniformBlockFinsetMass_sum_le (forbidden : List (Finset Block)) (count : Nat)
    (cardBound : ∀ current ∈ forbidden, current.card ≤ count) :
    (forbidden.map fun current =>
      (PMF.uniformOfFintype Block).toOuterMeasure (current : Set Block)).sum ≤
      (forbidden.length * count : ENNReal) *
        Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal) := by
  induction forbidden with
  | nil => simp
  | cons current tail inductionHypothesis =>
      have currentBound := uniformBlockFinsetMass_le current count
        (cardBound current (by simp))
      have tailBound : ∀ next ∈ tail, next.card ≤ count := by
        intro next member
        exact cardBound next (by simp [member])
      have remainingBound := inductionHypothesis tailBound
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        (PMF.uniformOfFintype Block).toOuterMeasure (current : Set Block) +
            (tail.map fun next =>
              (PMF.uniformOfFintype Block).toOuterMeasure (next : Set Block)).sum ≤
          (count : ENNReal) * Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal) +
            (tail.length * count : ENNReal) *
              Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal) :=
          add_le_add currentBound remainingBound
        _ = ((tail.length + 1) * count : ENNReal) *
              Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal) := by
          ring

/-- A reached trace has at most one local collision term for each budget unit. -/
theorem oracleProgramTrace_collisionScheduleMass_le
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState}
    (handler : OracleHandler oracle State)
    {budget : Nat} {program : OracleProgram oracle Result budget}
    {state : State} {trace : List (oracle.Query × State)}
    (reached : OracleProgramTrace handler program state trace)
    (forbidden : oracle.Query × State → Finset Block) (count : Nat)
    (cardBound : ∀ step ∈ trace, (forbidden step).card ≤ count) :
    ((trace.map forbidden).map fun current =>
      (PMF.uniformOfFintype Block).toOuterMeasure (current : Set Block)).sum ≤
      (budget * count : ENNReal) *
        Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal) := by
  have scheduleBound := uniformBlockFinsetMass_sum_le
    (trace.map forbidden) count (by
      intro current member
      rcases List.mem_map.mp member with ⟨step, stepMember, rfl⟩
      exact cardBound step stepMember)
  have countBound : trace.length * count ≤ budget * count :=
    Nat.mul_le_mul_right count reached.length_le
  calc
    ((trace.map forbidden).map fun current =>
        (PMF.uniformOfFintype Block).toOuterMeasure (current : Set Block)).sum ≤
      (trace.length * count : ENNReal) *
        Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal) := by
      simpa using scheduleBound
    _ ≤ (budget * count : ENNReal) *
        Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal) := by
      apply mul_le_mul_right'
      exact_mod_cast countBound

/-- A Boolean coupling bounds advantage by its two disagreement outcomes. -/
theorem advantage_map_prod_le_disagreement (joint : PMF (Bool × Bool)) :
    advantage (joint.map Prod.fst) (joint.map Prod.snd) ≤
      (joint (true, false)).toReal + (joint (false, true)).toReal := by
  unfold advantage
  simp only [PMF.map_apply]
  simp only [ENNReal.tsum_prod']
  simp only [tsum_bool]
  norm_num
  rw [ENNReal.toReal_add (joint.apply_ne_top _) (joint.apply_ne_top _),
    ENNReal.toReal_add (joint.apply_ne_top _) (joint.apply_ne_top _)]
  ring_nf
  have trueFalseNonnegative : 0 ≤ (joint (true, false)).toReal := ENNReal.toReal_nonneg
  have falseTrueNonnegative : 0 ≤ (joint (false, true)).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- This event contains the two Boolean outcomes where a coupling disagrees. -/
def boolDisagreement : Set (Bool × Bool) :=
  { output | output.1 ≠ output.2 }

/-- The disagreement event has the sum of its two possible outcome masses. -/
theorem boolDisagreement_mass (joint : PMF (Bool × Bool)) :
    joint.toOuterMeasure boolDisagreement =
      joint (true, false) + joint (false, true) := by
  rw [PMF.toOuterMeasure_apply]
  simp only [ENNReal.tsum_prod', tsum_bool]
  norm_num [boolDisagreement, add_comm]

/-- A Boolean coupling bounds advantage by the mass of its disagreement event. -/
theorem advantage_map_prod_le_disagreementMass (joint : PMF (Bool × Bool)) :
    advantage (joint.map Prod.fst) (joint.map Prod.snd) ≤
      (joint.toOuterMeasure boolDisagreement).toReal := by
  rw [boolDisagreement_mass,
    ENNReal.toReal_add (joint.apply_ne_top _) (joint.apply_ne_top _)]
  exact advantage_map_prod_le_disagreement joint

/-- A coupling with bounded disagreement gives the same bound on game advantage. -/
theorem advantage_le_of_coupling (first second : PMF Bool)
    (joint : PMF (Bool × Bool)) (error : ENNReal)
    (firstMarginal : joint.map Prod.fst = first)
    (secondMarginal : joint.map Prod.snd = second)
    (errorFinite : error ≠ ⊤)
    (disagreementBound : joint.toOuterMeasure boolDisagreement ≤ error) :
    advantage first second ≤ error.toReal := by
  rw [← firstMarginal, ← secondMarginal]
  exact (advantage_map_prod_le_disagreementMass joint).trans
    (ENNReal.toReal_mono errorFinite disagreementBound)

/-- A coupling of traced games bounds the advantage of their Boolean marginals. -/
theorem advantage_le_of_tracedCoupling
    {FirstTrace SecondTrace : Type uSample}
    (firstTraced : PMF (Bool × FirstTrace))
    (secondTraced : PMF (Bool × SecondTrace))
    (first second : PMF Bool)
    (joint : PMF ((Bool × FirstTrace) × (Bool × SecondTrace)))
    (error : ENNReal)
    (firstMarginal : joint.map Prod.fst = firstTraced)
    (secondMarginal : joint.map Prod.snd = secondTraced)
    (firstErase : firstTraced.map Prod.fst = first)
    (secondErase : secondTraced.map Prod.fst = second)
    (errorFinite : error ≠ ⊤)
    (disagreementBound : joint.toOuterMeasure
      { sample | sample.1.1 ≠ sample.2.1 } ≤ error) :
    advantage first second ≤ error.toReal := by
  let boolJoint : PMF (Bool × Bool) :=
    joint.map fun sample => (sample.1.1, sample.2.1)
  apply advantage_le_of_coupling first second boolJoint error
  · calc
      boolJoint.map Prod.fst = (joint.map Prod.fst).map Prod.fst := by
        simp [boolJoint, PMF.map_comp, Function.comp_def]
      _ = firstTraced.map Prod.fst := by rw [firstMarginal]
      _ = first := firstErase
  · calc
      boolJoint.map Prod.snd = (joint.map Prod.snd).map Prod.fst := by
        simp [boolJoint, PMF.map_comp, Function.comp_def]
      _ = secondTraced.map Prod.fst := by rw [secondMarginal]
      _ = second := secondErase
  · exact errorFinite
  · change (joint.map fun sample => (sample.1.1, sample.2.1)).toOuterMeasure
        boolDisagreement ≤ error
    rw [PMF.toOuterMeasure_map_apply]
    exact disagreementBound

/-- This coupling maps each first trace to one second trace. -/
noncomputable def traceTransportCoupling
    {FirstTrace SecondTrace : Type uSample}
    (firstTraced : PMF (Bool × FirstTrace))
    (transport : Bool × FirstTrace → Bool × SecondTrace) :
    PMF ((Bool × FirstTrace) × (Bool × SecondTrace)) :=
  firstTraced.map fun sample => (sample, transport sample)

theorem traceTransportCoupling_fst
    {FirstTrace SecondTrace : Type uSample}
    (firstTraced : PMF (Bool × FirstTrace))
    (transport : Bool × FirstTrace → Bool × SecondTrace) :
    (traceTransportCoupling firstTraced transport).map Prod.fst = firstTraced := by
  rw [traceTransportCoupling, PMF.map_comp]
  simpa [Function.comp_def] using PMF.map_id firstTraced

theorem traceTransportCoupling_snd
    {FirstTrace SecondTrace : Type uSample}
    (firstTraced : PMF (Bool × FirstTrace))
    (transport : Bool × FirstTrace → Bool × SecondTrace) :
    (traceTransportCoupling firstTraced transport).map Prod.snd =
      firstTraced.map transport := by
  simp [traceTransportCoupling, PMF.map_comp, Function.comp_def]

theorem traceTransportCoupling_disagreement
    {FirstTrace SecondTrace : Type uSample}
    (firstTraced : PMF (Bool × FirstTrace))
    (transport : Bool × FirstTrace → Bool × SecondTrace) :
    (traceTransportCoupling firstTraced transport).toOuterMeasure
        { sample | sample.1.1 ≠ sample.2.1 } =
      firstTraced.toOuterMeasure
        { sample | sample.1 ≠ (transport sample).1 } := by
  rw [traceTransportCoupling, PMF.toOuterMeasure_map_apply]
  rfl

/-- A Boolean change event is bounded by any bad event that contains it. -/
theorem traceTransport_changeMass_le_badMass
    {FirstTrace SecondTrace : Type uSample}
    (firstTraced : PMF (Bool × FirstTrace))
    (transport : Bool × FirstTrace → Bool × SecondTrace)
    (bad : Set (Bool × FirstTrace))
    (changeImpliesBad : ∀ sample,
      sample.1 ≠ (transport sample).1 → sample ∈ bad) :
    firstTraced.toOuterMeasure
        { sample | sample.1 ≠ (transport sample).1 } ≤
      firstTraced.toOuterMeasure bad := by
  apply firstTraced.toOuterMeasure.mono
  intro sample changed
  exact changeImpliesBad sample changed

/-- A trace transport reduces the game bound to its Boolean change event. -/
theorem advantage_le_of_traceTransport
    {FirstTrace SecondTrace : Type uSample}
    (firstTraced : PMF (Bool × FirstTrace))
    (secondTraced : PMF (Bool × SecondTrace))
    (first second : PMF Bool)
    (transport : Bool × FirstTrace → Bool × SecondTrace)
    (error : ENNReal)
    (secondMap : firstTraced.map transport = secondTraced)
    (firstErase : firstTraced.map Prod.fst = first)
    (secondErase : secondTraced.map Prod.fst = second)
    (errorFinite : error ≠ ⊤)
    (changeBound : firstTraced.toOuterMeasure
      { sample | sample.1 ≠ (transport sample).1 } ≤ error) :
    advantage first second ≤ error.toReal := by
  exact advantage_le_of_tracedCoupling firstTraced secondTraced first second
    (traceTransportCoupling firstTraced transport) error
    (traceTransportCoupling_fst firstTraced transport)
    ((traceTransportCoupling_snd firstTraced transport).trans secondMap)
    firstErase secondErase errorFinite
    (by simpa [traceTransportCoupling_disagreement] using changeBound)

/-- A trace transport and a containing bad event bound the game advantage. -/
theorem advantage_le_of_traceTransport_badEvent
    {FirstTrace SecondTrace : Type uSample}
    (firstTraced : PMF (Bool × FirstTrace))
    (secondTraced : PMF (Bool × SecondTrace))
    (first second : PMF Bool)
    (transport : Bool × FirstTrace → Bool × SecondTrace)
    (bad : Set (Bool × FirstTrace))
    (error : ENNReal)
    (secondMap : firstTraced.map transport = secondTraced)
    (firstErase : firstTraced.map Prod.fst = first)
    (secondErase : secondTraced.map Prod.fst = second)
    (errorFinite : error ≠ ⊤)
    (changeImpliesBad : ∀ sample,
      sample.1 ≠ (transport sample).1 → sample ∈ bad)
    (badBound : firstTraced.toOuterMeasure bad ≤ error) :
    advantage first second ≤ error.toReal := by
  apply advantage_le_of_traceTransport firstTraced secondTraced first second
    transport error secondMap firstErase secondErase errorFinite
  exact (traceTransport_changeMass_le_badMass firstTraced transport bad
    changeImpliesBad).trans badBound

/-- This coupling runs two deterministic Boolean games on one common sample. -/
noncomputable def deterministicBoolCoupling {Sample : Type uSample}
    (source : PMF Sample) (first second : Sample → Bool) : PMF (Bool × Bool) :=
  source.map fun sample => (first sample, second sample)

theorem deterministicBoolCoupling_fst {Sample : Type uSample}
    (source : PMF Sample) (first second : Sample → Bool) :
    (deterministicBoolCoupling source first second).map Prod.fst = source.map first := by
  simp [deterministicBoolCoupling, PMF.map_comp, Function.comp_def]

theorem deterministicBoolCoupling_snd {Sample : Type uSample}
    (source : PMF Sample) (first second : Sample → Bool) :
    (deterministicBoolCoupling source first second).map Prod.snd = source.map second := by
  simp [deterministicBoolCoupling, PMF.map_comp, Function.comp_def]

theorem deterministicBoolCoupling_disagreement {Sample : Type uSample}
    (source : PMF Sample) (first second : Sample → Bool) :
    (deterministicBoolCoupling source first second).toOuterMeasure boolDisagreement =
      source.toOuterMeasure { sample | first sample ≠ second sample } := by
  rw [deterministicBoolCoupling, PMF.toOuterMeasure_map_apply]
  rfl

/-- Two deterministic games differ by at most their disagreement-event mass. -/
theorem advantage_map_le_disagreementMass {Sample : Type uSample}
    (source : PMF Sample) (first second : Sample → Bool) :
    advantage (source.map first) (source.map second) ≤
      (source.toOuterMeasure { sample | first sample ≠ second sample }).toReal := by
  let joint := deterministicBoolCoupling source first second
  calc
    advantage (source.map first) (source.map second) =
        advantage (joint.map Prod.fst) (joint.map Prod.snd) := by
      rw [deterministicBoolCoupling_fst, deterministicBoolCoupling_snd]
    _ ≤ (joint.toOuterMeasure boolDisagreement).toReal :=
      advantage_map_prod_le_disagreementMass joint
    _ = (source.toOuterMeasure { sample | first sample ≠ second sample }).toReal := by
      rw [deterministicBoolCoupling_disagreement]

/-- The finite collision mass converts to the challenge's real-valued error formula. -/
theorem blockCollisionMass_toReal (count : Nat) :
    ((count : ENNReal) * Inv.inv (↑(2 ^ blockBits : Nat) : ENNReal)).toReal =
      (count : ℝ) / (2 : ℝ) ^ blockBits := by
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_inv]
  norm_num [blockBits, div_eq_mul_inv]

/-- This game refines the real adaptive game with both reached query traces. -/
noncomputable def tracedRealGame
    {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle : Type uSample} {Aux : Type uCPAAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle)
    (randomTape : Nat → PMF Randomness)
    (oracleHandler : OracleHandler oracle Randomness)
    (adversary : AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    PMF (Bool × Randomness × List (oracle.Query × Randomness)) :=
  (randomTape parameter).bind fun randomness =>
    let garbled := scheme.garble parameter circuit randomness
    runOracleProgramsWithTrace oracleHandler
      (adversary.chooseInput parameter garbled.1 auxiliary)
      (fun selected => adversary.decide parameter garbled.1
        (scheme.encode garbled.2 selected.1) auxiliary selected.2)
      randomness

/-- Erasing both real traces gives the challenge's real game. -/
theorem tracedRealGame_erase
    {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle : Type uSample} {Aux : Type uCPAAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle)
    (randomTape : Nat → PMF Randomness)
    (oracleHandler : OracleHandler oracle Randomness)
    (adversary : AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    (tracedRealGame scheme randomTape oracleHandler adversary parameter circuit auxiliary).map
        Prod.fst =
      realGame scheme randomTape oracleHandler adversary parameter circuit auxiliary := by
  rw [tracedRealGame, realGame, PMF.map_bind]
  congr 1
  funext randomness
  simpa only using runOracleProgramsWithTrace_result oracleHandler
    (adversary.chooseInput parameter (scheme.garble parameter circuit randomness).1 auxiliary)
    (fun selected : Input × adversary.State => adversary.decide parameter
      (scheme.garble parameter circuit randomness).1
      (scheme.encode (scheme.garble parameter circuit randomness).2 selected.1)
      auxiliary selected.2) randomness

/-- The traced real game gives zero mass to paths above both query budgets. -/
theorem tracedRealGame_overBudget_mass
    {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle : Type uSample} {Aux : Type uCPAAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle)
    (randomTape : Nat → PMF Randomness)
    (oracleHandler : OracleHandler oracle Randomness)
    (adversary : AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    PMF.toOuterMeasure
      (tracedRealGame scheme randomTape oracleHandler adversary parameter circuit auxiliary)
      { output |
        adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter <
          output.2.2.length } = 0 := by
  rw [tracedRealGame, PMF.toOuterMeasure_bind_apply]
  simp_rw [runOracleProgramsWithTrace_overBudget_mass, mul_zero]
  simp

/-- This game refines the ideal adaptive game with both reached query traces. -/
noncomputable def tracedIdealGame
    {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle
      Topology State : Type uSample} {Aux : Type uCPAAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle)
    (topology : Circuit → Topology)
    (simulator : Simulator Input Output Public Labels Topology State)
    (oracleHandler : OracleHandler oracle State)
    (adversary : AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    PMF (Bool × State × List (oracle.Query × State)) :=
  (simulator.simulateGarble parameter (topology circuit)).bind fun simulated =>
    runOracleProgramsWithBridgeTrace oracleHandler
      (adversary.chooseInput parameter simulated.1 auxiliary)
      (fun selected state =>
        simulator.simulateEncode state selected.1 (scheme.function circuit selected.1))
      (fun selected encoded => adversary.decide parameter simulated.1 encoded
        auxiliary selected.2)
      simulated.2

/-- Erasing both ideal traces gives the challenge's ideal game. -/
theorem tracedIdealGame_erase
    {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle
      Topology State : Type uSample} {Aux : Type uCPAAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle)
    (topology : Circuit → Topology)
    (simulator : Simulator Input Output Public Labels Topology State)
    (oracleHandler : OracleHandler oracle State)
    (adversary : AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    (tracedIdealGame scheme topology simulator oracleHandler adversary parameter circuit
      auxiliary).map Prod.fst =
      idealGame scheme topology simulator oracleHandler adversary parameter circuit
        auxiliary := by
  rw [tracedIdealGame, idealGame, PMF.map_bind]
  congr 1
  funext simulated
  simpa only using runOracleProgramsWithBridgeTrace_result oracleHandler
    (adversary.chooseInput parameter simulated.1 auxiliary)
    (fun selected : Input × adversary.State => fun state =>
      simulator.simulateEncode state selected.1 (scheme.function circuit selected.1))
    (fun selected : Input × adversary.State => fun encoded : Labels =>
      adversary.decide parameter simulated.1 encoded auxiliary selected.2)
    simulated.2

/-- The traced ideal game gives zero mass to paths above both query budgets. -/
theorem tracedIdealGame_overBudget_mass
    {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle
      Topology State : Type uSample} {Aux : Type uCPAAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle)
    (topology : Circuit → Topology)
    (simulator : Simulator Input Output Public Labels Topology State)
    (oracleHandler : OracleHandler oracle State)
    (adversary : AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    (tracedIdealGame scheme topology simulator oracleHandler adversary parameter circuit
      auxiliary).toOuterMeasure { output |
        adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter <
          output.2.2.length } = 0 := by
  rw [tracedIdealGame, PMF.toOuterMeasure_bind_apply]
  simp_rw [runOracleProgramsWithBridgeTrace_overBudget_mass, mul_zero]
  simp

/-- One traced coupling and one bad-event bound imply the adaptive game bound. -/
theorem adaptiveAdvantage_le_of_tracedCoupling
    {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle
      Topology State : Type uSample} {Aux : Type uCPAAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle)
    (topology : Circuit → Topology)
    (simulator : Simulator Input Output Public Labels Topology State)
    (randomTape : Nat → PMF Randomness)
    (realOracle : OracleHandler oracle Randomness)
    (idealOracle : OracleHandler oracle State)
    (adversary : AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux)
    (joint : PMF
      ((Bool × Randomness × List (oracle.Query × Randomness)) ×
        (Bool × State × List (oracle.Query × State))))
    (error : ENNReal)
    (firstMarginal : joint.map Prod.fst =
      tracedRealGame scheme randomTape realOracle adversary parameter circuit auxiliary)
    (secondMarginal : joint.map Prod.snd =
      tracedIdealGame scheme topology simulator idealOracle adversary parameter circuit
        auxiliary)
    (errorFinite : error ≠ ⊤)
    (disagreementBound : joint.toOuterMeasure
      { sample | sample.1.1 ≠ sample.2.1 } ≤ error) :
    advantage
      (realGame scheme randomTape realOracle adversary parameter circuit auxiliary)
      (idealGame scheme topology simulator idealOracle adversary parameter circuit auxiliary) ≤
        error.toReal := by
  exact advantage_le_of_tracedCoupling
    (tracedRealGame scheme randomTape realOracle adversary parameter circuit auxiliary)
    (tracedIdealGame scheme topology simulator idealOracle adversary parameter circuit auxiliary)
    (realGame scheme randomTape realOracle adversary parameter circuit auxiliary)
    (idealGame scheme topology simulator idealOracle adversary parameter circuit auxiliary)
    joint error firstMarginal secondMarginal
    (tracedRealGame_erase scheme randomTape realOracle adversary parameter circuit auxiliary)
    (tracedIdealGame_erase scheme topology simulator idealOracle adversary parameter circuit
      auxiliary)
    errorFinite disagreementBound

/-- One trace transport and one change-event bound imply the adaptive game bound. -/
theorem adaptiveAdvantage_le_of_traceTransport
    {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle
      Topology State : Type uSample} {Aux : Type uCPAAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle)
    (topology : Circuit → Topology)
    (simulator : Simulator Input Output Public Labels Topology State)
    (randomTape : Nat → PMF Randomness)
    (realOracle : OracleHandler oracle Randomness)
    (idealOracle : OracleHandler oracle State)
    (adversary : AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux)
    (transport :
      Bool × Randomness × List (oracle.Query × Randomness) →
        Bool × State × List (oracle.Query × State))
    (error : ENNReal)
    (secondMap :
      (tracedRealGame scheme randomTape realOracle adversary parameter circuit auxiliary).map
          transport =
        tracedIdealGame scheme topology simulator idealOracle adversary parameter circuit
          auxiliary)
    (errorFinite : error ≠ ⊤)
    (changeBound :
      PMF.toOuterMeasure
        (tracedRealGame scheme randomTape realOracle adversary parameter circuit auxiliary)
        { sample | sample.1 ≠ (transport sample).1 } ≤ error) :
    advantage
      (realGame scheme randomTape realOracle adversary parameter circuit auxiliary)
      (idealGame scheme topology simulator idealOracle adversary parameter circuit auxiliary) ≤
        error.toReal := by
  exact advantage_le_of_traceTransport
    (tracedRealGame scheme randomTape realOracle adversary parameter circuit auxiliary)
    (tracedIdealGame scheme topology simulator idealOracle adversary parameter circuit auxiliary)
    (realGame scheme randomTape realOracle adversary parameter circuit auxiliary)
    (idealGame scheme topology simulator idealOracle adversary parameter circuit auxiliary)
    transport error secondMap
    (tracedRealGame_erase scheme randomTape realOracle adversary parameter circuit auxiliary)
    (tracedIdealGame_erase scheme topology simulator idealOracle adversary parameter circuit
      auxiliary)
    errorFinite changeBound

/-- Traced couplings with concrete bounds imply the adaptive privacy property. -/
theorem concreteAdaptivePrivacy_of_tracedCouplings
    {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle
      Topology State : Type uSample} {Aux : Type uCPAAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle)
    (topology : Circuit → Topology)
    (simulator : Simulator Input Output Public Labels Topology State)
    (randomTape : Nat → PMF Randomness)
    (realOracle : OracleHandler oracle Randomness)
    (idealOracle : OracleHandler oracle State)
    (bits : Nat)
    (error : AdaptiveAdversary oracle Input Public Labels Aux → Nat → ENNReal)
    (errorFinite : ∀ adversary parameter, error adversary parameter ≠ ⊤)
    (errorConcrete : ∀ adversary parameter,
      WorkPerAdvantage bits (adversaryWork adversary parameter)
        (error adversary parameter).toReal)
    (coupling : ∀ adversary circuit auxiliary parameter,
      ∃ joint : PMF
        ((Bool × Randomness × List (oracle.Query × Randomness)) ×
          (Bool × State × List (oracle.Query × State))),
        joint.map Prod.fst =
            tracedRealGame scheme randomTape realOracle adversary parameter circuit auxiliary ∧
          joint.map Prod.snd =
            tracedIdealGame scheme topology simulator idealOracle adversary parameter circuit
              auxiliary ∧
          joint.toOuterMeasure { sample | sample.1.1 ≠ sample.2.1 } ≤
            error adversary parameter) :
    ConcreteAdaptivePrivacy (Aux := Aux) scheme topology simulator randomTape realOracle
      idealOracle bits := by
  intro adversary circuits auxiliaries parameter
  rcases coupling adversary (circuits parameter) (auxiliaries parameter) parameter with
    ⟨joint, firstMarginal, secondMarginal, disagreementBound⟩
  have advantageBound := adaptiveAdvantage_le_of_tracedCoupling
    scheme topology simulator randomTape realOracle idealOracle adversary parameter
    (circuits parameter) (auxiliaries parameter) joint (error adversary parameter)
    firstMarginal secondMarginal (errorFinite adversary parameter) disagreementBound
  unfold WorkPerAdvantage
  exact (mul_le_mul_of_nonneg_right advantageBound (by positivity)).trans
    (errorConcrete adversary parameter)

/-- Trace transports with concrete bounds imply the adaptive privacy property. -/
theorem concreteAdaptivePrivacy_of_traceTransports
    {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle
      Topology State : Type uSample} {Aux : Type uCPAAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle)
    (topology : Circuit → Topology)
    (simulator : Simulator Input Output Public Labels Topology State)
    (randomTape : Nat → PMF Randomness)
    (realOracle : OracleHandler oracle Randomness)
    (idealOracle : OracleHandler oracle State)
    (bits : Nat)
    (error : AdaptiveAdversary oracle Input Public Labels Aux → Nat → ENNReal)
    (errorFinite : ∀ adversary parameter, error adversary parameter ≠ ⊤)
    (errorConcrete : ∀ adversary parameter,
      WorkPerAdvantage bits (adversaryWork adversary parameter)
        (error adversary parameter).toReal)
    (transport : ∀
      (_adversary : AdaptiveAdversary oracle Input Public Labels Aux)
      (_circuit : Circuit) (_auxiliary : Aux) (_parameter : Nat),
      Bool × Randomness × List (oracle.Query × Randomness) →
        Bool × State × List (oracle.Query × State))
    (secondMap : ∀
      (adversary : AdaptiveAdversary oracle Input Public Labels Aux)
      (circuit : Circuit) (auxiliary : Aux) (parameter : Nat),
      (tracedRealGame scheme randomTape realOracle adversary parameter circuit auxiliary).map
          (transport adversary circuit auxiliary parameter) =
        tracedIdealGame scheme topology simulator idealOracle adversary parameter circuit
          auxiliary)
    (changeBound : ∀
      (adversary : AdaptiveAdversary oracle Input Public Labels Aux)
      (circuit : Circuit) (auxiliary : Aux) (parameter : Nat),
      PMF.toOuterMeasure
        (tracedRealGame scheme randomTape realOracle adversary parameter circuit auxiliary)
          { sample |
            sample.1 ≠ (transport adversary circuit auxiliary parameter sample).1 } ≤
        error adversary parameter) :
    ConcreteAdaptivePrivacy (Aux := Aux) scheme topology simulator randomTape realOracle
      idealOracle bits := by
  intro adversary circuits auxiliaries parameter
  have advantageBound := adaptiveAdvantage_le_of_traceTransport
    scheme topology simulator randomTape realOracle idealOracle adversary parameter
    (circuits parameter) (auxiliaries parameter)
    (transport adversary (circuits parameter) (auxiliaries parameter) parameter)
    (error adversary parameter)
    (secondMap adversary (circuits parameter) (auxiliaries parameter) parameter)
    (errorFinite adversary parameter)
    (changeBound adversary (circuits parameter) (auxiliaries parameter) parameter)
  unfold WorkPerAdvantage
  exact (mul_le_mul_of_nonneg_right advantageBound (by positivity)).trans
    (errorConcrete adversary parameter)

/-- The paper base-`(2 - omega)` case uses 92 active inputs per bucket. -/
def paperActiveInputsPerBucket : Nat := 92

/-- The paper proof uses 6858 independent permutation buckets. -/
def paperBucketCount : Nat := 6858

/-- Mixed selected branches fit below the three-hash birthday budget. -/
theorem selectedBranchBucketSquareBound (falseUses trueUses capacity : Nat)
    (loadBound : falseUses + trueUses ≤ capacity) :
    3 * falseUses ^ 2 + 2 * trueUses ^ 2 ≤ 3 * capacity ^ 2 := by
  nlinarith [Nat.zero_le falseUses, Nat.zero_le trueUses]

/-- Mixed selected branches fit below the three-hash linear query budget. -/
theorem selectedBranchBucketLinearBound (falseUses trueUses capacity : Nat)
    (loadBound : falseUses + trueUses ≤ capacity) :
    3 * falseUses + 2 * trueUses ≤ 3 * capacity := by
  omega

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
