import Proof.Simulator

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

universe uQuery uAnswer uResult uStateOne uStateTwo uFirst uMiddle uSecond

/-- This coupling samples two PMFs independently. -/
noncomputable def independentPMFCoupling
    {First : Type uFirst} {Second : Type uSecond}
    (first : PMF First) (second : PMF Second) : PMF (First × Second) :=
  first.bind fun firstValue => second.map fun secondValue => (firstValue, secondValue)

theorem independentPMFCoupling_fst
    {First : Type uFirst} {Second : Type uSecond}
    (first : PMF First) (second : PMF Second) :
    (independentPMFCoupling first second).map Prod.fst = first := by
  calc
    _ = first.bind fun value => second.map (Function.const Second value) := by
      rw [independentPMFCoupling, PMF.map_bind]
      congr 1
      funext value
      rw [PMF.map_comp]
      rfl
    _ = first.bind PMF.pure := by
      congr 1
      funext value
      exact PMF.map_const second value
    _ = first := PMF.bind_pure first

theorem independentPMFCoupling_snd
    {First : Type uFirst} {Second : Type uSecond}
    (first : PMF First) (second : PMF Second) :
    (independentPMFCoupling first second).map Prod.snd = second := by
  calc
    _ = first.bind fun _ => second.map id := by
      rw [independentPMFCoupling, PMF.map_bind]
      congr 1
      funext value
      rw [PMF.map_comp]
      rfl
    _ = first.bind fun _ => second := by rw [PMF.map_id]
    _ = second := PMF.bind_const first second

/-- One bridge step is exact or records a bad event. -/
inductive RelatedOrBadBridgeOutput
    (MiddleResult : Type uMiddle)
    (StateOne : Type uStateOne) (StateTwo : Type uStateTwo)
    (related : StateOne → StateTwo → Prop) where
  | related (result : MiddleResult) (stateOne : StateOne) (stateTwo : StateTwo)
      (statesRelated : related stateOne stateTwo)
  | bad (resultOne : MiddleResult) (stateOne : StateOne)
      (resultTwo : MiddleResult) (stateTwo : StateTwo)

def RelatedOrBadBridgeOutput.first
    {MiddleResult : Type uMiddle}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    {related : StateOne → StateTwo → Prop} :
    RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related →
      MiddleResult × StateOne
  | .related result stateOne _ _ => (result, stateOne)
  | .bad resultOne stateOne _ _ => (resultOne, stateOne)

def RelatedOrBadBridgeOutput.second
    {MiddleResult : Type uMiddle}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    {related : StateOne → StateTwo → Prop} :
    RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related →
      MiddleResult × StateTwo
  | .related result _ stateTwo _ => (result, stateTwo)
  | .bad _ _ resultTwo stateTwo => (resultTwo, stateTwo)

def RelatedOrBadBridgeOutput.isBad
    {MiddleResult : Type uMiddle}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    {related : StateOne → StateTwo → Prop} :
    RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related → Bool
  | .related _ _ _ _ => false
  | .bad _ _ _ _ => true

/-- Continue both second phases after one exact or bad bridge output. -/
noncomputable def boundedBridgeContinuation
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {secondBudget : Nat}
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (firstResult : FirstResult)
    (traceOne : List (oracle.Query × StateOne))
    (traceTwo : List (oracle.Query × StateTwo)) :
    RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related →
      PMF (((SecondResult × StateOne × List (oracle.Query × StateOne)) ×
        (SecondResult × StateTwo × List (oracle.Query × StateTwo))) × Bool)
  | .related result stateOne stateTwo statesRelated =>
      (runOracleProgramRelatedTraceCoupling handlerOne handlerTwo related
        handlerRelated (second firstResult result) stateOne stateTwo statesRelated).map
          fun secondOutput =>
            (((secondOutput.result, secondOutput.stateOne,
                traceOne ++ secondOutput.traceOne),
              (secondOutput.result, secondOutput.stateTwo,
                traceTwo ++ secondOutput.traceTwo)), false)
  | .bad resultOne stateOne resultTwo stateTwo =>
      (independentPMFCoupling
        (runOracleProgramWithTrace handlerOne (second firstResult resultOne) stateOne)
        (runOracleProgramWithTrace handlerTwo (second firstResult resultTwo) stateTwo)).map
          fun secondOutput =>
            (((secondOutput.1.1, secondOutput.1.2.1,
                traceOne ++ secondOutput.1.2.2),
              (secondOutput.2.1, secondOutput.2.2.1,
                traceTwo ++ secondOutput.2.2.2)), true)

/-- The first continuation marginal follows the first bridge output. -/
theorem boundedBridgeContinuation_fst
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {secondBudget : Nat}
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (firstResult : FirstResult)
    (traceOne : List (oracle.Query × StateOne))
    (traceTwo : List (oracle.Query × StateTwo))
    (middleOutput : RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related) :
    (boundedBridgeContinuation handlerOne handlerTwo related handlerRelated second
      firstResult traceOne traceTwo middleOutput).map (fun output => output.1.1) =
      (runOracleProgramWithTrace handlerOne
        (second firstResult (RelatedOrBadBridgeOutput.first middleOutput).1)
        (RelatedOrBadBridgeOutput.first middleOutput).2).map fun secondOutput =>
          (secondOutput.1, secondOutput.2.1, traceOne ++ secondOutput.2.2) := by
  cases middleOutput with
  | related result stateOne stateTwo statesRelated =>
      simp only [boundedBridgeContinuation, RelatedOrBadBridgeOutput.first,
        PMF.map_comp, Function.comp_def]
      change (runOracleProgramRelatedTraceCoupling handlerOne handlerTwo related
          handlerRelated (second firstResult result) stateOne stateTwo statesRelated).map
            ((fun output =>
              (output.1, output.2.1, traceOne ++ output.2.2)) ∘
              fun output => (output.result, output.stateOne, output.traceOne)) = _
      rw [← PMF.map_comp]
      rw [runOracleProgramRelatedTraceCoupling_fst]
  | bad resultOne stateOne resultTwo stateTwo =>
      simp only [boundedBridgeContinuation, RelatedOrBadBridgeOutput.first,
        PMF.map_comp, Function.comp_def]
      change (independentPMFCoupling
          (runOracleProgramWithTrace handlerOne (second firstResult resultOne) stateOne)
          (runOracleProgramWithTrace handlerTwo (second firstResult resultTwo) stateTwo)).map
            ((fun output =>
              (output.1, output.2.1, traceOne ++ output.2.2)) ∘ Prod.fst) = _
      rw [← PMF.map_comp]
      rw [independentPMFCoupling_fst]

/-- The second continuation marginal follows the second bridge output. -/
theorem boundedBridgeContinuation_snd
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {secondBudget : Nat}
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (firstResult : FirstResult)
    (traceOne : List (oracle.Query × StateOne))
    (traceTwo : List (oracle.Query × StateTwo))
    (middleOutput : RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related) :
    (boundedBridgeContinuation handlerOne handlerTwo related handlerRelated second
      firstResult traceOne traceTwo middleOutput).map (fun output => output.1.2) =
      (runOracleProgramWithTrace handlerTwo
        (second firstResult (RelatedOrBadBridgeOutput.second middleOutput).1)
        (RelatedOrBadBridgeOutput.second middleOutput).2).map fun secondOutput =>
          (secondOutput.1, secondOutput.2.1, traceTwo ++ secondOutput.2.2) := by
  cases middleOutput with
  | related result stateOne stateTwo statesRelated =>
      simp only [boundedBridgeContinuation, RelatedOrBadBridgeOutput.second,
        PMF.map_comp, Function.comp_def]
      change (runOracleProgramRelatedTraceCoupling handlerOne handlerTwo related
          handlerRelated (second firstResult result) stateOne stateTwo statesRelated).map
            ((fun output =>
              (output.1, output.2.1, traceTwo ++ output.2.2)) ∘
              fun output => (output.result, output.stateTwo, output.traceTwo)) = _
      rw [← PMF.map_comp]
      rw [runOracleProgramRelatedTraceCoupling_snd]
  | bad resultOne stateOne resultTwo stateTwo =>
      simp only [boundedBridgeContinuation, RelatedOrBadBridgeOutput.second,
        PMF.map_comp, Function.comp_def]
      change (independentPMFCoupling
          (runOracleProgramWithTrace handlerOne (second firstResult resultOne) stateOne)
          (runOracleProgramWithTrace handlerTwo (second firstResult resultTwo) stateTwo)).map
            ((fun output =>
              (output.1, output.2.1, traceTwo ++ output.2.2)) ∘ Prod.snd) = _
      rw [← PMF.map_comp]
      rw [independentPMFCoupling_snd]

/-- The continuation keeps the bridge bad-event flag. -/
theorem boundedBridgeContinuation_bad
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {secondBudget : Nat}
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (firstResult : FirstResult)
    (traceOne : List (oracle.Query × StateOne))
    (traceTwo : List (oracle.Query × StateTwo))
    (middleOutput : RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related) :
    (boundedBridgeContinuation handlerOne handlerTwo related handlerRelated second
      firstResult traceOne traceTwo middleOutput).map Prod.snd =
      PMF.pure middleOutput.isBad := by
  cases middleOutput with
  | related result stateOne stateTwo statesRelated =>
      simp only [boundedBridgeContinuation, RelatedOrBadBridgeOutput.isBad,
        PMF.map_comp, Function.comp_def]
      change PMF.map (Function.const _ false)
        (runOracleProgramRelatedTraceCoupling handlerOne handlerTwo related handlerRelated
          (second firstResult result) stateOne stateTwo statesRelated) = PMF.pure false
      exact PMF.map_const _ _
  | bad resultOne stateOne resultTwo stateTwo =>
      simp only [boundedBridgeContinuation, RelatedOrBadBridgeOutput.isBad,
        PMF.map_comp, Function.comp_def]
      change PMF.map (Function.const _ true)
        (independentPMFCoupling
          (runOracleProgramWithTrace handlerOne (second firstResult resultOne) stateOne)
          (runOracleProgramWithTrace handlerTwo (second firstResult resultTwo) stateTwo)) =
            PMF.pure true
      exact PMF.map_const _ _

/-- Couple two phases exactly until the bridge records a bad event. -/
noncomputable def runOracleProgramsBoundedBridgeTraceCoupling
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (bridgeCoupling : FirstResult → (stateOne : StateOne) →
      (stateTwo : StateTwo) → related stateOne stateTwo →
        PMF (RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related))
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (stateOne : StateOne) (stateTwo : StateTwo)
    (statesRelated : related stateOne stateTwo) :
    PMF (((SecondResult × StateOne × List (oracle.Query × StateOne)) ×
      (SecondResult × StateTwo × List (oracle.Query × StateTwo))) × Bool) :=
  (runOracleProgramRelatedTraceCoupling handlerOne handlerTwo related handlerRelated
    first stateOne stateTwo statesRelated).bind fun firstOutput =>
      (bridgeCoupling firstOutput.result firstOutput.stateOne firstOutput.stateTwo
        firstOutput.statesRelated).bind fun middleOutput =>
          boundedBridgeContinuation handlerOne handlerTwo related handlerRelated second
            firstOutput.result firstOutput.traceOne firstOutput.traceTwo middleOutput

/-- The first marginal is the first bridged traced run. -/
theorem runOracleProgramsBoundedBridgeTraceCoupling_fst
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (bridgeOne : FirstResult → StateOne → PMF (MiddleResult × StateOne))
    (bridgeCoupling : FirstResult → (stateOne : StateOne) →
      (stateTwo : StateTwo) → related stateOne stateTwo →
        PMF (RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related))
    (bridgeFst : ∀ result stateOne stateTwo statesRelated,
      (bridgeCoupling result stateOne stateTwo statesRelated).map
          RelatedOrBadBridgeOutput.first = bridgeOne result stateOne)
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (stateOne : StateOne) (stateTwo : StateTwo)
    (statesRelated : related stateOne stateTwo) :
    (runOracleProgramsBoundedBridgeTraceCoupling handlerOne handlerTwo related
      handlerRelated first bridgeCoupling second stateOne stateTwo statesRelated).map
        (fun output => output.1.1) =
      runOracleProgramsWithBridgeTrace handlerOne first bridgeOne second stateOne := by
  simp only [runOracleProgramsBoundedBridgeTraceCoupling,
    runOracleProgramsWithBridgeTrace, PMF.map_bind]
  rw [← runOracleProgramRelatedTraceCoupling_fst handlerOne handlerTwo related
    handlerRelated first stateOne stateTwo statesRelated]
  rw [PMF.bind_map]
  congr 1
  funext firstOutput
  simp_rw [boundedBridgeContinuation_fst]
  calc
    _ = ((bridgeCoupling firstOutput.result firstOutput.stateOne
        firstOutput.stateTwo firstOutput.statesRelated).map
          RelatedOrBadBridgeOutput.first).bind fun middleOutput =>
            (runOracleProgramWithTrace handlerOne
              (second firstOutput.result middleOutput.1) middleOutput.2).map fun secondOutput =>
                (secondOutput.1, secondOutput.2.1,
                  firstOutput.traceOne ++ secondOutput.2.2) := by
      rw [PMF.bind_map]
      simp only [Function.comp_def]
    _ = _ := by
      rw [bridgeFst]
      rfl

/-- The second marginal is the second bridged traced run. -/
theorem runOracleProgramsBoundedBridgeTraceCoupling_snd
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (bridgeTwo : FirstResult → StateTwo → PMF (MiddleResult × StateTwo))
    (bridgeCoupling : FirstResult → (stateOne : StateOne) →
      (stateTwo : StateTwo) → related stateOne stateTwo →
        PMF (RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related))
    (bridgeSnd : ∀ result stateOne stateTwo statesRelated,
      (bridgeCoupling result stateOne stateTwo statesRelated).map
          RelatedOrBadBridgeOutput.second = bridgeTwo result stateTwo)
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (stateOne : StateOne) (stateTwo : StateTwo)
    (statesRelated : related stateOne stateTwo) :
    (runOracleProgramsBoundedBridgeTraceCoupling handlerOne handlerTwo related
      handlerRelated first bridgeCoupling second stateOne stateTwo statesRelated).map
        (fun output => output.1.2) =
      runOracleProgramsWithBridgeTrace handlerTwo first bridgeTwo second stateTwo := by
  simp only [runOracleProgramsBoundedBridgeTraceCoupling,
    runOracleProgramsWithBridgeTrace, PMF.map_bind]
  rw [← runOracleProgramRelatedTraceCoupling_snd handlerOne handlerTwo related
    handlerRelated first stateOne stateTwo statesRelated]
  rw [PMF.bind_map]
  congr 1
  funext firstOutput
  simp_rw [boundedBridgeContinuation_snd]
  calc
    _ = ((bridgeCoupling firstOutput.result firstOutput.stateOne
        firstOutput.stateTwo firstOutput.statesRelated).map
          RelatedOrBadBridgeOutput.second).bind fun middleOutput =>
            (runOracleProgramWithTrace handlerTwo
              (second firstOutput.result middleOutput.1) middleOutput.2).map fun secondOutput =>
                (secondOutput.1, secondOutput.2.1,
                  firstOutput.traceTwo ++ secondOutput.2.2) := by
      rw [PMF.bind_map]
      simp only [Function.comp_def]
    _ = _ := by
      rw [bridgeSnd]
      rfl

/-- The full coupling keeps the bridge bad-event distribution. -/
theorem runOracleProgramsBoundedBridgeTraceCoupling_bad
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (bridgeCoupling : FirstResult → (stateOne : StateOne) →
      (stateTwo : StateTwo) → related stateOne stateTwo →
        PMF (RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related))
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (stateOne : StateOne) (stateTwo : StateTwo)
    (statesRelated : related stateOne stateTwo) :
    (runOracleProgramsBoundedBridgeTraceCoupling handlerOne handlerTwo related
      handlerRelated first bridgeCoupling second stateOne stateTwo statesRelated).map
        Prod.snd =
      (runOracleProgramRelatedTraceCoupling handlerOne handlerTwo related handlerRelated
        first stateOne stateTwo statesRelated).bind fun firstOutput =>
          (bridgeCoupling firstOutput.result firstOutput.stateOne firstOutput.stateTwo
            firstOutput.statesRelated).map RelatedOrBadBridgeOutput.isBad := by
  simp only [runOracleProgramsBoundedBridgeTraceCoupling, PMF.map_bind]
  congr 1
  funext firstOutput
  simp_rw [boundedBridgeContinuation_bad]
  change (bridgeCoupling firstOutput.result firstOutput.stateOne firstOutput.stateTwo
      firstOutput.statesRelated).bind (PMF.pure ∘ RelatedOrBadBridgeOutput.isBad) = _
  exact PMF.bind_pure_comp _ _

/-- The final bad-event mass is the bad bridge probability. -/
theorem runOracleProgramsBoundedBridgeTraceCoupling_bad_mass
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (bridgeCoupling : FirstResult → (stateOne : StateOne) →
      (stateTwo : StateTwo) → related stateOne stateTwo →
        PMF (RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related))
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (stateOne : StateOne) (stateTwo : StateTwo)
    (statesRelated : related stateOne stateTwo) :
    (runOracleProgramsBoundedBridgeTraceCoupling handlerOne handlerTwo related
      handlerRelated first bridgeCoupling second stateOne stateTwo statesRelated).toOuterMeasure
        { output | output.2 = true } =
      ((runOracleProgramRelatedTraceCoupling handlerOne handlerTwo related handlerRelated
        first stateOne stateTwo statesRelated).bind fun firstOutput =>
          (bridgeCoupling firstOutput.result firstOutput.stateOne firstOutput.stateTwo
            firstOutput.statesRelated).map RelatedOrBadBridgeOutput.isBad) true := by
  let joint := runOracleProgramsBoundedBridgeTraceCoupling handlerOne handlerTwo related
    handlerRelated first bridgeCoupling second stateOne stateTwo statesRelated
  calc
    joint.toOuterMeasure { output | output.2 = true } =
        (joint.map Prod.snd).toOuterMeasure {true} := by
      rw [PMF.toOuterMeasure_map_apply]
      rfl
    _ = (joint.map Prod.snd) true := PMF.toOuterMeasure_apply_singleton _ _
    _ = _ := by
      rw [runOracleProgramsBoundedBridgeTraceCoupling_bad]

/-- Result disagreement implies that the bridge recorded a bad event. -/
theorem runOracleProgramsBoundedBridgeTraceCoupling_disagreement_implies_bad
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (bridgeCoupling : FirstResult → (stateOne : StateOne) →
      (stateTwo : StateTwo) → related stateOne stateTwo →
        PMF (RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related))
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (stateOne : StateOne) (stateTwo : StateTwo)
    (statesRelated : related stateOne stateTwo)
    (output :
      ((SecondResult × StateOne × List (oracle.Query × StateOne)) ×
        (SecondResult × StateTwo × List (oracle.Query × StateTwo))) × Bool)
    (member : output ∈
      (runOracleProgramsBoundedBridgeTraceCoupling handlerOne handlerTwo related
        handlerRelated first bridgeCoupling second stateOne stateTwo
        statesRelated).support)
    (different : output.1.1.1 ≠ output.1.2.1) :
    output.2 = true := by
  simp only [runOracleProgramsBoundedBridgeTraceCoupling,
    PMF.mem_support_bind_iff] at member
  rcases member with ⟨firstOutput, _, middleOutput, _, member⟩
  cases middleOutput with
  | related result bridgeStateOne bridgeStateTwo bridgeRelated =>
      simp only [boundedBridgeContinuation, PMF.mem_support_map_iff] at member
      rcases member with ⟨secondOutput, _, rfl⟩
      exact (different rfl).elim
  | bad resultOne bridgeStateOne resultTwo bridgeStateTwo =>
      simp only [boundedBridgeContinuation, PMF.mem_support_map_iff] at member
      rcases member with ⟨secondOutput, _, rfl⟩
      rfl

/-- The result-disagreement mass is at most the recorded bad-event mass. -/
theorem runOracleProgramsBoundedBridgeTraceCoupling_disagreement_le_bad
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (bridgeCoupling : FirstResult → (stateOne : StateOne) →
      (stateTwo : StateTwo) → related stateOne stateTwo →
        PMF (RelatedOrBadBridgeOutput MiddleResult StateOne StateTwo related))
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (stateOne : StateOne) (stateTwo : StateTwo)
    (statesRelated : related stateOne stateTwo) :
    (runOracleProgramsBoundedBridgeTraceCoupling handlerOne handlerTwo related
      handlerRelated first bridgeCoupling second stateOne stateTwo statesRelated).toOuterMeasure
        { output | output.1.1.1 ≠ output.1.2.1 } ≤
      (runOracleProgramsBoundedBridgeTraceCoupling handlerOne handlerTwo related
        handlerRelated first bridgeCoupling second stateOne stateTwo statesRelated).toOuterMeasure
          { output | output.2 = true } := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_le_tsum
  intro output
  by_cases different : output.1.1.1 ≠ output.1.2.1
  · rw [Set.indicator_of_mem different]
    by_cases member : output ∈
        (runOracleProgramsBoundedBridgeTraceCoupling handlerOne handlerTwo related
          handlerRelated first bridgeCoupling second stateOne stateTwo
          statesRelated).support
    · have bad := runOracleProgramsBoundedBridgeTraceCoupling_disagreement_implies_bad
        handlerOne handlerTwo related handlerRelated first bridgeCoupling second
        stateOne stateTwo statesRelated output member different
      rw [Set.indicator_of_mem
        (show output ∈ { output | output.2 = true } from bad)]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr member]
      exact zero_le _
  · rw [Set.indicator_of_notMem different]
    exact zero_le _

end Kriterion.ArgoMAC.Security
