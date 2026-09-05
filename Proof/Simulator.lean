/-
This file defines one simulator state for all ArgoMAC layers.
The paper uses shared state in `gc_optimizations.tex`.
The paper source is https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/gc_optimizations.tex.
-/

import Proof.Linking

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

universe uSample uDomain uRange uIndex uSlot
  uQuery uAnswer uResult uStateOne uStateTwo uFirst uMiddle uSecond

/-- An equivalence preserves the uniform distribution on one finite type. -/
theorem map_uniformOfFintype_equiv
    {Sample : Type uSample} [Fintype Sample] [Nonempty Sample]
    (equivalence : Sample ≃ Sample) :
    (PMF.uniformOfFintype Sample).map equivalence =
      PMF.uniformOfFintype Sample := by
  classical
  apply PMF.ext
  intro output
  rw [PMF.map_apply, PMF.uniformOfFintype_apply]
  simp only [PMF.uniformOfFintype_apply, ← equivalence.symm_apply_eq,
    eq_comm]
  exact (tsum_ite_eq (equivalence.symm output)
    (Inv.inv (Fintype.card Sample : ENNReal))).symm

/-- This predicate requires safety only on one program's reachable query path. -/
def OracleProgramSafe
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uStateOne}
    (handler : OracleHandler oracle State)
    (safe : (query : oracle.Query) → State → Prop) :
    {budget : Nat} → OracleProgram oracle Result budget → State → Prop
  | _, .pure _, _ => True
  | _, .query request next, state =>
      let answered := handler request state
      safe request state ∧ OracleProgramSafe handler safe (next answered.1) answered.2
  | _, .sample _ next, state =>
      ∀ value, OracleProgramSafe handler safe (next value) state

/-- A trace records each reached query and its state. -/
inductive OracleProgramTrace
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uStateOne}
    (handler : OracleHandler oracle State) :
    {budget : Nat} → OracleProgram oracle Result budget → State →
      List (oracle.Query × State) → Prop
  | pure {budget : Nat} (result : PMF Result) (state : State) :
      OracleProgramTrace handler (.pure (budget := budget) result) state []
  | query {budget : Nat} (request : oracle.Query)
      (next : oracle.Answer request → OracleProgram oracle Result budget)
      (state : State) (trace : List (oracle.Query × State))
      (tail : OracleProgramTrace handler
        (next (handler request state).1) (handler request state).2 trace) :
      OracleProgramTrace handler (.query request next) state
        ((request, state) :: trace)
  | sample {budget : Nat} {Sample : Type uResult} (distribution : PMF Sample)
      (next : Sample → OracleProgram oracle Result budget)
      (state : State) (value : Sample) (trace : List (oracle.Query × State))
      (tail : OracleProgramTrace handler (next value) state trace) :
      OracleProgramTrace handler (.sample distribution next) state trace

/-- Every reached trace stays within the program's indexed query budget. -/
theorem OracleProgramTrace.length_le
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uStateOne} (handler : OracleHandler oracle State)
    {budget : Nat} {program : OracleProgram oracle Result budget}
    {state : State} {trace : List (oracle.Query × State)}
    (reached : OracleProgramTrace handler program state trace) :
    trace.length ≤ budget := by
  induction reached with
  | pure => simp
  | query request next state trace tail inductionHypothesis =>
      simpa [Nat.add_comm] using Nat.succ_le_succ inductionHypothesis
  | sample distribution next state value trace tail inductionHypothesis =>
      exact inductionHypothesis

/-- A safe program marks every step of each reached trace as safe. -/
theorem OracleProgramTrace.all_safe
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uStateOne}
    (handler : OracleHandler oracle State)
    (safe : (query : oracle.Query) → State → Prop)
    {budget : Nat} {program : OracleProgram oracle Result budget}
    {state : State} {trace : List (oracle.Query × State)}
    (programSafe : OracleProgramSafe handler safe program state)
    (reached : OracleProgramTrace handler program state trace) :
    ∀ step ∈ trace, safe step.1 step.2 := by
  induction reached with
  | pure => simp
  | query request next state trace tail inductionHypothesis =>
      intro step member
      simp only [List.mem_cons] at member
      rcases member with same | member
      · simpa [same] using programSafe.1
      · exact inductionHypothesis programSafe.2 step member
  | sample distribution next state value trace tail inductionHypothesis =>
      exact inductionHypothesis (programSafe value)

/-- Two reached phases use no more queries than their two indexed budgets. -/
theorem OracleProgramTrace.append_length_le
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult SecondResult : Type uResult} {State : Type uStateOne}
    (handler : OracleHandler oracle State)
    {firstBudget secondBudget : Nat}
    {first : OracleProgram oracle FirstResult firstBudget}
    {second : OracleProgram oracle SecondResult secondBudget}
    {firstState secondState : State}
    {firstTrace secondTrace : List (oracle.Query × State)}
    (firstReached : OracleProgramTrace handler first firstState firstTrace)
    (secondReached : OracleProgramTrace handler second secondState secondTrace) :
    (firstTrace ++ secondTrace).length ≤ firstBudget + secondBudget := by
  rw [List.length_append]
  exact Nat.add_le_add firstReached.length_le secondReached.length_le

/-- This interpreter adds the reached query trace to each program output. -/
noncomputable def runOracleProgramWithTrace
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uStateOne}
    (handler : OracleHandler oracle State) :
    {budget : Nat} → OracleProgram oracle Result budget → State →
      PMF (Result × State × List (oracle.Query × State))
  | _, .pure result, state =>
      result.map fun value => (value, state, [])
  | _, .query request next, state =>
      let answered := handler request state
      (runOracleProgramWithTrace handler (next answered.1) answered.2).map
        fun output => (output.1, output.2.1, (request, state) :: output.2.2)
  | _, .sample distribution next, state =>
      distribution.bind fun value => runOracleProgramWithTrace handler (next value) state

/-- Erasing a trace gives the original program distribution. -/
theorem runOracleProgramWithTrace_erase
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uStateOne} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State) :
    (runOracleProgramWithTrace handler program state).map
        (fun output => (output.1, output.2.1)) =
      program.run handler state := by
  induction program generalizing state with
  | pure result =>
      rw [runOracleProgramWithTrace, OracleProgram.run, PMF.map_comp]
      rfl
  | query request next inductionHypothesis =>
      simp only [runOracleProgramWithTrace, OracleProgram.run, PMF.map_comp]
      change (runOracleProgramWithTrace handler
          (next (handler request state).1) (handler request state).2).map
          (fun output => (output.1, output.2.1)) =
        (next (handler request state).1).run handler (handler request state).2
      exact inductionHypothesis _ _
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTrace, OracleProgram.run, PMF.map_bind]
      congr 1
      funext value
      exact inductionHypothesis value state

/-- Every output in the traced distribution has a valid reached trace. -/
theorem runOracleProgramWithTrace_reached
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uStateOne} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State)
    (output : Result × State × List (oracle.Query × State))
    (member : output ∈ (runOracleProgramWithTrace handler program state).support) :
    OracleProgramTrace handler program state output.2.2 := by
  induction program generalizing state output with
  | pure result =>
      simp only [runOracleProgramWithTrace, PMF.mem_support_map_iff] at member
      rcases member with ⟨value, _, rfl⟩
      exact .pure result state
  | query request next inductionHypothesis =>
      simp only [runOracleProgramWithTrace, PMF.mem_support_map_iff] at member
      rcases member with ⟨tailOutput, tailMember, rfl⟩
      exact .query request next state tailOutput.2.2
        (inductionHypothesis _ _ tailOutput tailMember)
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTrace, PMF.mem_support_bind_iff] at member
      rcases member with ⟨value, _, tailMember⟩
      exact .sample distribution next state value output.2.2
        (inductionHypothesis value state output tailMember)

/-- Every output in the traced distribution stays within the query budget. -/
theorem runOracleProgramWithTrace_length_le
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uStateOne} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State)
    (output : Result × State × List (oracle.Query × State))
    (member : output ∈ (runOracleProgramWithTrace handler program state).support) :
    output.2.2.length ≤ budget :=
  (runOracleProgramWithTrace_reached handler program state output member).length_le

/-- The traced distribution gives zero mass to traces above the query budget. -/
theorem runOracleProgramWithTrace_overBudget_mass
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uStateOne} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State) :
    (runOracleProgramWithTrace handler program state).toOuterMeasure
        { output | budget < output.2.2.length } = 0 := by
  rw [PMF.toOuterMeasure_apply]
  rw [ENNReal.tsum_eq_zero]
  intro output
  simp only [Set.indicator_apply]
  split_ifs with overBudget
  · rw [PMF.apply_eq_zero_iff]
    intro member
    have withinBudget :=
      runOracleProgramWithTrace_length_le handler program state output member
    exact (Nat.not_lt_of_ge withinBudget overBudget).elim
  · rfl

/-- This interpreter appends the traces of two adaptive program phases. -/
noncomputable def runOracleProgramsWithTrace
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {SecondResult : Type uSecond}
    {State : Type uStateOne}
    (handler : OracleHandler oracle State)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (second : FirstResult → OracleProgram oracle SecondResult secondBudget)
    (state : State) :
    PMF (SecondResult × State × List (oracle.Query × State)) :=
  (runOracleProgramWithTrace handler first state).bind fun firstOutput =>
    (runOracleProgramWithTrace handler (second firstOutput.1) firstOutput.2.1).map
      fun secondOutput =>
        (secondOutput.1, secondOutput.2.1, firstOutput.2.2 ++ secondOutput.2.2)

/-- Erasing the appended trace gives the original two-phase distribution. -/
theorem runOracleProgramsWithTrace_erase
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {SecondResult : Type uSecond}
    {State : Type uStateOne}
    (handler : OracleHandler oracle State)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (second : FirstResult → OracleProgram oracle SecondResult secondBudget)
    (state : State) :
    (runOracleProgramsWithTrace handler first second state).map
        (fun output => (output.1, output.2.1)) =
      (first.run handler state).bind fun firstOutput =>
        (second firstOutput.1).run handler firstOutput.2 := by
  rw [runOracleProgramsWithTrace, PMF.map_bind]
  simp_rw [PMF.map_comp]
  change (runOracleProgramWithTrace handler first state).bind
      (fun firstOutput =>
        (runOracleProgramWithTrace handler (second firstOutput.1)
          firstOutput.2.1).map (fun output => (output.1, output.2.1))) = _
  simp_rw [runOracleProgramWithTrace_erase]
  rw [← runOracleProgramWithTrace_erase handler first state]
  rw [PMF.bind_map]
  rfl

/-- Erasing state and trace gives the two-phase result distribution. -/
theorem runOracleProgramsWithTrace_result
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {SecondResult : Type uSecond}
    {State : Type uStateOne} (handler : OracleHandler oracle State)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (second : FirstResult → OracleProgram oracle SecondResult secondBudget)
    (state : State) :
    (runOracleProgramsWithTrace handler first second state).map Prod.fst =
      (first.run handler state).bind fun firstOutput =>
        ((second firstOutput.1).run handler firstOutput.2).map Prod.fst := by
  calc
    (runOracleProgramsWithTrace handler first second state).map Prod.fst =
        ((runOracleProgramsWithTrace handler first second state).map
          (fun output => (output.1, output.2.1))).map Prod.fst := by
      rw [PMF.map_comp]
      rfl
    _ = ((first.run handler state).bind fun firstOutput =>
        (second firstOutput.1).run handler firstOutput.2).map Prod.fst := by
      rw [runOracleProgramsWithTrace_erase]
    _ = (first.run handler state).bind fun firstOutput =>
        ((second firstOutput.1).run handler firstOutput.2).map Prod.fst := by
      rw [PMF.map_bind]

/-- Every two-phase traced output stays within the sum of both budgets. -/
theorem runOracleProgramsWithTrace_length_le
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {SecondResult : Type uSecond}
    {State : Type uStateOne}
    (handler : OracleHandler oracle State)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (second : FirstResult → OracleProgram oracle SecondResult secondBudget)
    (state : State)
    (output : SecondResult × State × List (oracle.Query × State))
    (member : output ∈
      (runOracleProgramsWithTrace handler first second state).support) :
    output.2.2.length ≤ firstBudget + secondBudget := by
  simp only [runOracleProgramsWithTrace, PMF.mem_support_bind_iff] at member
  rcases member with ⟨firstOutput, firstMember, member⟩
  rw [PMF.mem_support_map_iff] at member
  rcases member with ⟨secondOutput, secondMember, rfl⟩
  rw [List.length_append]
  exact Nat.add_le_add
    (runOracleProgramWithTrace_length_le handler first state firstOutput firstMember)
    (runOracleProgramWithTrace_length_le handler (second firstOutput.1)
      firstOutput.2.1 secondOutput secondMember)

/-- Two-phase traces above the summed query budget have zero mass. -/
theorem runOracleProgramsWithTrace_overBudget_mass
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {SecondResult : Type uSecond}
    {State : Type uStateOne}
    (handler : OracleHandler oracle State)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (second : FirstResult → OracleProgram oracle SecondResult secondBudget)
    (state : State) :
    (runOracleProgramsWithTrace handler first second state).toOuterMeasure
        { output | firstBudget + secondBudget < output.2.2.length } = 0 := by
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_eq_zero]
  intro output
  simp only [Set.indicator_apply]
  split_ifs with overBudget
  · rw [PMF.apply_eq_zero_iff]
    intro member
    have withinBudget :=
      runOracleProgramsWithTrace_length_le handler first second state output member
    exact (Nat.not_lt_of_ge withinBudget overBudget).elim
  · rfl

/-- This two-phase interpreter permits one query-free state bridge. -/
noncomputable def runOracleProgramsWithBridgeTrace
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {State : Type uStateOne} (handler : OracleHandler oracle State)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (bridge : FirstResult → State → PMF (MiddleResult × State))
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (state : State) :
    PMF (SecondResult × State × List (oracle.Query × State)) :=
  (runOracleProgramWithTrace handler first state).bind fun firstOutput =>
    (bridge firstOutput.1 firstOutput.2.1).bind fun middleOutput =>
      (runOracleProgramWithTrace handler
        (second firstOutput.1 middleOutput.1) middleOutput.2).map
          fun secondOutput =>
            (secondOutput.1, secondOutput.2.1,
              firstOutput.2.2 ++ secondOutput.2.2)

/-- Erasing a bridged trace gives the original bridged distribution. -/
theorem runOracleProgramsWithBridgeTrace_erase
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {State : Type uStateOne} (handler : OracleHandler oracle State)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (bridge : FirstResult → State → PMF (MiddleResult × State))
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (state : State) :
    (runOracleProgramsWithBridgeTrace handler first bridge second state).map
        (fun output => (output.1, output.2.1)) =
      (first.run handler state).bind fun firstOutput =>
        (bridge firstOutput.1 firstOutput.2).bind fun middleOutput =>
          (second firstOutput.1 middleOutput.1).run handler middleOutput.2 := by
  rw [runOracleProgramsWithBridgeTrace, PMF.map_bind]
  simp_rw [PMF.map_bind, PMF.map_comp]
  change (runOracleProgramWithTrace handler first state).bind
      (fun firstOutput =>
        (bridge firstOutput.1 firstOutput.2.1).bind fun middleOutput =>
          (runOracleProgramWithTrace handler
            (second firstOutput.1 middleOutput.1) middleOutput.2).map
              (fun output => (output.1, output.2.1))) = _
  simp_rw [runOracleProgramWithTrace_erase]
  rw [← runOracleProgramWithTrace_erase handler first state]
  rw [PMF.bind_map]
  rfl

/-- Erasing state and trace gives the bridged result distribution. -/
theorem runOracleProgramsWithBridgeTrace_result
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {State : Type uStateOne} (handler : OracleHandler oracle State)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (bridge : FirstResult → State → PMF (MiddleResult × State))
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (state : State) :
    (runOracleProgramsWithBridgeTrace handler first bridge second state).map Prod.fst =
      (first.run handler state).bind fun firstOutput =>
        (bridge firstOutput.1 firstOutput.2).bind fun middleOutput =>
          ((second firstOutput.1 middleOutput.1).run handler middleOutput.2).map
            Prod.fst := by
  calc
    (runOracleProgramsWithBridgeTrace handler first bridge second state).map Prod.fst =
        ((runOracleProgramsWithBridgeTrace handler first bridge second state).map
          (fun output => (output.1, output.2.1))).map Prod.fst := by
      rw [PMF.map_comp]
      rfl
    _ = ((first.run handler state).bind fun firstOutput =>
        (bridge firstOutput.1 firstOutput.2).bind fun middleOutput =>
          (second firstOutput.1 middleOutput.1).run handler middleOutput.2).map Prod.fst := by
      rw [runOracleProgramsWithBridgeTrace_erase]
    _ = (first.run handler state).bind fun firstOutput =>
        (bridge firstOutput.1 firstOutput.2).bind fun middleOutput =>
          ((second firstOutput.1 middleOutput.1).run handler middleOutput.2).map
            Prod.fst := by
      rw [PMF.map_bind]
      congr 1
      funext firstOutput
      rw [PMF.map_bind]

/-- A query-free bridge does not increase the two-phase trace budget. -/
theorem runOracleProgramsWithBridgeTrace_length_le
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {State : Type uStateOne} (handler : OracleHandler oracle State)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (bridge : FirstResult → State → PMF (MiddleResult × State))
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (state : State)
    (output : SecondResult × State × List (oracle.Query × State))
    (member : output ∈
      (runOracleProgramsWithBridgeTrace handler first bridge second state).support) :
    output.2.2.length ≤ firstBudget + secondBudget := by
  simp only [runOracleProgramsWithBridgeTrace, PMF.mem_support_bind_iff] at member
  rcases member with ⟨firstOutput, firstMember, middleMember⟩
  rcases middleMember with ⟨middleOutput, _, member⟩
  rw [PMF.mem_support_map_iff] at member
  rcases member with ⟨secondOutput, secondMember, rfl⟩
  rw [List.length_append]
  exact Nat.add_le_add
    (runOracleProgramWithTrace_length_le handler first state firstOutput firstMember)
    (runOracleProgramWithTrace_length_le handler
      (second firstOutput.1 middleOutput.1) middleOutput.2 secondOutput secondMember)

/-- Bridged traces above both query budgets have zero mass. -/
theorem runOracleProgramsWithBridgeTrace_overBudget_mass
    {oracle : OracleSpec.{uQuery, uAnswer}}
    {FirstResult : Type uFirst} {MiddleResult : Type uMiddle}
    {SecondResult : Type uSecond}
    {State : Type uStateOne} (handler : OracleHandler oracle State)
    {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle FirstResult firstBudget)
    (bridge : FirstResult → State → PMF (MiddleResult × State))
    (second : FirstResult → MiddleResult →
      OracleProgram oracle SecondResult secondBudget)
    (state : State) :
    (runOracleProgramsWithBridgeTrace handler first bridge second state).toOuterMeasure
        { output | firstBudget + secondBudget < output.2.2.length } = 0 := by
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_eq_zero]
  intro output
  simp only [Set.indicator_apply]
  split_ifs with overBudget
  · rw [PMF.apply_eq_zero_iff]
    intro member
    have withinBudget := runOracleProgramsWithBridgeTrace_length_le
      handler first bridge second state output member
    exact (Nat.not_lt_of_ge withinBudget overBudget).elim
  · rfl

/-- A path-safe handler equivalence lifts through one oracle program. -/
theorem oracleProgram_run_stateEquiv_of_safe
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (stateEquiv : StateOne ≃ StateTwo)
    (safe : (query : oracle.Query) → StateOne → Prop)
    (handlerEquiv : ∀ query state, safe query state →
      (handlerOne query state).1 =
          (handlerTwo query (stateEquiv state)).1 ∧
        stateEquiv (handlerOne query state).2 =
          (handlerTwo query (stateEquiv state)).2)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (state : StateOne) (programSafe : OracleProgramSafe handlerOne safe program state) :
    (program.run handlerOne state).map
        (fun output => (output.1, stateEquiv output.2)) =
      program.run handlerTwo (stateEquiv state) := by
  induction program generalizing state with
  | pure result =>
      rw [OracleProgram.run, OracleProgram.run, PMF.map_comp]
      congr 1
  | query request next inductionHypothesis =>
      simp only [OracleProgram.run]
      have related := handlerEquiv request state programSafe.1
      have tailSafe : OracleProgramSafe handlerOne safe
          (next (handlerTwo request (stateEquiv state)).1)
          (handlerOne request state).2 := by
        rw [← related.1]
        exact programSafe.2
      rw [show (handlerOne request state).1 =
        (handlerTwo request (stateEquiv state)).1 from related.1]
      rw [inductionHypothesis _ _ tailSafe]
      rw [related.2]
  | sample distribution next inductionHypothesis =>
      simp only [OracleProgram.run, PMF.map_bind]
      congr 1
      funext sample
      exact inductionHypothesis sample state (programSafe sample)

/-- A handler equivalence lifts through every oracle program. -/
theorem oracleProgram_run_stateEquiv
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (stateEquiv : StateOne ≃ StateTwo)
    (handlerEquiv : ∀ query state,
      (handlerOne query state).1 =
          (handlerTwo query (stateEquiv state)).1 ∧
        stateEquiv (handlerOne query state).2 =
          (handlerTwo query (stateEquiv state)).2)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (state : StateOne) :
    (program.run handlerOne state).map
        (fun output => (output.1, stateEquiv output.2)) =
      program.run handlerTwo (stateEquiv state) := by
  induction program generalizing state with
  | pure result =>
      rw [OracleProgram.run, OracleProgram.run, PMF.map_comp]
      congr 1
  | query request next inductionHypothesis =>
      simp only [OracleProgram.run]
      have related := handlerEquiv request state
      rw [show (handlerOne request state).1 =
        (handlerTwo request (stateEquiv state)).1 from related.1]
      rw [inductionHypothesis]
      rw [related.2]
  | sample distribution next inductionHypothesis =>
      simp only [OracleProgram.run, PMF.map_bind]
      congr 1
      funext sample
      exact inductionHypothesis sample state

/-- Related handlers give the same program result distribution. -/
theorem oracleProgram_run_result_of_related
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (stateOne : StateOne) (stateTwo : StateTwo)
    (statesRelated : related stateOne stateTwo) :
    (program.run handlerOne stateOne).map Prod.fst =
      (program.run handlerTwo stateTwo).map Prod.fst := by
  induction program generalizing stateOne stateTwo with
  | pure result =>
      simp only [OracleProgram.run, PMF.map_comp]
      congr 1
  | query request next inductionHypothesis =>
      simp only [OracleProgram.run]
      have nextRelated := handlerRelated request stateOne stateTwo statesRelated
      rw [nextRelated.1]
      exact inductionHypothesis _ _ _ nextRelated.2
  | sample distribution next inductionHypothesis =>
      simp only [OracleProgram.run, PMF.map_bind]
      congr 1
      funext sample
      exact inductionHypothesis sample stateOne stateTwo statesRelated

/-- Replay one query list and record the state before each query. -/
def replayQueryTrace
    {oracle : OracleSpec.{uQuery, uAnswer}} {StateOne : Type uStateOne}
    {StateTwo : Type uStateTwo} (handler : OracleHandler oracle StateTwo) :
    StateTwo → List (oracle.Query × StateOne) →
      StateTwo × List (oracle.Query × StateTwo)
  | state, [] => (state, [])
  | state, (query, _) :: remaining =>
      let tail := replayQueryTrace handler (handler query state).2 remaining
      (tail.1, (query, state) :: tail.2)

/-- Replay a traced output from a second initial state. -/
def replayTracedOutput
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handler : OracleHandler oracle StateTwo) (state : StateTwo) :
    Result × StateOne × List (oracle.Query × StateOne) →
      Result × StateTwo × List (oracle.Query × StateTwo) :=
  fun output =>
    let replayed := replayQueryTrace handler state output.2.2
    (output.1, replayed.1, replayed.2)

/-- Replay composes over two consecutive query traces. -/
theorem replayQueryTrace_append
    {oracle : OracleSpec.{uQuery, uAnswer}} {StateOne : Type uStateOne}
    {StateTwo : Type uStateTwo} (handler : OracleHandler oracle StateTwo)
    (state : StateTwo) (first second : List (oracle.Query × StateOne)) :
    replayQueryTrace handler state (first ++ second) =
      let firstReplay := replayQueryTrace handler state first
      let secondReplay := replayQueryTrace handler firstReplay.1 second
      (secondReplay.1, firstReplay.2 ++ secondReplay.2) := by
  induction first generalizing state with
  | nil => rfl
  | cons current remaining inductionHypothesis =>
      simp only [List.cons_append, replayQueryTrace]
      rw [inductionHypothesis]

/-- Replay preserves the number of reached queries. -/
theorem replayQueryTrace_length
    {oracle : OracleSpec.{uQuery, uAnswer}} {StateOne : Type uStateOne}
    {StateTwo : Type uStateTwo} (handler : OracleHandler oracle StateTwo)
    (state : StateTwo) (trace : List (oracle.Query × StateOne)) :
    (replayQueryTrace handler state trace).2.length = trace.length := by
  induction trace generalizing state with
  | nil => rfl
  | cons current remaining inductionHypothesis =>
      simp only [replayQueryTrace, List.length_cons]
      rw [inductionHypothesis]

/-- Replay preserves the ordered public query list. -/
theorem replayQueryTrace_queries
    {oracle : OracleSpec.{uQuery, uAnswer}} {StateOne : Type uStateOne}
    {StateTwo : Type uStateTwo} (handler : OracleHandler oracle StateTwo)
    (state : StateTwo) (trace : List (oracle.Query × StateOne)) :
    (replayQueryTrace handler state trace).2.map Prod.fst = trace.map Prod.fst := by
  induction trace generalizing state with
  | nil => rfl
  | cons current remaining inductionHypothesis =>
      simp only [replayQueryTrace, List.map_cons, List.cons.injEq, true_and]
      exact inductionHypothesis _

/-- Trace replay transports a related handler run exactly. -/
theorem runOracleProgramWithTrace_replay_of_related
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {StateOne : Type uStateOne} {StateTwo : Type uStateTwo}
    (handlerOne : OracleHandler oracle StateOne)
    (handlerTwo : OracleHandler oracle StateTwo)
    (related : StateOne → StateTwo → Prop)
    (handlerRelated : ∀ query stateOne stateTwo, related stateOne stateTwo →
      (handlerOne query stateOne).1 = (handlerTwo query stateTwo).1 ∧
        related (handlerOne query stateOne).2 (handlerTwo query stateTwo).2)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (stateOne : StateOne) (stateTwo : StateTwo)
    (statesRelated : related stateOne stateTwo) :
    (runOracleProgramWithTrace handlerOne program stateOne).map
        (replayTracedOutput handlerTwo stateTwo) =
      runOracleProgramWithTrace handlerTwo program stateTwo := by
  induction program generalizing stateOne stateTwo with
  | pure result =>
      simp [runOracleProgramWithTrace, replayTracedOutput, replayQueryTrace,
        PMF.map_comp, Function.comp_def]
  | query request next inductionHypothesis =>
      simp only [runOracleProgramWithTrace]
      have nextRelated := handlerRelated request stateOne stateTwo statesRelated
      rw [nextRelated.1]
      rw [← inductionHypothesis _ (handlerOne request stateOne).2
        (handlerTwo request stateTwo).2 nextRelated.2]
      rw [PMF.map_comp]
      rw [PMF.map_comp]
      congr 1
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTrace, PMF.map_bind]
      congr 1
      funext sample
      exact inductionHypothesis sample stateOne stateTwo statesRelated

/-- This value identifies one layer in the composed circuit. -/
inductive Layer
  | input
  | curve
  | point
deriving DecidableEq

/-- This value identifies one label wire. -/
structure Wire where
  layer : Layer
  position : Nat
  branch : Bool
deriving DecidableEq

/-- This value records one pending or committed wire label. -/
structure LabelCommitment where
  wire : Wire
  label : Block
  pending : Bool
deriving DecidableEq

/-- Distinct wires use distinct labels. -/
def DistinctCommitments (commitments : List LabelCommitment) : Prop :=
  commitments.Pairwise fun first second =>
    first.wire ≠ second.wire ∧ first.label ≠ second.label

/-- This value contains the inputs for the exact non-black-box key relation. -/
structure LinkingState where
  bridgeKey : BaseField
  sourceKey : InputMacKey

/-- This value records one random-oracle query. -/
structure HashRecord where
  input : BaseField
  output : Block × Block

/-- This state is shared by every simulator layer. -/
structure SimulatorState where
  fixedOracle : PermutationOracle Pipeline.FixedKeyIndex Block
  encOracle : PermutationOracle EncPRF.PermutationIndex Block
  hashOracle : EncPRF.HashOracle
  fixedTranscript : List (PermutationRecord Pipeline.FixedKeyIndex Block)
  encTranscript : List (PermutationRecord EncPRF.PermutationIndex Block)
  hashTranscript : List HashRecord
  commitments : List LabelCommitment
  linking : Option LinkingState
  bad : Bool

/-- This relation connects one permutation transcript to its oracle. -/
def PermutationTranscriptMatches (oracle : PermutationOracle Index Block)
    (history : List (PermutationRecord Index Block)) : Prop :=
  ∀ record ∈ history, oracle.permutation record.index record.domain = record.range

/-- This relation connects one random-oracle transcript to its oracle. -/
def HashTranscriptMatches (oracle : EncPRF.HashOracle) (history : List HashRecord) : Prop :=
  ∀ record ∈ history, oracle record.input = record.output

/-- A fresh random-oracle input does not occur in the transcript. -/
def FreshHashInput (history : List HashRecord) (input : BaseField) : Prop :=
  ∀ record ∈ history, record.input ≠ input

/-- This executable check tests random-oracle input freshness. -/
def freshHashInputCheck (history : List HashRecord) (input : BaseField) : Bool :=
  history.all fun record => decide (record.input ≠ input)

theorem freshHashInputCheck_eq_true (history : List HashRecord) (input : BaseField) :
    freshHashInputCheck history input = true ↔ FreshHashInput history input := by
  rw [freshHashInputCheck, List.all_eq_true]
  constructor
  · intro check record member
    exact of_decide_eq_true (check record member)
  · intro fresh record member
    exact decide_eq_true (fresh record member)

/-- This operation programs one permutation point by swapping two range values. -/
def programPermutation [DecidableEq Index] (oracle : PermutationOracle Index Block)
    (index : Index) (input output : Block) : PermutationOracle Index Block := {
  permutation := fun current => if current = index then
    (oracle.permutation current).trans
      (Equiv.swap (oracle.permutation current input) output)
  else oracle.permutation current
}

/-- This map programs one point and returns its old range value. -/
def swapProgramPair [DecidableEq Index]
    (index : Index) (input : Block) :
    PermutationOracle Index Block × Block →
      PermutationOracle Index Block × Block :=
  fun sample =>
    (programPermutation sample.1 index input sample.2,
      sample.1.permutation index input)

theorem programPermutation_apply [DecidableEq Index]
    (oracle : PermutationOracle Index Block) (index : Index) (input output : Block) :
    (programPermutation oracle index input output).permutation index input = output := by
  simp [programPermutation, Equiv.trans_apply, Equiv.swap_apply_left]

theorem programPermutation_symm [DecidableEq Index]
    (oracle : PermutationOracle Index Block) (index : Index) (input output : Block) :
    ((programPermutation oracle index input output).permutation index).symm output = input := by
  rw [Equiv.symm_apply_eq]
  exact (programPermutation_apply oracle index input output).symm

/-- Applying the swap-programming map two times restores its input. -/
theorem swapProgramPair_involutive [DecidableEq Index]
    (index : Index) (input : Block) :
    Function.Involutive (swapProgramPair index input) := by
  intro sample
  rcases sample with ⟨oracle, target⟩
  refine Prod.ext ?_ ?_
  · change programPermutation
      (programPermutation oracle index input target) index input
        (oracle.permutation index input) = oracle
    cases oracle with
    | mk permutation =>
      change PermutationOracle.mk _ = PermutationOracle.mk permutation
      rw [PermutationOracle.mk.injEq]
      funext current
      by_cases sameIndex : current = index
      · subst current
        apply Equiv.ext
        intro value
        simp only [programPermutation, if_pos, Equiv.trans_apply,
          Equiv.swap_apply_left]
        rw [Equiv.swap_comm target]
        exact Equiv.swap_apply_self _ _ _
      · simp [programPermutation, sameIndex]
  · exact programPermutation_apply oracle index input target

/-- This equivalence contains the swap-programming map. -/
noncomputable def swapProgramEquiv [DecidableEq Index]
    (index : Index) (input : Block) :
    (PermutationOracle Index Block × Block) ≃
      (PermutationOracle Index Block × Block) :=
  (swapProgramPair_involutive index input).toPerm

/-- Fresh swap programming preserves the uniform joint distribution exactly. -/
theorem map_uniform_swapProgramPair
    [Fintype Index] [DecidableEq Index]
    (index : Index) (input : Block) :
    (PMF.uniformOfFintype (PermutationOracle Index Block × Block)).map
        (swapProgramPair index input) =
      PMF.uniformOfFintype (PermutationOracle Index Block × Block) :=
  map_uniformOfFintype_equiv (swapProgramEquiv (Index := Index) index input)

/-- This map programs one point from one coordinate of a target tape. -/
def swapProgramTapeStep {Index : Type uIndex} {Slot : Type uSlot}
    [DecidableEq Index] [DecidableEq Slot]
    (index : Index) (input : Block) (slot : Slot) :
    PermutationOracle Index Block × (Slot → Block) →
      PermutationOracle Index Block × (Slot → Block) :=
  fun sample =>
    (programPermutation sample.1 index input (sample.2 slot),
      Function.update sample.2 slot (sample.1.permutation index input))

/-- Applying one target-tape step two times restores its input. -/
theorem swapProgramTapeStep_involutive
    {Index : Type uIndex} {Slot : Type uSlot}
    [DecidableEq Index] [DecidableEq Slot]
    (index : Index) (input : Block) (slot : Slot) :
    Function.Involutive (swapProgramTapeStep index input slot) := by
  intro sample
  rcases sample with ⟨oracle, tape⟩
  refine Prod.ext ?_ ?_
  · simp only [swapProgramTapeStep, Function.update_self]
    exact congrArg Prod.fst
      (swapProgramPair_involutive index input (oracle, tape slot))
  · funext current
    by_cases sameSlot : current = slot
    · subst current
      simp [swapProgramTapeStep, programPermutation_apply]
    · simp [swapProgramTapeStep, sameSlot]

/-- This equivalence contains one target-tape step. -/
noncomputable def swapProgramTapeStepEquiv
    {Index : Type uIndex} {Slot : Type uSlot}
    [DecidableEq Index] [DecidableEq Slot]
    (index : Index) (input : Block) (slot : Slot) :
    (PermutationOracle Index Block × (Slot → Block)) ≃
      (PermutationOracle Index Block × (Slot → Block)) :=
  (swapProgramTapeStep_involutive index input slot).toPerm

/-- One target-tape step preserves its uniform joint distribution exactly. -/
theorem map_uniform_swapProgramTapeStep
    {Index : Type uIndex} {Slot : Type uSlot}
    [Fintype Index] [DecidableEq Index]
    [Fintype Slot] [DecidableEq Slot]
    (index : Index) (input : Block) (slot : Slot) :
    (PMF.uniformOfFintype
      (PermutationOracle Index Block × (Slot → Block))).map
        (swapProgramTapeStep index input slot) =
      PMF.uniformOfFintype
        (PermutationOracle Index Block × (Slot → Block)) :=
  map_uniformOfFintype_equiv
    (swapProgramTapeStepEquiv index input slot)

/-- This equivalence composes a fixed list of target-tape steps. -/
noncomputable def swapProgramTapeScheduleEquiv
    {Index : Type uIndex} {Slot : Type uSlot}
    [DecidableEq Index] [DecidableEq Slot] :
    List (Index × Block × Slot) →
      (PermutationOracle Index Block × (Slot → Block)) ≃
        (PermutationOracle Index Block × (Slot → Block))
  | [] => Equiv.refl _
  | point :: rest =>
      (swapProgramTapeStepEquiv point.1 point.2.1 point.2.2).trans
        (swapProgramTapeScheduleEquiv rest)

/-- A fixed swap-programming schedule preserves the uniform joint tape exactly. -/
theorem map_uniform_swapProgramTapeSchedule
    {Index : Type uIndex} {Slot : Type uSlot}
    [Fintype Index] [DecidableEq Index]
    [Fintype Slot] [DecidableEq Slot]
    (schedule : List (Index × Block × Slot)) :
    (PMF.uniformOfFintype
      (PermutationOracle Index Block × (Slot → Block))).map
        (swapProgramTapeScheduleEquiv schedule) =
      PMF.uniformOfFintype
        (PermutationOracle Index Block × (Slot → Block)) :=
  map_uniformOfFintype_equiv
    (swapProgramTapeScheduleEquiv schedule)

/-- This map programs one function point and returns its old output. -/
def updateProgramPair {Domain : Type uDomain} {Range : Type uRange}
    [DecidableEq Domain] (input : Domain) :
    (Domain → Range) × Range → (Domain → Range) × Range :=
  fun sample =>
    (Function.update sample.1 input sample.2, sample.1 input)

/-- Applying the function-programming map two times restores its input. -/
theorem updateProgramPair_involutive
    {Domain : Type uDomain} {Range : Type uRange} [DecidableEq Domain]
    (input : Domain) : Function.Involutive
      (updateProgramPair (Range := Range) input) := by
  intro sample
  rcases sample with ⟨oracle, target⟩
  refine Prod.ext ?_ ?_
  · funext current
    by_cases sameInput : current = input
    · subst current
      simp [updateProgramPair]
    · simp [updateProgramPair]
  · simp [updateProgramPair]

/-- This equivalence contains the function-programming map. -/
noncomputable def updateProgramEquiv
    {Domain : Type uDomain} {Range : Type uRange} [DecidableEq Domain]
    (input : Domain) :
    ((Domain → Range) × Range) ≃ ((Domain → Range) × Range) :=
  (updateProgramPair_involutive (Range := Range) input).toPerm

/-- Fresh function programming preserves the uniform joint distribution exactly. -/
theorem map_uniform_updateProgramPair
    {Domain : Type uDomain} {Range : Type uRange}
    [Fintype Domain] [DecidableEq Domain] [Fintype Range] [Nonempty Range]
    (input : Domain) :
    (PMF.uniformOfFintype ((Domain → Range) × Range)).map
        (updateProgramPair input) =
      PMF.uniformOfFintype ((Domain → Range) × Range) :=
  map_uniformOfFintype_equiv
    (updateProgramEquiv (Range := Range) input)

/-- A different function query has the same answer after programming. -/
theorem updateProgramPair_apply_of_ne
    {Domain : Type uDomain} {Range : Type uRange} [DecidableEq Domain]
    (oracle : Domain → Range) (input : Domain) (target : Range)
    (current : Domain) (different : current ≠ input) :
    (updateProgramPair input (oracle, target)).1 current = oracle current := by
  simp [updateProgramPair, different]

/-- This map embeds one fixed-key swap into the complete simulator state. -/
def swapFixedStateTarget (index : Pipeline.FixedKeyIndex) (input : Block) :
    SimulatorState × Block → SimulatorState × Block :=
  fun sample =>
    ({ sample.1 with
        fixedOracle := programPermutation sample.1.fixedOracle index input sample.2 },
      sample.1.fixedOracle.permutation index input)

/-- The fixed-key state swap is an involution. -/
theorem swapFixedStateTarget_involutive
    (index : Pipeline.FixedKeyIndex) (input : Block) :
    Function.Involutive (swapFixedStateTarget index input) := by
  intro sample
  rcases sample with ⟨state, target⟩
  have pairRestored := swapProgramPair_involutive index input
    (state.fixedOracle, target)
  refine Prod.ext ?_ ?_
  · cases state with
    | mk fixedOracle encOracle hashOracle fixedTranscript encTranscript
        hashTranscript commitments linking bad =>
      change SimulatorState.mk _ encOracle hashOracle fixedTranscript
        encTranscript hashTranscript commitments linking bad =
          SimulatorState.mk fixedOracle encOracle hashOracle fixedTranscript
            encTranscript hashTranscript commitments linking bad
      rw [SimulatorState.mk.injEq]
      exact ⟨congrArg Prod.fst pairRestored, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl⟩
  · change (swapProgramPair index input
      (swapProgramPair index input (state.fixedOracle, target))).2 = target
    exact congrArg Prod.snd pairRestored

/-- This equivalence contains one fixed-key swap on simulator state. -/
noncomputable def swapFixedStateTargetEquiv
    (index : Pipeline.FixedKeyIndex) (input : Block) :
    (SimulatorState × Block) ≃ (SimulatorState × Block) :=
  (swapFixedStateTarget_involutive index input).toPerm

/-- This map embeds one hash update into the complete simulator state. -/
def swapHashStateTarget (input : BaseField) :
    SimulatorState × (Block × Block) →
      SimulatorState × (Block × Block) :=
  fun sample =>
    ({ sample.1 with
        hashOracle := Function.update sample.1.hashOracle input sample.2 },
      sample.1.hashOracle input)

/-- The hash state swap is an involution. -/
theorem swapHashStateTarget_involutive (input : BaseField) :
    Function.Involutive (swapHashStateTarget input) := by
  intro sample
  rcases sample with ⟨state, target⟩
  have pairRestored := updateProgramPair_involutive input
    (state.hashOracle, target)
  refine Prod.ext ?_ ?_
  · cases state with
    | mk fixedOracle encOracle hashOracle fixedTranscript encTranscript
        hashTranscript commitments linking bad =>
      change SimulatorState.mk fixedOracle encOracle _ fixedTranscript
        encTranscript hashTranscript commitments linking bad =
          SimulatorState.mk fixedOracle encOracle hashOracle fixedTranscript
            encTranscript hashTranscript commitments linking bad
      rw [SimulatorState.mk.injEq]
      exact ⟨rfl, rfl, congrArg Prod.fst pairRestored, rfl, rfl,
        rfl, rfl, rfl, rfl⟩
  · change (updateProgramPair input
      (updateProgramPair input (state.hashOracle, target))).2 = target
    exact congrArg Prod.snd pairRestored

/-- This equivalence contains one hash update on simulator state. -/
noncomputable def swapHashStateTargetEquiv (input : BaseField) :
    (SimulatorState × (Block × Block)) ≃
      (SimulatorState × (Block × Block)) :=
  (swapHashStateTarget_involutive input).toPerm

/-- This type contains one fresh hash target that matches a fixed transcript. -/
def FreshHashProgrammingSample (history : List HashRecord)
    (input : BaseField) :=
  { sample : EncPRF.HashOracle × (Block × Block) //
    HashTranscriptMatches sample.1 history ∧ FreshHashInput history input }

/-- A matching hash oracle and one fresh input give a nonempty fiber. -/
theorem freshHashProgrammingSample_nonempty (history : List HashRecord)
    (input : BaseField) (oracle : EncPRF.HashOracle)
    (matchesTranscript : HashTranscriptMatches oracle history)
    (fresh : FreshHashInput history input) :
    Nonempty (FreshHashProgrammingSample history input) :=
  ⟨⟨(oracle, (0, 0)), matchesTranscript, fresh⟩⟩

noncomputable instance freshHashProgrammingSampleFintype
    (history : List HashRecord) (input : BaseField) :
    Fintype (FreshHashProgrammingSample history input) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun sample : EncPRF.HashOracle × (Block × Block) =>
      HashTranscriptMatches sample.1 history ∧ FreshHashInput history input) (by simp)

/-- This map swaps one fresh hash target inside a fixed transcript fiber. -/
def swapFreshHashProgrammingSample (history : List HashRecord)
    (input : BaseField) :
    FreshHashProgrammingSample history input →
      FreshHashProgrammingSample history input := by
  intro sample
  refine ⟨updateProgramPair input sample.1, ?_⟩
  constructor
  · intro record member
    change Function.update sample.1.1 input sample.1.2 record.input = record.output
    rw [Function.update_of_ne (sample.2.2 record member)]
    exact sample.2.1 record member
  · exact sample.2.2

/-- The fresh hash swap is an involution inside its transcript fiber. -/
theorem swapFreshHashProgrammingSample_involutive
    (history : List HashRecord) (input : BaseField) :
    Function.Involutive (swapFreshHashProgrammingSample history input) := by
  intro sample
  apply Subtype.ext
  exact updateProgramPair_involutive input sample.1

/-- This equivalence contains the fresh hash swap in one transcript fiber. -/
noncomputable def swapFreshHashProgrammingSampleEquiv
    (history : List HashRecord) (input : BaseField) :
    FreshHashProgrammingSample history input ≃
      FreshHashProgrammingSample history input :=
  (swapFreshHashProgrammingSample_involutive history input).toPerm

/-- Fresh hash programming preserves a uniform transcript fiber exactly. -/
theorem map_uniform_swapFreshHashProgrammingSample
    (history : List HashRecord) (input : BaseField)
    [Nonempty (FreshHashProgrammingSample history input)] :
    (PMF.uniformOfFintype
      (FreshHashProgrammingSample history input)).map
        (swapFreshHashProgrammingSample history input) =
      PMF.uniformOfFintype
        (FreshHashProgrammingSample history input) :=
  map_uniformOfFintype_equiv
    (swapFreshHashProgrammingSampleEquiv history input)

/-- Fresh programming preserves one prior permutation pair. -/
theorem programPermutation_preserves [DecidableEq Index]
    (oracle : PermutationOracle Index Block) (index : Index) (input output : Block)
    (record : PermutationRecord Index Block)
    (recordMatches : oracle.permutation record.index record.domain = record.range)
    (fresh : record.index = index → record.domain ≠ input ∧ record.range ≠ output) :
    (programPermutation oracle index input output).permutation record.index record.domain =
      record.range := by
  by_cases sameIndex : record.index = index
  · have different := fresh sameIndex
    have differentImage : record.range ≠ oracle.permutation record.index input := by
      rw [← recordMatches]
      exact (oracle.permutation record.index).injective.ne different.1
    simp only [programPermutation, if_pos sameIndex, Equiv.trans_apply]
    rw [recordMatches]
    exact Equiv.swap_apply_of_ne_of_ne differentImage different.2
  · simp [programPermutation, sameIndex, recordMatches]

/-- A fresh forward query has the same answer after swap programming. -/
theorem programPermutation_forward_eq_of_fresh [DecidableEq Index]
    (oracle : PermutationOracle Index Block) (index : Index)
    (input target : Block) (current : Index) (domain : Block)
    (fresh : current = index →
      domain ≠ input ∧ oracle.permutation current domain ≠ target) :
    (programPermutation oracle index input target).permutation current domain =
      oracle.permutation current domain := by
  exact programPermutation_preserves oracle index input target
    (PermutationRecord.mk .forward .adversary current domain
      (oracle.permutation current domain)) rfl fresh

/-- A fresh inverse query has the same answer after swap programming. -/
theorem programPermutation_inverse_eq_of_fresh [DecidableEq Index]
    (oracle : PermutationOracle Index Block) (index : Index)
    (input target : Block) (current : Index) (range : Block)
    (fresh : current = index →
      range ≠ oracle.permutation current input ∧ range ≠ target) :
    ((programPermutation oracle index input target).permutation current).symm range =
      (oracle.permutation current).symm range := by
  let domain := (oracle.permutation current).symm range
  have domainFresh : current = index → domain ≠ input ∧ range ≠ target := by
    intro sameIndex
    have freshAtIndex := fresh sameIndex
    constructor
    · intro sameDomain
      apply freshAtIndex.1
      calc
        range = oracle.permutation current domain :=
          (oracle.permutation current).apply_symm_apply range |>.symm
        _ = oracle.permutation current input := congrArg _ sameDomain
    · exact freshAtIndex.2
  have preserved :
      (programPermutation oracle index input target).permutation current domain = range :=
    programPermutation_preserves oracle index input target
      (PermutationRecord.mk .inverse .adversary current domain range)
      (Equiv.apply_symm_apply (oracle.permutation current) range) domainFresh
  apply (programPermutation oracle index input target).permutation current |>.injective
  rw [Equiv.apply_symm_apply, preserved]

/-- This type contains one fresh programming pair that matches a fixed transcript. -/
def FreshProgrammingSample {Index : Type uIndex} [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block) :=
  { sample : PermutationOracle Index Block × Block //
    PermutationTranscriptMatches sample.1 history ∧
      FreshPermutationPair history index input sample.2 }

/-- A matching oracle and one fresh domain give a nonempty fiber. -/
theorem freshProgrammingSample_nonempty
    {Index : Type uIndex} [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block) (oracle : PermutationOracle Index Block)
    (matchesTranscript : PermutationTranscriptMatches oracle history)
    (freshDomain : ∀ record ∈ history, record.index = index →
      record.domain ≠ input) :
    Nonempty (FreshProgrammingSample history index input) := by
  refine ⟨⟨(oracle, oracle.permutation index input), matchesTranscript, ?_⟩⟩
  intro record member sameIndex
  constructor
  · exact freshDomain record member sameIndex
  · intro sameRange
    apply freshDomain record member sameIndex
    apply (oracle.permutation record.index).injective
    rw [matchesTranscript record member]
    simpa [sameIndex] using sameRange

noncomputable instance freshProgrammingSampleFintype
    {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block) :
    Fintype (FreshProgrammingSample history index input) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun sample : PermutationOracle Index Block × Block =>
      PermutationTranscriptMatches sample.1 history ∧
        FreshPermutationPair history index input sample.2) (by simp)

/-- This map swaps one fresh pair inside a fixed transcript fiber. -/
def swapFreshProgrammingSample
    {Index : Type uIndex} [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block) :
    FreshProgrammingSample history index input →
      FreshProgrammingSample history index input := by
  intro sample
  refine ⟨swapProgramPair index input sample.1, ?_⟩
  constructor
  · intro record member
    exact programPermutation_preserves sample.1.1 index input sample.1.2
      record (sample.2.1 record member) (sample.2.2 record member)
  · intro record member sameIndex
    have fresh := sample.2.2 record member sameIndex
    constructor
    · exact fresh.1
    · intro sameRange
      apply fresh.1
      apply (sample.1.1.permutation record.index).injective
      rw [sample.2.1 record member]
      simpa [sameIndex] using sameRange

/-- The fresh swap map is an involution inside its transcript fiber. -/
theorem swapFreshProgrammingSample_involutive
    {Index : Type uIndex} [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block) :
    Function.Involutive
      (swapFreshProgrammingSample history index input) := by
  intro sample
  apply Subtype.ext
  exact swapProgramPair_involutive index input sample.1

/-- This equivalence contains the fresh swap map in one transcript fiber. -/
noncomputable def swapFreshProgrammingSampleEquiv
    {Index : Type uIndex} [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block) :
    FreshProgrammingSample history index input ≃
      FreshProgrammingSample history index input :=
  (swapFreshProgrammingSample_involutive history index input).toPerm

/-- Fresh swap programming preserves a uniform transcript fiber exactly. -/
theorem map_uniform_swapFreshProgrammingSample
    {Index : Type uIndex} [Fintype Index] [DecidableEq Index]
    (history : List (PermutationRecord Index Block))
    (index : Index) (input : Block)
    [Nonempty (FreshProgrammingSample history index input)] :
    (PMF.uniformOfFintype
      (FreshProgrammingSample history index input)).map
        (swapFreshProgrammingSample history index input) =
      PMF.uniformOfFintype
        (FreshProgrammingSample history index input) :=
  map_uniformOfFintype_equiv
    (swapFreshProgrammingSampleEquiv history index input)

/-- A matching permutation transcript defines one partial injection. -/
theorem permutationTranscriptMatches_consistent
    {oracle : PermutationOracle Index Block}
    {history : List (PermutationRecord Index Block)}
    (matchesOracle : PermutationTranscriptMatches oracle history) :
    ConsistentPermutationTranscript history := by
  intro first firstMember second secondMember sameIndex
  have firstMatches := matchesOracle first firstMember
  have secondMatches := matchesOracle second secondMember
  constructor
  · intro sameDomain
    rw [← firstMatches, ← secondMatches, sameIndex, sameDomain]
  · intro sameRange
    apply (oracle.permutation first.index).injective
    rw [firstMatches, sameRange, ← secondMatches, sameIndex]

/-- A matching hash transcript gives one output to each input. -/
theorem hashTranscriptMatches_consistent {oracle : EncPRF.HashOracle}
    {history : List HashRecord} (matchesOracle : HashTranscriptMatches oracle history) :
    ∀ first ∈ history, ∀ second ∈ history,
      first.input = second.input → first.output = second.output := by
  intro first firstMember second secondMember sameInput
  rw [← matchesOracle first firstMember, ← matchesOracle second secondMember, sameInput]

/-- This key uses the exact non-black-box relation. -/
def SimulatorState.linkedKey (state : SimulatorState) : Option InputMacKey :=
  state.linking.map fun linking =>
    linkedInputKey state.encOracle state.hashOracle linking.bridgeKey linking.sourceKey

/-- This invariant covers every public oracle and every layer label. -/
def SimulatorInvariant (state : SimulatorState) : Prop :=
  PermutationTranscriptMatches state.fixedOracle state.fixedTranscript ∧
    PermutationTranscriptMatches state.encOracle state.encTranscript ∧
      HashTranscriptMatches state.hashOracle state.hashTranscript ∧
      DistinctCommitments state.commitments

/-- A fresh fixed-key state swap preserves the shared invariant. -/
theorem swapFixedStateTarget_preservesInvariant
    (state : SimulatorState) (target : Block)
    (index : Pipeline.FixedKeyIndex) (input : Block)
    (invariant : SimulatorInvariant state)
    (fresh : FreshPermutationPair state.fixedTranscript index input target) :
    SimulatorInvariant (swapFixedStateTarget index input (state, target)).1 := by
  refine ⟨?_, invariant.2⟩
  intro record member
  exact programPermutation_preserves state.fixedOracle index input target record
    (invariant.1 record member) (fresh record member)

/-- A fresh hash state swap preserves the shared invariant. -/
theorem swapHashStateTarget_preservesInvariant
    (state : SimulatorState) (target : Block × Block)
    (input : BaseField) (invariant : SimulatorInvariant state)
    (fresh : FreshHashInput state.hashTranscript input) :
    SimulatorInvariant (swapHashStateTarget input (state, target)).1 := by
  refine ⟨invariant.1, invariant.2.1, ?_, invariant.2.2.2⟩
  intro record member
  change Function.update state.hashOracle input target record.input = record.output
  rw [Function.update_of_ne (fresh record member)]
  exact invariant.2.2.1 record member

/-- The shared invariant gives consistent public-oracle transcripts. -/
theorem SimulatorInvariant.transcriptsConsistent {state : SimulatorState}
    (invariant : SimulatorInvariant state) :
    ConsistentPermutationTranscript state.fixedTranscript ∧
      ConsistentPermutationTranscript state.encTranscript :=
  ⟨permutationTranscriptMatches_consistent invariant.1,
    permutationTranscriptMatches_consistent invariant.2.1⟩

/-- This state uses the oracle functions from one random tape. -/
def initialState (randomness : Garbling.Randomness) : SimulatorState := {
  fixedOracle := randomness.fixedKeyOracle
  encOracle := randomness.encPRFOracle
  hashOracle := randomness.hashOracle
  fixedTranscript := []
  encTranscript := []
  hashTranscript := []
  commitments := []
  linking := none
  bad := false
}

theorem initialState_invariant (randomness : Garbling.Randomness) :
    SimulatorInvariant (initialState randomness) := by
  simp [SimulatorInvariant, initialState, PermutationTranscriptMatches,
    HashTranscriptMatches, DistinctCommitments]

/-- This operation programs one fresh fixed-key permutation pair. -/
def programFixed (state : SimulatorState) (index : Pipeline.FixedKeyIndex)
    (input output : Block) : SimulatorState :=
  { state with
    fixedOracle := programPermutation state.fixedOracle index input output
    fixedTranscript := PermutationRecord.mk .program .simulator index input output ::
      state.fixedTranscript }

/-- This operation programs one fresh EncPRF permutation pair. -/
def programEnc (state : SimulatorState) (index : EncPRF.PermutationIndex)
    (input output : Block) : SimulatorState :=
  { state with
    encOracle := programPermutation state.encOracle index input output
    encTranscript := PermutationRecord.mk .program .simulator index input output ::
      state.encTranscript }

/-- This operation programs one fresh random-oracle input. -/
def programHash (state : SimulatorState) (input : BaseField)
    (output : Block × Block) : SimulatorState :=
  { state with
    hashOracle := Function.update state.hashOracle input output
    hashTranscript := { input := input, output := output } :: state.hashTranscript }

/-- This operation records a programming collision. -/
def markBad (state : SimulatorState) : SimulatorState := { state with bad := true }

/-- This operation programs one fixed-key pair or records a collision. -/
def tryProgramFixed (state : SimulatorState) (index : Pipeline.FixedKeyIndex)
    (input output : Block) : SimulatorState :=
  if freshPermutationPairCheck state.fixedTranscript index input output
  then programFixed state index input output else markBad state

/-- This operation programs one EncPRF pair or records a collision. -/
def tryProgramEnc (state : SimulatorState) (index : EncPRF.PermutationIndex)
    (input output : Block) : SimulatorState :=
  if freshPermutationPairCheck state.encTranscript index input output
  then programEnc state index input output else markBad state

/-- This operation programs one random-oracle input or records a collision. -/
def tryProgramHash (state : SimulatorState) (input : BaseField)
    (output : Block × Block) : SimulatorState :=
  if freshHashInputCheck state.hashTranscript input
  then programHash state input output else markBad state

/-- A prior collision remains recorded after checked fixed-key programming. -/
theorem tryProgramFixed_bad_of_bad (state : SimulatorState)
    (index : Pipeline.FixedKeyIndex) (input output : Block)
    (bad : state.bad = true) :
    (tryProgramFixed state index input output).bad = true := by
  unfold tryProgramFixed
  split <;> simp_all [programFixed, markBad]

theorem programHash_apply (state : SimulatorState) (input : BaseField)
    (output : Block × Block) :
    (programHash state input output).hashOracle input = output := by
  exact Function.update_self input output state.hashOracle

/-- Fresh fixed-key programming preserves the shared invariant. -/
theorem programFixed_preservesInvariant {state : SimulatorState}
    {index : Pipeline.FixedKeyIndex} {input output : Block}
    (invariant : SimulatorInvariant state)
    (fresh : FreshPermutationPair state.fixedTranscript index input output) :
    SimulatorInvariant (programFixed state index input output) := by
  refine ⟨?_, invariant.2⟩
  intro record member
  simp only [programFixed, List.mem_cons] at member
  rcases member with rfl | member
  · exact programPermutation_apply state.fixedOracle index input output
  · exact programPermutation_preserves state.fixedOracle index input output record
      (invariant.1 record member) (fresh record member)

/-- Fresh EncPRF programming preserves the shared invariant. -/
theorem programEnc_preservesInvariant {state : SimulatorState}
    {index : EncPRF.PermutationIndex} {input output : Block}
    (invariant : SimulatorInvariant state)
    (fresh : FreshPermutationPair state.encTranscript index input output) :
    SimulatorInvariant (programEnc state index input output) := by
  refine ⟨invariant.1, ?_, invariant.2.2⟩
  intro record member
  simp only [programEnc, List.mem_cons] at member
  rcases member with rfl | member
  · exact programPermutation_apply state.encOracle index input output
  · exact programPermutation_preserves state.encOracle index input output record
      (invariant.2.1 record member) (fresh record member)

/-- Fresh random-oracle programming preserves the shared invariant. -/
theorem programHash_preservesInvariant {state : SimulatorState}
    {input : BaseField} {output : Block × Block}
    (invariant : SimulatorInvariant state)
    (fresh : FreshHashInput state.hashTranscript input) :
    SimulatorInvariant (programHash state input output) := by
  refine ⟨invariant.1, invariant.2.1, ?_, invariant.2.2.2⟩
  intro record member
  simp only [programHash, List.mem_cons] at member
  rcases member with rfl | member
  · exact programHash_apply state input output
  · change Function.update state.hashOracle input output record.input = record.output
    rw [Function.update_of_ne (fresh record member)]
    exact invariant.2.2.1 record member

/-- Checked fixed-key programming preserves the shared invariant. -/
theorem tryProgramFixed_preservesInvariant (state : SimulatorState)
    (index : Pipeline.FixedKeyIndex) (input output : Block)
    (invariant : SimulatorInvariant state) :
    SimulatorInvariant (tryProgramFixed state index input output) := by
  by_cases checked : freshPermutationPairCheck state.fixedTranscript index input output = true
  · have fresh := (freshPermutationPairCheck_eq_true _ _ _ _).mp checked
    simpa [tryProgramFixed, checked] using programFixed_preservesInvariant invariant fresh
  · simpa [tryProgramFixed, checked, markBad, SimulatorInvariant] using invariant

/-- Checked EncPRF programming preserves the shared invariant. -/
theorem tryProgramEnc_preservesInvariant (state : SimulatorState)
    (index : EncPRF.PermutationIndex) (input output : Block)
    (invariant : SimulatorInvariant state) :
    SimulatorInvariant (tryProgramEnc state index input output) := by
  by_cases checked : freshPermutationPairCheck state.encTranscript index input output = true
  · have fresh := (freshPermutationPairCheck_eq_true _ _ _ _).mp checked
    simpa [tryProgramEnc, checked] using programEnc_preservesInvariant invariant fresh
  · simpa [tryProgramEnc, checked, markBad, SimulatorInvariant] using invariant

/-- Checked random-oracle programming preserves the shared invariant. -/
theorem tryProgramHash_preservesInvariant (state : SimulatorState)
    (input : BaseField) (output : Block × Block)
    (invariant : SimulatorInvariant state) :
    SimulatorInvariant (tryProgramHash state input output) := by
  by_cases checked : freshHashInputCheck state.hashTranscript input = true
  · have fresh := (freshHashInputCheck_eq_true _ _).mp checked
    simpa [tryProgramHash, checked] using programHash_preservesInvariant invariant fresh
  · simpa [tryProgramHash, checked, markBad, SimulatorInvariant] using invariant

/-- Checked fixed-key programming succeeds or records a collision. -/
theorem tryProgramFixed_badOrFresh (state : SimulatorState)
    (index : Pipeline.FixedKeyIndex) (input output : Block) :
    (tryProgramFixed state index input output).bad = true ∨
      FreshPermutationPair state.fixedTranscript index input output := by
  by_cases checked : freshPermutationPairCheck state.fixedTranscript index input output = true
  · exact Or.inr ((freshPermutationPairCheck_eq_true _ _ _ _).mp checked)
  · simp [tryProgramFixed, checked, markBad]

/-- A non-bad result implies a non-bad prior state. -/
theorem tryProgramFixed_priorNotBad (state : SimulatorState)
    (index : Pipeline.FixedKeyIndex) (input output : Block)
    (notBad : (tryProgramFixed state index input output).bad = false) :
    state.bad = false := by
  by_cases checked : freshPermutationPairCheck state.fixedTranscript index input output = true
  · simpa [tryProgramFixed, checked, programFixed] using notBad
  · simp [tryProgramFixed, checked, markBad] at notBad

/-- A non-bad result contains the requested fixed-key pair. -/
theorem tryProgramFixed_apply_of_notBad (state : SimulatorState)
    (index : Pipeline.FixedKeyIndex) (input output : Block)
    (notBad : (tryProgramFixed state index input output).bad = false) :
    (tryProgramFixed state index input output).fixedOracle.permutation index input = output := by
  by_cases checked : freshPermutationPairCheck state.fixedTranscript index input output = true
  · simp [tryProgramFixed, checked, programFixed, programPermutation_apply]
  · simp [tryProgramFixed, checked, markBad] at notBad

/-- Programming a different index preserves one fixed-key pair. -/
theorem tryProgramFixed_preservesOther (state : SimulatorState)
    (oldIndex newIndex : Pipeline.FixedKeyIndex) (oldInput oldOutput input output : Block)
    (different : oldIndex ≠ newIndex)
    (prior : state.fixedOracle.permutation oldIndex oldInput = oldOutput) :
    (tryProgramFixed state newIndex input output).fixedOracle.permutation oldIndex oldInput =
      oldOutput := by
  by_cases checked : freshPermutationPairCheck state.fixedTranscript newIndex input output = true
  · simpa [tryProgramFixed, checked, programFixed, programPermutation, different] using prior
  · simpa [tryProgramFixed, checked, markBad] using prior

/-- Checked EncPRF programming succeeds or records a collision. -/
theorem tryProgramEnc_badOrFresh (state : SimulatorState)
    (index : EncPRF.PermutationIndex) (input output : Block) :
    (tryProgramEnc state index input output).bad = true ∨
      FreshPermutationPair state.encTranscript index input output := by
  by_cases checked : freshPermutationPairCheck state.encTranscript index input output = true
  · exact Or.inr ((freshPermutationPairCheck_eq_true _ _ _ _).mp checked)
  · simp [tryProgramEnc, checked, markBad]

/-- Checked random-oracle programming succeeds or records a collision. -/
theorem tryProgramHash_badOrFresh (state : SimulatorState)
    (input : BaseField) (output : Block × Block) :
    (tryProgramHash state input output).bad = true ∨
      FreshHashInput state.hashTranscript input := by
  by_cases checked : freshHashInputCheck state.hashTranscript input = true
  · exact Or.inr ((freshHashInputCheck_eq_true _ _).mp checked)
  · simp [tryProgramHash, checked, markBad]

/-- This operation records one fixed-key permutation pair. -/
def recordFixed (state : SimulatorState)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) : SimulatorState :=
  { state with fixedTranscript := record :: state.fixedTranscript }

/-- This operation records one EncPRF permutation pair. -/
def recordEnc (state : SimulatorState)
    (record : PermutationRecord EncPRF.PermutationIndex Block) : SimulatorState :=
  { state with encTranscript := record :: state.encTranscript }

/-- This operation records one random-oracle query. -/
def recordHash (state : SimulatorState) (record : HashRecord) : SimulatorState :=
  { state with hashTranscript := record :: state.hashTranscript }

/-- This operation records one label constraint. -/
def addCommitment (state : SimulatorState)
    (commitment : LabelCommitment) : SimulatorState :=
  { state with commitments := commitment :: state.commitments }

/-- A compatible fixed-key record preserves the shared invariant. -/
theorem recordFixed_preservesInvariant {state : SimulatorState}
    {record : PermutationRecord Pipeline.FixedKeyIndex Block}
    (invariant : SimulatorInvariant state)
    (recordMatches : state.fixedOracle.permutation record.index record.domain = record.range) :
    SimulatorInvariant (recordFixed state record) := by
  exact ⟨by simpa [PermutationTranscriptMatches, recordFixed] using And.intro recordMatches invariant.1,
    invariant.2⟩

/-- A compatible EncPRF record preserves the shared invariant. -/
theorem recordEnc_preservesInvariant {state : SimulatorState}
    {record : PermutationRecord EncPRF.PermutationIndex Block}
    (invariant : SimulatorInvariant state)
    (recordMatches : state.encOracle.permutation record.index record.domain = record.range) :
    SimulatorInvariant (recordEnc state record) := by
  exact ⟨invariant.1,
    by simpa [PermutationTranscriptMatches, recordEnc] using And.intro recordMatches invariant.2.1,
    invariant.2.2⟩

/-- An exact random-oracle record preserves the shared invariant. -/
theorem recordHash_preservesInvariant {state : SimulatorState} {record : HashRecord}
    (invariant : SimulatorInvariant state)
    (recordMatches : state.hashOracle record.input = record.output) :
    SimulatorInvariant (recordHash state record) := by
  exact ⟨invariant.1, invariant.2.1,
    by simpa [HashTranscriptMatches, recordHash] using And.intro recordMatches invariant.2.2.1,
    invariant.2.2.2⟩

/-- A fresh label constraint preserves the shared invariant. -/
theorem addCommitment_preservesInvariant {state : SimulatorState}
    {commitment : LabelCommitment}
    (invariant : SimulatorInvariant state)
    (fresh : ∀ prior ∈ state.commitments,
      commitment.wire ≠ prior.wire ∧ commitment.label ≠ prior.label) :
    SimulatorInvariant (addCommitment state commitment) := by
  exact ⟨invariant.1, invariant.2.1, invariant.2.2.1,
    List.pairwise_cons.mpr ⟨fresh, invariant.2.2.2⟩⟩

/-- This handler records every public-oracle query with its origin. -/
def oracleHandlerFor (origin : PermutationOrigin) :
    OracleHandler Garbling.oracleSpec SimulatorState
  | .fixedForward index input, state =>
      let output := state.fixedOracle.permutation index input
      (output, recordFixed state
        (PermutationRecord.mk .forward origin index input output))
  | .fixedInverse index output, state =>
      let input := (state.fixedOracle.permutation index).symm output
      (input, recordFixed state
        (PermutationRecord.mk .inverse origin index input output))
  | .encForward index input, state =>
      let output := state.encOracle.permutation index input
      (output, recordEnc state
        (PermutationRecord.mk .forward origin index input output))
  | .encInverse index output, state =>
      let input := (state.encOracle.permutation index).symm output
      (input, recordEnc state
        (PermutationRecord.mk .inverse origin index input output))
  | .hash input, state =>
      let output := state.hashOracle input
      (output, recordHash state { input := input, output := output })

/-- The ideal handler records every adversary query. -/
def idealOracleHandler : OracleHandler Garbling.oracleSpec SimulatorState :=
  oracleHandlerFor .adversary

/-- This handler records every construction query. -/
def constructionOracleHandler : OracleHandler Garbling.oracleSpec SimulatorState :=
  oracleHandlerFor .construction

/-- This handler carries one programming target without changing it. -/
def carrySimulatorHandler {Target : Type}
    (handler : OracleHandler Garbling.oracleSpec SimulatorState) :
    OracleHandler Garbling.oracleSpec (SimulatorState × Target)
  | query, sample =>
      let answered := handler query sample.1
      (answered.1, (answered.2, sample.2))

/-- This condition excludes the two fixed-key swap collision points. -/
def FixedQuerySafe (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (index : Pipeline.FixedKeyIndex) (input target : Block) :
    Garbling.OracleQuery → Prop
  | .fixedForward current domain => current = index →
      domain ≠ input ∧ oracle.permutation current domain ≠ target
  | .fixedInverse current range => current = index →
      range ≠ oracle.permutation current input ∧ range ≠ target
  | _ => True

/-- A safe ideal query commutes with one fixed-key state swap. -/
theorem carryIdealHandler_swapFixed
    (index : Pipeline.FixedKeyIndex) (input : Block)
    (sample : SimulatorState × Block) (query : Garbling.OracleQuery)
    (safe : FixedQuerySafe sample.1.fixedOracle index input sample.2 query) :
    let original := carrySimulatorHandler idealOracleHandler query sample
    let swapped := carrySimulatorHandler idealOracleHandler query
      (swapFixedStateTarget index input sample)
    original.1 = swapped.1 ∧
      swapFixedStateTarget index input original.2 = swapped.2 := by
  rcases sample with ⟨state, target⟩
  cases query with
  | fixedForward current domain =>
      have answerEq := programPermutation_forward_eq_of_fresh
        state.fixedOracle index input target current domain safe
      simp only [carrySimulatorHandler, idealOracleHandler, oracleHandlerFor,
        swapFixedStateTarget]
      rw [answerEq]
      constructor
      · rfl
      · rfl
  | fixedInverse current range =>
      have answerEq := programPermutation_inverse_eq_of_fresh
        state.fixedOracle index input target current range safe
      simp only [carrySimulatorHandler, idealOracleHandler, oracleHandlerFor,
        swapFixedStateTarget]
      rw [answerEq]
      constructor
      · rfl
      · rfl
  | encForward current domain =>
      simp [carrySimulatorHandler, idealOracleHandler, oracleHandlerFor,
        swapFixedStateTarget, recordEnc]
  | encInverse current range =>
      simp [carrySimulatorHandler, idealOracleHandler, oracleHandlerFor,
        swapFixedStateTarget, recordEnc]
  | hash current =>
      simp [carrySimulatorHandler, idealOracleHandler, oracleHandlerFor,
        swapFixedStateTarget, recordHash]

/-- This condition excludes the programmed hash input. -/
def HashQuerySafe (input : BaseField) : Garbling.OracleQuery → Prop
  | .hash current => current ≠ input
  | _ => True

/-- A safe ideal query commutes with one hash state swap. -/
theorem carryIdealHandler_swapHash
    (input : BaseField) (sample : SimulatorState × (Block × Block))
    (query : Garbling.OracleQuery) (safe : HashQuerySafe input query) :
    let original := carrySimulatorHandler idealOracleHandler query sample
    let swapped := carrySimulatorHandler idealOracleHandler query
      (swapHashStateTarget input sample)
    original.1 = swapped.1 ∧
      swapHashStateTarget input original.2 = swapped.2 := by
  rcases sample with ⟨state, target⟩
  cases query with
  | fixedForward current domain =>
      simp [carrySimulatorHandler, idealOracleHandler, oracleHandlerFor,
        swapHashStateTarget, recordFixed]
  | fixedInverse current range =>
      simp [carrySimulatorHandler, idealOracleHandler, oracleHandlerFor,
        swapHashStateTarget, recordFixed]
  | encForward current domain =>
      simp [carrySimulatorHandler, idealOracleHandler, oracleHandlerFor,
        swapHashStateTarget, recordEnc]
  | encInverse current range =>
      simp [carrySimulatorHandler, idealOracleHandler, oracleHandlerFor,
        swapHashStateTarget, recordEnc]
  | hash current =>
      have answerEq := updateProgramPair_apply_of_ne state.hashOracle
        input target current safe
      have answerEq' : Function.update state.hashOracle input target current =
          state.hashOracle current := by
        simpa [updateProgramPair] using answerEq
      simp only [carrySimulatorHandler, idealOracleHandler, oracleHandlerFor,
        swapHashStateTarget]
      rw [answerEq']
      simp [recordHash]

/-- A path-safe adversary program commutes with one fixed-key state swap. -/
theorem oracleProgram_run_swapFixed_of_safe
    {Result : Type uResult} {budget : Nat}
    (index : Pipeline.FixedKeyIndex) (input : Block)
    (program : OracleProgram Garbling.oracleSpec Result budget)
    (sample : SimulatorState × Block)
    (programSafe : OracleProgramSafe
      (carrySimulatorHandler idealOracleHandler)
      (fun query state =>
        FixedQuerySafe state.1.fixedOracle index input state.2 query)
      program sample) :
    (program.run (carrySimulatorHandler idealOracleHandler) sample).map
        (fun output => (output.1, swapFixedStateTarget index input output.2)) =
      program.run (carrySimulatorHandler idealOracleHandler)
        (swapFixedStateTarget index input sample) := by
  exact oracleProgram_run_stateEquiv_of_safe
    (carrySimulatorHandler idealOracleHandler)
    (carrySimulatorHandler idealOracleHandler)
    (swapFixedStateTargetEquiv index input)
    (fun query state =>
      FixedQuerySafe state.1.fixedOracle index input state.2 query)
    (fun query state safe => carryIdealHandler_swapFixed index input state query safe)
    program sample programSafe

/-- A path-safe adversary program commutes with one hash state swap. -/
theorem oracleProgram_run_swapHash_of_safe
    {Result : Type uResult} {budget : Nat} (input : BaseField)
    (program : OracleProgram Garbling.oracleSpec Result budget)
    (sample : SimulatorState × (Block × Block))
    (programSafe : OracleProgramSafe
      (carrySimulatorHandler idealOracleHandler)
      (fun query _ => HashQuerySafe input query) program sample) :
    (program.run (carrySimulatorHandler idealOracleHandler) sample).map
        (fun output => (output.1, swapHashStateTarget input output.2)) =
      program.run (carrySimulatorHandler idealOracleHandler)
        (swapHashStateTarget input sample) := by
  exact oracleProgram_run_stateEquiv_of_safe
    (carrySimulatorHandler idealOracleHandler)
    (carrySimulatorHandler idealOracleHandler)
    (swapHashStateTargetEquiv input)
    (fun query _ => HashQuerySafe input query)
    (fun query state safe => carryIdealHandler_swapHash input state query safe)
    program sample programSafe

/-- Every public-oracle query preserves the shared invariant. -/
theorem oracleHandlerFor_preservesInvariant (origin : PermutationOrigin)
    (query : Garbling.oracleSpec.Query)
    (state : SimulatorState) (invariant : SimulatorInvariant state) :
    SimulatorInvariant (oracleHandlerFor origin query state).2 := by
  cases query <;> simp only [oracleHandlerFor]
  · exact recordFixed_preservesInvariant invariant rfl
  · exact recordFixed_preservesInvariant invariant (Equiv.apply_symm_apply _ _)
  · exact recordEnc_preservesInvariant invariant rfl
  · exact recordEnc_preservesInvariant invariant (Equiv.apply_symm_apply _ _)
  · exact recordHash_preservesInvariant invariant rfl

theorem idealOracleHandler_preservesInvariant (query : Garbling.oracleSpec.Query)
    (state : SimulatorState) (invariant : SimulatorInvariant state) :
    SimulatorInvariant (idealOracleHandler query state).2 :=
  oracleHandlerFor_preservesInvariant .adversary query state invariant

/-- This relation keeps the three public oracle functions equal. -/
def RealIdealOracleRelated (randomness : Garbling.Randomness)
    (state : SimulatorState) : Prop :=
  randomness.fixedKeyOracle = state.fixedOracle ∧
    randomness.encPRFOracle = state.encOracle ∧
    randomness.hashOracle = state.hashOracle

theorem initialState_realIdealOracleRelated (randomness : Garbling.Randomness) :
    RealIdealOracleRelated randomness (initialState randomness) := by
  simp [RealIdealOracleRelated, initialState]

/-- Real and recording handlers keep equal public oracle answers. -/
theorem realIdealOracleHandlers_related
    (query : Garbling.oracleSpec.Query) (randomness : Garbling.Randomness)
    (state : SimulatorState) (related : RealIdealOracleRelated randomness state) :
    (Garbling.oracleHandler query randomness).1 =
        (idealOracleHandler query state).1 ∧
      RealIdealOracleRelated (Garbling.oracleHandler query randomness).2
        (idealOracleHandler query state).2 := by
  rcases related with ⟨fixed, enc, hash⟩
  cases query <;>
    simp only [Garbling.oracleHandler, idealOracleHandler, oracleHandlerFor]
  · exact ⟨by rw [fixed],
      by simp [RealIdealOracleRelated, recordFixed, fixed, enc, hash]⟩
  · exact ⟨by rw [fixed],
      by simp [RealIdealOracleRelated, recordFixed, fixed, enc, hash]⟩
  · exact ⟨by rw [enc],
      by simp [RealIdealOracleRelated, recordEnc, fixed, enc, hash]⟩
  · exact ⟨by rw [enc],
      by simp [RealIdealOracleRelated, recordEnc, fixed, enc, hash]⟩
  · exact ⟨congrFun hash _,
      by simp [RealIdealOracleRelated, recordHash, fixed, enc, hash]⟩

/-- Recording queries does not change an adversary's result distribution. -/
theorem oracleProgram_real_ideal_result
    {Result : Type uResult} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget)
    (randomness : Garbling.Randomness) (state : SimulatorState)
    (related : RealIdealOracleRelated randomness state) :
    (program.run Garbling.oracleHandler randomness).map Prod.fst =
      (program.run idealOracleHandler state).map Prod.fst :=
  oracleProgram_run_result_of_related Garbling.oracleHandler idealOracleHandler
    RealIdealOracleRelated realIdealOracleHandlers_related program randomness state related

theorem oracleProgram_real_initial_result
    {Result : Type uResult} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget)
    (randomness : Garbling.Randomness) :
    (program.run Garbling.oracleHandler randomness).map Prod.fst =
      (program.run idealOracleHandler (initialState randomness)).map Prod.fst :=
  oracleProgram_real_ideal_result program randomness (initialState randomness)
    (initialState_realIdealOracleRelated randomness)

/-- The recording handler exactly replays every real query trace. -/
theorem runOracleProgramWithTrace_real_initial_replay
    {Result : Type uResult} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget)
    (randomness : Garbling.Randomness) :
    (runOracleProgramWithTrace Garbling.oracleHandler program randomness).map
        (replayTracedOutput idealOracleHandler (initialState randomness)) =
      runOracleProgramWithTrace idealOracleHandler program (initialState randomness) :=
  runOracleProgramWithTrace_replay_of_related Garbling.oracleHandler
    idealOracleHandler RealIdealOracleRelated realIdealOracleHandlers_related
    program randomness (initialState randomness)
    (initialState_realIdealOracleRelated randomness)

end Kriterion.ArgoMAC.Security
