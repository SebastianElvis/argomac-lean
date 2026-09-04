import Proof

open Kriterion Kriterion.BN254

theorem paperCTPRFHas100Bits :
    Cryptography.Assumptions.ConcreteBound 100
      ArgoMAC.Security.permutationWork ArgoMAC.Security.paperConcreteCTPRFError :=
  ArgoMAC.Security.paperConcreteCTPRFHas100Bits

theorem fullScheduleTransferredCTPRFDoesNotHave100Bits :
    ¬Cryptography.Assumptions.ConcreteBound 100
      ArgoMAC.Security.permutationWork ArgoMAC.Security.fullScheduleTransferredCTPRFError :=
  ArgoMAC.Security.fullScheduleTransferredCTPRFDoesNotHave100Bits

theorem programmedHashArithmeticHas100Bits :
    Cryptography.Assumptions.ConcreteBound 100
      ArgoMAC.Security.permutationWork ArgoMAC.Security.programmedHashError :=
  ArgoMAC.Security.programmedHashArithmeticHas100Bits

theorem programmedPadArithmeticHas100Bits :
    Cryptography.Assumptions.ConcreteBound 100
      ArgoMAC.Security.permutationWork ArgoMAC.Security.programmedPadError :=
  ArgoMAC.Security.programmedPadArithmeticHas100Bits

theorem selectedBranchProgrammingArithmeticHas100Bits (bit : Bool) :
    Cryptography.Assumptions.ConcreteBound 100
      ArgoMAC.Security.permutationWork
      (ArgoMAC.Security.selectedBranchProgrammedError bit) :=
  ArgoMAC.Security.selectedBranchProgrammingArithmeticHas100Bits bit

theorem hashLiftRoundingArithmeticHas100Bits :
    Cryptography.Assumptions.WorkPerAdvantage 100 1
      ArgoMAC.Security.hashLiftRoundingError :=
  ArgoMAC.Security.hashLiftRoundingArithmeticHas100Bits

#print axioms paperCTPRFHas100Bits
#print axioms fullScheduleTransferredCTPRFDoesNotHave100Bits
#print axioms programmedHashArithmeticHas100Bits
#print axioms programmedPadArithmeticHas100Bits
#print axioms selectedBranchProgrammingArithmeticHas100Bits
#print axioms hashLiftRoundingArithmeticHas100Bits
#print axioms ArgoMAC.Security.blockCard
#print axioms ArgoMAC.Security.uniformBlockMass
#print axioms ArgoMAC.Security.uniformBlockTwoPointUnionBound
#print axioms ArgoMAC.Security.uniformBlockFinsetMass
#print axioms ArgoMAC.Security.uniformBlockFinsetMass_le
#print axioms ArgoMAC.Security.uniformBlockTwoPointEvent_le
#print axioms ArgoMAC.Security.uniformBlockFinsetMass_sum_le
#print axioms ArgoMAC.Security.OracleProgramTrace.length_le
#print axioms ArgoMAC.Security.OracleProgramTrace.all_safe
#print axioms ArgoMAC.Security.OracleProgramTrace.append_length_le
#print axioms ArgoMAC.Security.oracleProgramTrace_collisionScheduleMass_le
#print axioms ArgoMAC.Security.advantage_map_prod_le_disagreement
#print axioms ArgoMAC.Security.boolDisagreement_mass
#print axioms ArgoMAC.Security.advantage_map_prod_le_disagreementMass
#print axioms ArgoMAC.Security.advantage_le_of_coupling
#print axioms ArgoMAC.Security.deterministicBoolCoupling_fst
#print axioms ArgoMAC.Security.deterministicBoolCoupling_snd
#print axioms ArgoMAC.Security.deterministicBoolCoupling_disagreement
#print axioms ArgoMAC.Security.advantage_map_le_disagreementMass
#print axioms ArgoMAC.Security.blockCollisionMass_toReal
#print axioms ArgoMAC.Security.pointLayerUsesLinkedInputKey
#print axioms ArgoMAC.Security.recordFixed_preservesInvariant
#print axioms ArgoMAC.Security.recordEnc_preservesInvariant
#print axioms ArgoMAC.Security.addCommitment_preservesInvariant
#print axioms ArgoMAC.Security.initialState_invariant
#print axioms ArgoMAC.Security.SimulatorInvariant.transcriptsConsistent
#print axioms ArgoMAC.Security.idealOracleHandler_preservesInvariant
#print axioms ArgoMAC.Security.oracleProgram_run_stateEquiv
#print axioms ArgoMAC.Security.programPermutation_apply
#print axioms ArgoMAC.Security.programPermutation_symm
#print axioms ArgoMAC.Security.programPermutation_preserves
#print axioms ArgoMAC.Security.programPermutation_forward_eq_of_fresh
#print axioms ArgoMAC.Security.programPermutation_inverse_eq_of_fresh
#print axioms ArgoMAC.Security.map_uniform_swapProgramPair
#print axioms ArgoMAC.Security.map_uniform_swapProgramTapeStep
#print axioms ArgoMAC.Security.map_uniform_swapProgramTapeSchedule
#print axioms ArgoMAC.Security.map_uniform_swapFreshProgrammingSample
#print axioms ArgoMAC.Security.map_uniform_updateProgramPair
#print axioms ArgoMAC.Security.updateProgramPair_apply_of_ne
#print axioms ArgoMAC.Security.map_uniform_swapFreshHashProgrammingSample
#print axioms ArgoMAC.Security.swapFixedStateTarget_involutive
#print axioms ArgoMAC.Security.swapHashStateTarget_involutive
#print axioms ArgoMAC.Security.swapFixedStateTarget_preservesInvariant
#print axioms ArgoMAC.Security.swapHashStateTarget_preservesInvariant
#print axioms ArgoMAC.Security.carryIdealHandler_swapFixed
#print axioms ArgoMAC.Security.carryIdealHandler_swapHash
#print axioms ArgoMAC.Security.oracleProgram_run_stateEquiv_of_safe
#print axioms ArgoMAC.Security.oracleProgram_run_swapFixed_of_safe
#print axioms ArgoMAC.Security.oracleProgram_run_swapHash_of_safe
#print axioms ArgoMAC.Security.programFixed_preservesInvariant
#print axioms ArgoMAC.Security.programEnc_preservesInvariant
#print axioms ArgoMAC.Security.programHash_apply
#print axioms ArgoMAC.Security.programHash_preservesInvariant
#print axioms Cryptography.freshPermutationPairCheck_eq_true
#print axioms ArgoMAC.Security.freshHashInputCheck_eq_true
#print axioms ArgoMAC.Security.tryProgramFixed_preservesInvariant
#print axioms ArgoMAC.Security.tryProgramEnc_preservesInvariant
#print axioms ArgoMAC.Security.tryProgramHash_preservesInvariant
#print axioms ArgoMAC.Security.tryProgramFixed_badOrFresh
#print axioms ArgoMAC.Security.tryProgramEnc_badOrFresh
#print axioms ArgoMAC.Security.tryProgramHash_badOrFresh
#print axioms ArgoMAC.Security.programHashGate_evaluate
#print axioms ArgoMAC.Security.programPadGate_evaluate
#print axioms ArgoMAC.Security.programGate_evaluate
#print axioms ArgoMAC.Security.programGate_preservesInvariant
#print axioms ArgoMAC.Security.programGate_badOrFreshAll
#print axioms ArgoMAC.Security.liftHashBlocks_value
#print axioms ArgoMAC.Security.targetPadBlocks_value
#print axioms ArgoMAC.Security.programGateForTarget_evaluate
#print axioms ArgoMAC.Security.programGateForTarget_preservesInvariant
#print axioms ArgoMAC.Security.programGateForTarget_badOrFreshAll
#print axioms ArgoMAC.Security.recordGateConstructionQueries_preservesInvariant
#print axioms ArgoMAC.Security.recordGateConstructionQueries_length
#print axioms ArgoMAC.Security.recordGateConstructionQueries_origin
