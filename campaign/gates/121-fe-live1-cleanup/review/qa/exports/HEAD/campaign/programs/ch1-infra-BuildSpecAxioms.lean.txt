import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.Uncomputability.Halting

set_option maxHeartbeats 0

-- Machine-library spec layer, maintainer attestation (round 3: 23 contracts).
-- (1) The Chapter-1 headline regression set must stay admission-free: the Build
-- modules are only imported, outside the Build subgraph, by the facade, so their
-- sorried contracts must not reach any headline print.
#print axioms Turing.timed_universal
#print axioms Turing.universal
#print axioms Turing.universal_quadratic
#print axioms Turing.exists_effectiveMachineCode
#print axioms Complexity.HALT_not_computable

-- (2) The Convention module is fully proved: its glue must be admission-free.
#print axioms Turing.initCfg_ofWords
#print axioms Turing.Cfg.ofWords_workTapes

-- (3) The 23 sorried spec contracts, printed to pin the expected admission set
-- of this commit (each must show sorryAx; nothing else in the tree gains one).
#print axioms Turing.capture_run
#print axioms Turing.FinTM.redirectTM_computes
#print axioms Turing.FinTM.redirectTM_live
#print axioms Turing.FinTM.computesFunInTime_cond
#print axioms Turing.loop_run
#print axioms Turing.FinTM.exists_loopCfgTM
#print axioms Turing.FinTM.exists_loopTM
#print axioms Turing.FinTM.exists_loopFindTM
#print axioms Turing.FinTM.computesFunInTime_prepend
#print axioms Turing.FinTM.computesFunInTime_lengthBits
#print axioms Turing.FinTM.computesFunInTime_polyUnary
#print axioms Turing.FinTM.computesFunInTime_polyBits
#print axioms Turing.FinTM.computesFunInTime_pairEncodeFixed
#print axioms Turing.FinTM.computesFunInTime_pairFst
#print axioms Turing.FinTM.computesFunInTime_pairSnd
#print axioms Turing.FinTM.computesFunInTime_pairValid
#print axioms Turing.FinTM.computesFunInTime_pairConcat
#print axioms Turing.FinTM.computesFunInTime_pairDup
#print axioms Turing.FinTM.computesFunInTime_pairMapSnd
#print axioms Turing.FinTM.computesFunInTime_pairLenCheck
#print axioms Turing.FinTM.computesFunInTime_stripLast
#print axioms Turing.FinTM.computesFunInTime_splitSolve
#print axioms Turing.FinTM.computesFunInTime_incFixed
