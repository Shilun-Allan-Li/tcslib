<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.exists_oracle_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An oracle separation of NP and P

**Claim.** There is an oracle B for which the unary language having a length-n witness in B is in NP relative to B but not in P relative to B.

**Proof.** Choose an enumeration N of all finite deterministic oracle machines, with the property that every such machine M occurs at arbitrarily large indices i and N_i has the same behavior as M for every oracle, input, output, and time bound (`exists_finOracleTM_enumeration`). Set B to the diagonal oracle `bgsOracle N`. The unary witness language is in NP relative to B by `unaryWitnessLang_mem_NPOracle`.

Suppose instead it were in P relative to B, decided by M in time c(n^k+1). Choose an index i at least k+1+2c at which N_i simulates M, and put n=`freshLen i (stage N i).bound`. On input 1^n, the assumed decision runs within c(n^k+1); `stage_dominates` bounds this by n^i+i. The simulation equivalence transfers that computation to N_i within the stage bound. Thus N_i’s behavior on this input must decide the unary witness language.

But `stage_flip` defines B’s diagonal behavior at precisely this stage so that N_i accepts 1^n exactly when 1^n is not in the unary witness language. If 1^n belongs, the simulated decider’s accepting output contradicts this flip. If it does not belong, the decider outputs false, whereas the flip requires acceptance; equivalently, the same machine and input cannot have both outputs, by `ComputesInTime.output_unique`. Both cases are impossible, so the language is not in P relative to B.

**Key facts.** `Complexity.exists_finOracleTM_enumeration`, `Complexity.unaryWitnessLang_mem_NPOracle`, `Complexity.stage_dominates`, `Turing.FinOracleTM.ComputesInTime.mono`, `Complexity.stage_flip`, `Turing.FinOracleTM.ComputesInTime.output_unique`.
