<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.exists_proj_decider -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time bound for existential projection

**Claim.** A language obtained by existentially appending a string of prescribed length to an input has a deterministic decider whose time is bounded by the stated exponential-times-polynomial expression.

**Proof.** Use the enumerating machine E supplied by `enumMachine_contracts`. After a startup phase, E visits each of the 2^w binary strings of length w, where w=C(|x|+1)^c, and runs the given decider for V on x followed by that string. Each round costs at most B=b(T_v(|x|+w)+(|x|+w+1)^{c+1}); the contract also ensures that if a candidate is accepted, E halts with true, and if none is accepted, it finishes with false.

The certificate theorem `enumAny_certificates` identifies the Boolean result of this finite enumeration with the existence of a length-w suffix u for which xu belongs to V. Hence E decides the projected language. `enumLoop_run` bounds the enumeration phase by 2^wB, and the startup phase is at most B. Since B≤2^wB, the total is at most 2·2^wB. Substituting w and B gives exactly the asserted bound with coefficient 2b. The computation-to-decision characterization and monotonicity of time bounds transfer this run and its output to the stated time limit.

**Key facts.** `Complexity.enumMachine_contracts`, `Complexity.enumAny_certificates`, `Complexity.enumLoop_run`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.ComputesInTime.mono`.
