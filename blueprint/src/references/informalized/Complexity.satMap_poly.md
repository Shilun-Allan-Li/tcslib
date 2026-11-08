<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satMap_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Transducer Semantics

**Claim.** The word function defined by emitting according to the per-bit rule, updating state on each bit, and applying the final emission rule is polynomial-time computable.

**Proof.** Use the transducer machine with time bound $n+1$, which is a polynomial bound of the required form with both constants equal to $1$. Its run result says that, from the initial configuration on an input word $x$, it halts after $|x|+1$ steps and outputs exactly the transducer semantics on $x$ (`Complexity.satMap_run`), by taking the already-processed prefix empty and the remaining word to be $x$. The initial configuration agrees with the canonical transducer configuration at position zero and empty output; for a machine with zero work tapes, the state, input position, and output determine the configuration (`Turing.Cfg.ext_zero_tapes`). The equivalence between the computation predicate and halting with the specified output then gives the required polynomial-time computation (`Turing.FinTM.computesInTime_iff`).

**Key facts.** `Complexity.satMap_run`, `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.computesInTime_iff`.
