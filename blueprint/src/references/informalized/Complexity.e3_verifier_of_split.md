<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_verifier_of_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time verifier language

**Claim.** If a deterministic machine computes the split-emitter function in time $A(n+1)^{r+1}$, then the language of words admitting a split and choice string as specified, on which the nondeterministic machine accepts, belongs to $\mathrm{P}$.

**Proof.** The proof uses the polynomial-time characterization of $\mathrm{P}$ (`mem_P_iff`) and chooses the buffered composition of the split-emitter machine with a machine that simulates the nondeterministic verifier on a supplied choice string. On input $y$, the split-emitter produces the encoded candidate split. The buffered composition setup bounds the time to reach the verifier phase by the split computation time plus the output length and a fixed overhead (`bufferedComp_start`). The verifier simulation then takes at most $3(2|y|+3)$ steps while preserving its simulated computation (`bufferedSecondCfg_run`). The resulting computation accepts exactly when the verifier does: this is the established correctness statement for the split-and-verifier computation (`e3_split_answer`), together with the equivalence between machine computation and its halting state and output (`computesInTime_iff`). Its output is the indicator of the target language. Finally, the emitted word has length at most $2|y|+2$ (`e3_split_length`), and the setup and simulation overhead are absorbed into a bound $(A+13)(|y|+1)^{r+1}$, using $|y|+1\le (|y|+1)^{r+1}$. Thus the composite machine decides the language within a polynomial bound, proving membership in $\mathrm{P}$.

**Key facts.** `Complexity.mem_P_iff`, `Turing.FinTM.bufferedComp_start`, `Turing.FinTM.bufferedSecondCfg_run`, `Complexity.e3_split_answer`, `Turing.FinTM.computesInTime_iff`, `Complexity.e3_split_length`, `Turing.FinTM.ComputesInTime.mono`, `Turing.MultiTapeTM.runFrom_add`.
