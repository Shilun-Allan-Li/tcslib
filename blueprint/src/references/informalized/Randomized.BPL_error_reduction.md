<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.BPL_error_reduction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Error reduction for bounded-error log space

**Claim.** If a language is decidable in bounded-error probabilistic logarithmic space, then for every $d$ there is a finite-state nondeterministic machine using logarithmic space, halting after a fixed number of choices per input, whose probability of outputting the membership bit is at least $1-(1/2)^{(|x|+1)^d}$.

**Proof.** Choose a bounded-error log-space machine $N$ for the language, with space constant $c$, and set $F=\mathrm{codeK}(N)(c+2)+d+5$. The polynomial-amplification construction provides an amplified computation with a polynomially bounded amount of work, whose answer can be checked by a nondeterministic log-space machine. Applying the log-space-to-nondeterministic-machine simulation theorem (`Complexity.LogProg.narm_logspace_ptm`) to that amplified construction gives a finite-state machine $M$ with logarithmic space and the required halting behavior for each input and its chosen number of random choices.

Fix an input $x$. The amplification setting theorem (`Randomized.polyAmp_setting`) supplies a common time bound $K=\mathrm{bigK}(F,|x|)$, preserves the original machine's output probabilities when padded to that time, and relates the amplified computation's acceptance probability to the event that its amplified answer is true. The bound on the amplification parameter (`Randomized.PolyAmp.bigK_ge`) gives $32(|x|+1)^d\le K$. In the yes case, the original machine accepts with probability at least $2/3$; the two-run amplification estimate (`Randomized.PolyAmp.runVal_two_ge`) and the amplification error estimate (`Randomized.PolyAmp.two_mul_pow_le`) then give error at most $(1/2)^{(|x|+1)^d}$. In the no case, the original machine's probability of outputting true is at most $1/3$: the probabilities of the two distinct one-bit outputs sum to at most one, by disjointness of those events and the probability bound (`Randomized.randProb_or_disjoint`, `Randomized.randProb_le_one`). The upper amplification estimate (`Randomized.PolyAmp.runVal_two_le`), together with the same error estimate, gives the matching bound on erroneously outputting true. Thus in either case $M$ outputs the membership bit with probability at least the asserted amount.

**Key facts.** `Complexity.LogProg.narm_logspace_ptm`, `Randomized.polyAmp_setting`, `Randomized.PolyAmp.bigK_ge`, `Randomized.PolyAmp.runVal_two_ge`, `Randomized.PolyAmp.two_mul_pow_le`, `Randomized.randProb_or_disjoint`, `Randomized.randProb_le_one`, `Randomized.PolyAmp.runVal_two_le`.

**Caveat.** The supplied statements for the amplification and simulation results are truncated in the payload. The proof uses their stated roles in the source, but the full interface details are not available to spell out further.
