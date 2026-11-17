<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean :: Complexity.LogProg.ISGen.gen_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Generator initialization decides the complement

**Claim.** Under the stated space bound and code-size hypotheses, the generator started in its scanning state with all registers zero terminates with every register at most $B$ and accepts exactly when $x\notin L$.

**Proof.** First, the input-length oracle query on the encoding of $(x,\operatorname{bits}(m))$ answers whether $m<|x|$ for every $m\le |x|$. This follows from the oracle's definition through the indicator formula for encoded index-language queries (`Complexity.indicator_indexLang_pairEncode`). The exponent used by the generator is large enough for its setup: since $E\ge1$, the inequality $2^{\operatorname{lgv}(|x|)}\le 2^{2E\operatorname{lgv}(|x|)+2E(sp(|x|)+1)}$ holds, and $\operatorname{lgv}(|x|)<2^{\operatorname{lgv}(|x|)}$. The loop theorem, applied with the space parameter $s=sp(|x|)+1$ and the initial zero state, therefore supplies termination, the register bound, and the complement acceptance condition at the first round state. The initialization theorem then uses the input-length oracle answers to pass from the scanning state to that round state, preserving those conclusions.

**Key facts.** `Complexity.indicator_indexLang_pairEncode`, `Complexity.LogProg.ISGen.loop_run`, `Complexity.LogProg.ISGen.start_run`.
