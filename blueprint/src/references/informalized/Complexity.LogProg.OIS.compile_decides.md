<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.compile_decides -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound for Compiled Decisions

**Claim.** Under the stated correctness and space-bound hypotheses for the two deciders, the compiled machine halts on $x$ with output $w$ and uses at most the asserted space bound.

**Proof.** 1. Replace each language-membership oracle by its Boolean indicator. The membership hypotheses say that the first oracle returns the length test $i<|v|$ for all $i\le |v|$, while the second returns the $i$th bit of $v$ for $i<|v|$; the indicator agrees with the corresponding membership decision (`indicator_eq_decide`). The original machine halts with output $w$, by unpacking its time-and-output specification (`Turing.FinTM.computesInTime_iff`).

2. Apply the simulation theorem `run` with these two oracle identities. It supplies a halting run of the recursive program with the same output, together with bounds on every register head and a description of every call encountered: each call is a whole-input query whose sole argument is the extra index tape, containing $\operatorname{bits}(i)$ for some $i\le |v|$. The query word is therefore $\langle x,\operatorname{bits}(i)\rangle$, by `vword_whole₁` and `tapeWord_bufferTape`. Its argument tape is the designated extra tape, and its length is bounded using monotonicity of binary-expansion length (`length_bits_mono`).

3. For each such call, the decider bank correctly decides the queried language and uses at most $\max(s_j(|\langle x,\operatorname{bits}(i)\rangle|),1)$ space (`bank_cleanRun`). The assumed bound makes this at most $B$; monotonicity of clean-run space bounds (`CleanRun.mono`) gives the call condition required by `compile_space`. That compilation theorem then yields a halting compiled machine with output $w$ and its space bound.

4. Finally, separate the compiled machine's original-machine tapes from the two bank blocks in the finite sum defining total space. Substituting the simulation's head bounds and the bank sizes, and simplifying the finite sum, gives
\[M.k(2\,\mathrm{space}_M(v,t)+1)+(|\operatorname{bits}(|v|+1)|+2)+2K(2B+1),\]
where $K=\max((M_0).k,(M_1).k)$ as encoded by the bank tape count.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `Turing.FinTM.computesInTime_iff`, `Complexity.LogProg.OIS.run`, `Complexity.LogProg.vword_whole₁`, `Complexity.LogProg.tapeWord_bufferTape`, `Complexity.LogProg.length_bits_mono`, `Complexity.LogProg.bank_cleanRun`, `Complexity.LogProg.CleanRun.mono`, `Complexity.LogProg.compile_space`.

**Caveat.** The supplied statement for `run` is truncated, but the proof uses precisely its halting, output, head-bound, and call-description conclusions as recorded in the proof source.
