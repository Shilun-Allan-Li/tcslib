<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.inBPPWith_of_mem_BPP_PTMWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondeterministic Choices as Random Bits

**Claim.** If a language is decided by a nondeterministic polynomial-time machine that halts on every prescribed-length choice string and achieves correctness probability at least $p(n)$, then a polynomial-time randomized verifier achieves the same correctness bound on every input.

**Proof.** Choose an exponent and running-time constant witnessing membership in the nondeterministic polynomial-time class, and write $N$ for the corresponding machine. The polynomial-time choice-verifier theorem supplies a polynomial-time decidable language $V$ encoding accepting computations of $N$ on a given input and choice string (\texttt{Complexity.exists\_choiceVerifier\_mem\_P}). Use the verifier that, on input $x$ and random string $r$, tests whether $x\mathbin{++}r$ belongs to $V$. Its efficiency follows from the polynomial-time append-membership construction (\texttt{Randomized.eff\_append\_mem}).

For input length $n$, let $T$ be the machine's time bound and let $Q$ be the verifier's random-string length. The choice-budget inequality ensures $T\le Q$ (\texttt{Turing.choiceBudget\_le}). A uniformly chosen string of length $Q$, when truncated to length $T$, is uniformly distributed among length-$T$ strings (\texttt{Randomized.randProb\_take}). The choice-verifier characterization identifies acceptance on a length-$Q$ string with the machine halting with output true on its first $T$ choices (\texttt{Randomized.append\_mem\_iff\_outputWith\_take}); the corresponding probability equality transfers the machine's true-output probability to the verifier (\texttt{Randomized.randProb\_choiceVerifier}).

If $x$ belongs to the language, the machine's probability of outputting true is at least $p(n)$, so the verifier's probability of outputting true is also at least $p(n)$. If $x$ does not belong, the assumed correctness bound is a lower bound on the probability of outputting false. The verifier outputs false whenever the encoded string is not in $V$; the indicator characterization and monotonicity of probability under event inclusion (\texttt{Randomized.indicator\_eq\_false\_iff}, \texttt{Randomized.randProb\_mono}) give the same lower bound for that event. Thus the constructed verifier meets both correctness conditions.

**Key facts.** `Complexity.exists_choiceVerifier_mem_P`, `Randomized.eff_append_mem`, `Turing.choiceBudget_le`, `Randomized.randProb_take`, `Randomized.append_mem_iff_outputWith_take`, `Randomized.randProb_choiceVerifier`, `Randomized.indicator_eq_false_iff`, `Randomized.randProb_mono`.
