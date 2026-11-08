<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.pairLenCheckTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial length check time bound

**Claim.** For all natural numbers $C,e$, the length-checking machine outputs the one-bit truth value of whether a successful decoding $(a,b)$ satisfies $|b|\le C(|a|+1)^e$, and otherwise outputs $0$. On inputs of length $n$, it halts within $(C+5e+17)((n+1)^e+n+1)$ steps.

**Proof.** Fix an input $x$. First, the proof establishes that the length of the decoded first component, taken to be empty on decoding failure, is at most $|x|$. In the successful case, the decoding characterization gives $x=\operatorname{pairEncode}(a,b)$, whose length is $2|a|+2+|b|$ (`length_pairEncode`), so in particular $|a|\le |x|. Raising the inequality $|a|+1\le |x|+1$ to the power $e$ preserves it. The first-component extractor followed by the unary polynomial machine therefore computes a unary word of length $C(|a|+1)^e$: the buffered composition bound (`bufferedCompTM_computesInTime`) gives a time no greater than $(C+5e+12)((|x|+1)^e+|x|+1)$ after the power and length estimates. The proof's arithmetic bounds this composition time using the unary machine's stated bound and the extractor's $5(|x|+1)$ bound. Next, the pair-counting result (`pairCount_computes`) applies to this computed unary word. It outputs true exactly when decoding succeeds and the second component's length is at most the unary word's length, and its extra time is at most $2|x|+5$. In the failure case its output is false. Unfolding the composite machine identifies this with the desired one-bit output. Combining the two time estimates gives $(C+5e+12)((|x|+1)^e+|x|+1)+2|x|+5$, which is at most $(C+5e+17)((|x|+1)^e+|x|+1)$; computation-time monotonicity (`ComputesInTime.mono`) yields the claimed bound.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Turing.length_pairEncode`, `Turing.FinTM.pairExtractTM_fst`, `Turing.FinTM.polyUnaryTM_computes`, `Turing.FinTM.bufferedCompTM_computesInTime`, `Turing.FinTM.pairCount_computes`, `Turing.FinTM.ComputesInTime.mono`.
