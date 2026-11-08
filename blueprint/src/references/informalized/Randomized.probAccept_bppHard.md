<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPHard.lean :: Randomized.probAccept_bppHard -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hardness of Probabilistic Acceptance

**Claim.** For every code $c$ of a binary-choice probabilistic Turing machine, its bounded-time acceptance language is hard for $\mathsf{BPP}$ under polynomial-time many-one reductions.

**Proof.** Take any language $L$ in $\mathsf{BPP}$. It has a finite probabilistic machine $N$ and a time bound $a(n^e+1)$ meeting the stipulated acceptance thresholds. Choose a code $M$ representing $N$, and let $\alpha$ be the encoding of $M$ by $c$. On input $x$, output the pair encoding of $\alpha$ and the pair encoding of $x$ with a unary time parameter $t=2a(|x|+1)^e$. The polynomial-time encoding facts show this is a polynomial-time map. The elementary bound $n^e+1\le2(n+1)^e$ ensures that $t$ is at least the original running-time bound. Since $N$ halts within that bound, its probability of accepting by time $t$ equals its probability of outputting the accepting symbol at the original bound. The code decoding identity and the representation of $N$ by $M$ preserve this output probability. Pair-encoding injectivity shows that the constructed string belongs to the acceptance language exactly when this probability is at least $2/3$. If $x\in L$, that follows from $N$'s completeness guarantee. If $x\notin L$, the probability of outputting the accepting symbol is at most one minus the probability of outputting the rejecting symbol: these are disjoint outcomes. The soundness guarantee bounds the latter probability below by $2/3$, so the accepting probability is at most $1/3$. Hence the constructed string is outside the language, establishing the reduction.

**Key facts.** `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_polyUnary`, `Randomized.pow_add_one_le_two_mul`, `Turing.FinNDTM.exists_codePTM`, `Turing.PTMCode.decode_encode`, `Turing.FinNDTM.acceptWithinProb_eq_outputProb`, `Randomized.randProb_congr`, `Turing.pairEncode_injective`, `Randomized.randProb_not`, `Randomized.randProb_mono`.
