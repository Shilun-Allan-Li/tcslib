<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide.lean :: Complexity.PathHard.wAns_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement with the Language Indicator

**Claim.** For every input string $x$, index $i$, and Boolean mode, the value of $\mathrm{wAns}$ at the specified parameters equals the indicator of whether the paired encoding of $x$ and the binary expansion of $i$ belongs to the indexed language $qLang$.

**Proof.** First observe from the definition of $nV$ that the chosen vertex count is $2^E$, where $E=\mathrm{codeK}(N)(c_0+1)\ell(|x|)+(\mathrm{codeK}(N)+2)$. In length mode, membership in $qLang$ asks whether $i$ is below the length of the reduction output. The output-length formula gives that length as $2(2^E)^2+2\cdot2^E+7$, exactly the cutoff used by $\mathrm{wAns}$, so the two Boolean values agree. In bit mode, membership asks whether the $i$th bit of the reduction output is true. The reduction's indexed-bit formula splits into the initial unary block, the two separator bits, the adjacency-matrix block, and the fixed tail. Its cases and values match the corresponding cases in the definition of $\mathrm{wAns}$; within the matrix block, both use the same edge predicate with the same decoded source and target indices. The reduction-bit formula supplies this correspondence, and the indicator theorem for indexed languages identifies membership of the paired encoding with the truth value of that bit predicate.

**Key facts.** `Complexity.PathHard.length_red`, `Complexity.PathHard.red_getD`, `Complexity.indicator_indexLang_pairEncode`.
