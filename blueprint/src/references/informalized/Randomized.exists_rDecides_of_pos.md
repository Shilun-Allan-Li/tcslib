<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.exists_rDecides_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amplification of Randomized Decisions

**Claim.** Under the stated space, halting, acceptance-probability, and rejection hypotheses, there are a constant multiplier and a finite nondeterministic machine whose space is bounded by that multiplier times the original space and whose acceptance probability on members of the language is at least $1-\varepsilon$, while every choice word on nonmembers still yields rejection.

**Proof.** 1. Put $d=\min(\delta,1)$. Then $0<d\leq 1$. Choose $n$ so that $(1-d)^{n+1}<\varepsilon$. The amplified machine runs the original machine on $n+1$ independent blocks of $T$ choices and accepts when at least one block accepts. The amplification construction supplies its halting bound (`Randomized.Amplify.amp_haltsWithin`), its output-probability formula in terms of the number of accepting blocks (`Randomized.Amplify.amp_outputProb`), and a space bound with multiplier $3(n+1)N.k$ (`Randomized.amp_usesSpace_mul`).

2. Fix an input in the language. Let $p$ be the original acceptance probability at its supplied time $T$. The accepting-block count is zero precisely when all $n+1$ blocks reject, whose probability is $(1-p)^{n+1}$ by the binomial block-count formula (`Randomized.randProb_blockCount`). Thus the amplified acceptance probability is $1-(1-p)^{n+1}$. Since $p\geq\delta$ and $p\leq1$, we have $p\geq d$, so $(1-p)^{n+1}\leq(1-d)^{n+1}<\varepsilon$. The amplified acceptance probability is therefore at least $1-\varepsilon$.

3. Now fix an input outside the language. Every length-$T$ choice word makes the original machine output false, so its acceptance probability is zero: pointwise agreement on all encoded choice words preserves randomized probability (`Randomized.randProb_congr`), and the false property has probability zero (`Randomized.randProb_false`). Consequently every block rejects, and the amplified machine also rejects on every choice word of its halting length. In the formal conclusion, an arbitrary choice list of that length is represented by a function on its finite index set using the list representation result (`Randomized.exists_ofFn_eq`); probability one for rejection then implies rejection for every such function (`Randomized.forall_of_randProb_eq_one`).

**Key facts.** `Randomized.Amplify.amp_haltsWithin`, `Randomized.amp_usesSpace_mul`, `Randomized.Amplify.amp_outputProb`, `Randomized.randProb_blockCount`, `Randomized.randProb_congr`, `Randomized.randProb_false`, `Randomized.exists_ofFn_eq`, `Randomized.forall_of_randProb_eq_one`.
