<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_machine_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier behavior on split inputs

**Claim.** For every binary word $z$, the verifier outputs $B(z)$ on the specified split encoding within $40(|z|+1)$ steps.

**Proof.** If the bounded split search has no solution, then the split encoding is empty and $B(z)=0$. The empty-input machine result gives output $[\mathrm{false}]$ in two steps; by monotonicity of the time bound, this is also a computation within $40(|z|+1)$ steps. If the search returns an index $i$, the split-search property gives $|z|=i+(i+1)$. Since the search only considers indices at most $|z|$, we also have $i\le |z|$. Hence the suffix $z.drop\ i$ has length $i+1$, while the prefix is $z.take\ i$. The pair-input machine result therefore applies to these two words: it outputs the negation of the decoded DNF's evaluation under the suffix assignment, which is exactly $B(z)$. Its time bound is $10$ times the encoded input length plus one. The pair-encoding length formula, together with the split equation, bounds this time by $40(|z|+1)$; monotonicity extends the computation to the stated bound.

**Key facts.** `Complexity.taut_machine_empty`, `Turing.FinTM.ComputesInTime.mono`, `Complexity.taut_split_some`, `Complexity.taut_machine_pair`, `Turing.universal_pair_length`.
