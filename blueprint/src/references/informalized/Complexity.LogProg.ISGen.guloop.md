<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean :: Complexity.LogProg.ISGen.guloop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner Enumeration Counting Invariant

**Claim.** Under the stated hypotheses, the machine at the inner-enumeration test terminates within register bound $B$ and accepts exactly when the recursive count condition holds with terminal condition $c=\sigma.cp$ and $Q$.

**Proof.** Induct on the number $\sigma.K-\sigma.u$ of codes left to enumerate, strengthening the statement to allow any state satisfying the displayed bounds and zero conditions. When no codes remain, the machine tests whether the current count equals $\sigma.cp$. If it does, it clears the scratch registers and continues to the supplied computation at the next outer vertex; otherwise it rejects. Thus acceptance is exactly the terminal count condition together with $Q$.

For a positive number of remaining codes, the machine chooses whether to count the current code $u$. On the count branch, it checks that $u$ belongs to the current ball, differs from $v$, and has no edge to $v$. The walk-based membership test is supplied by `gwalk_spec`; the equality check and type-$3$ oracle query establish the other two requirements. If all checks succeed, the count is incremented and the induction hypothesis applies at $u+1$ with the updated count. If the machine skips counting $u$, the recursive predicate takes its second branch, which is always true, and the induction hypothesis applies with the count unchanged. In both branches the next recursive condition is therefore exactly the one required by the current `GS` clause. The choice of these branches realizes the disjunction in the definition of `GS`, while the induction hypothesis supplies termination and the stated acceptance characterization for the continuation. The register bound is preserved by the given bounds and $K+1\le B$.

**Key facts.** `Complexity.LogProg.ISGen.gwalk_spec`.
