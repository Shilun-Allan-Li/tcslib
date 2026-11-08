<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satSplitClause_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of Clause Splitting

**Claim.** If every variable in a clause $C$ has index below $n$ and an assignment $a$ satisfies $C$, then some assignment $a'$ agrees with $a$ below $n$ and satisfies the CNF formula produced by splitting $C$ at cursor $n$.

**Proof.** Split on whether $C$ is empty. The empty clause has evaluation false, contradicting the assumed satisfaction, so that case is impossible. Otherwise write $C$ as its first literal followed by the remaining literals. The upstream completeness result for the chain construction (`satChain_complete`) applies to this nonempty clause, using the given variable bound and satisfaction hypothesis. It supplies an assignment agreeing with $a$ on all indices below $n$ and satisfying the CNF produced by the chain. For a nonempty clause, the splitting construction is exactly this chain construction, which yields the required assignment and conclusion.

**Key facts.** `Complexity.satChain_complete`.
