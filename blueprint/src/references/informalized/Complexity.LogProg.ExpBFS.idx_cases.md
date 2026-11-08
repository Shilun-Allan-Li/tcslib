<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.idx_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory Access Register Cases

**Claim.** For every memory-access site, its associated register is either $U$ or $V$.

**Proof.** Inspect the constructors of a memory-access site. The sites that access $V$ are the relaxation-round read of $V$ and the marking of $V$; their associated register is $V$. Every other site has associated register $U$. Hence in all cases the associated register equals one of the two stated registers.
