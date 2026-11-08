<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.coRP_PTM_subset_BPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CoRP Is Contained in BPP

**Claim.** Every language whose complement is decidable by a randomized Turing machine in polynomial time with one-sided error is decidable by a randomized Turing machine in polynomial time with two-sided error at most $1/3$.

**Proof.** Take $L\in\mathrm{coRP}$. Its complement is in RP, and every RP language is in BPP (RP_PTM_subset_BPP_PTM). Thus $L^c\in\mathrm{BPP}$. BPP is closed under complement (compl_mem_BPP_PTM), so $(L^c)^c\in\mathrm{BPP}$. Since the double complement is $L$, this proves $L\in\mathrm{BPP}$.

**Key facts.** `Randomized.RP_PTM_subset_BPP_PTM`, `Randomized.compl_mem_BPP_PTM`.
