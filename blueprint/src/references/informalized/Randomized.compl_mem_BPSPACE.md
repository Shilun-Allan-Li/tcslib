<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.compl_mem_BPSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement Closure of BPSPACE

**Claim.** For any space bound $s$ and language $L$, if $L$ belongs to BPSPACE$(s)$, then its complement also belongs to BPSPACE$(s)$.

**Proof.** Membership in BPSPACE$(s)$ supplies a constant factor, a randomized machine $N$, and a proof that $N$ decides $L$ within that scaled space bound. Keep the same factor and machine, but flip its output. The output-flipping theorem states that this machine decides the complement with the same space usage (BPDecidesInSpace.flipOutput). These data witness that $L^c$ belongs to BPSPACE$(s)$.

**Key facts.** `Turing.FinNDTM.BPDecidesInSpace.flipOutput`.
