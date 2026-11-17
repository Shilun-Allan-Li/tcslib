<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Randomized.compl_mem_BPTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement Closure of BPTIME

**Claim.** For any time bound $T$ and language $L$, if $L$ belongs to BPTIME$(T)$, then its complement also belongs to BPTIME$(T)$.

**Proof.** Membership in BPTIME$(T)$ gives a constant factor $c$, a randomized machine $N$, and a proof that $N$ decides $L$ within the scaled time bound. Retain $c$ and use the machine with its output flipped. The output-flipping theorem says that it decides $L^c$ within the same time bound and with the required bounded-error guarantee (BPDecidesInTime.flipOutput). These witnesses establish membership of the complement in BPTIME$(T)$.

**Key facts.** `Turing.FinNDTM.BPDecidesInTime.flipOutput`.
