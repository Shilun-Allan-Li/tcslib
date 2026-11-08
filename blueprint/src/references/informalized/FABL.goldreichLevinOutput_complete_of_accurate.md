<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.goldreichLevinOutput_complete_of_accurate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Goldreich–Levin output

**Claim.** If the restricted Fourier weight estimates are accurate and the algorithm outputs an active family, then every frequency whose Fourier coefficient has magnitude at least the threshold belongs to that family.

**Proof.** Fix a heavy frequency set $U$. The heavy-prefix propagation theorem says that, at every stage, its restriction to that stage’s prefix belongs to the active family produced by the run, provided the estimates are accurate (`heavy_prefix_mem_goldreichLevinRunUpTo`). Apply this at the terminal stage $n$, where the algorithm’s output is precisely the run’s active family. At that stage the prefix restriction of $U$ equals $U$ itself, because every coordinate in the $n$-dimensional cube lies in the first $n$ coordinates (`prefixFrequency_eq_self`). Hence $U$ belongs to the output family.

**Key facts.** `FABL.heavy_prefix_mem_goldreichLevinRunUpTo`, `FABL.prefixFrequency_eq_self`.
