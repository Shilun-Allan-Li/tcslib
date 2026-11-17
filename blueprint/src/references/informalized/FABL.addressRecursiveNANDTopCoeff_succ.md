<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.addressRecursiveNANDTopCoeff_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NAND Top Coefficient Recurrence

**Claim.** For every depth $d\in\mathbb{N}$, the top coefficient of the depth-$(d+1)$ recursively composed two-input NAND function equals one half the square of the depth-$d$ top coefficient.

**Proof.** Fix a depth $d$. For a block of inputs, write $F$ for the recursively computed NAND sign and $P$ for the product of all input signs in that block. The mean of $P$ is zero because full parity has mean zero. Re-index the expectation on all inputs at depth $d+1$ as an average over pairs of blocks. The sign of the NAND of two signs $F_1,F_2$ is $(-1-F_1-F_2+F_1F_2)/2$, and the full parity is $P_1P_2$. The NAND-parity averaging identity, using the zero mean of block parity, reduces the expectation of their product to $\frac12(\mathbb{E}[FP])^2$. This single-block correlation is the depth-$d$ top coefficient, so the stated recurrence follows.

**Key facts.** `FABL.expect_fullParity_eq_zero`, `FABL.signValue_nandPair`, `FABL.expect_nandParity_step`.
