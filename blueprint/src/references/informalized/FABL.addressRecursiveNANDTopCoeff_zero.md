<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.addressRecursiveNANDTopCoeff_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial NAND top coefficient

**Claim.** The top coefficient of the depth-zero recursively composed two-input NAND function is $1$.

**Proof.** At depth zero, the address space is a singleton, so the recursively composed function simply returns the unique input sign. Reindexing the expectation over sign assignments on this singleton as an expectation over a single sign $s$, the integrand becomes $s^2$. The sign set consists of $1$ and $-1$, each with equal weight; since both squares are $1$, their average is $1$.
