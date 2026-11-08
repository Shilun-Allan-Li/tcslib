<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.re_I_pow_eq_zero_of_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Part of an Odd Power of the Imaginary Unit

**Claim.** For every odd nonnegative integer $k$, the real part of $i^k$ is zero.

**Proof.** Write $k=2m+1$ using oddness. Then $i^k=i(i^2)^m=i(-1)^m$. The factor $(-1)^m$ is real, so this product is purely imaginary. Its real part is therefore zero.
