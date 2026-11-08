<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.coprime_iff_natCast_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coprimality and Nonzero Residues

**Claim.** If $p$ is prime and $A$ is a natural number, then $A$ is coprime to $p$ exactly when its residue modulo $p$ is nonzero.

**Proof.** A natural number has zero residue in $\mathbb{Z}/p\mathbb{Z}$ exactly when it is divisible by $p$. Negating this equivalence says its residue is nonzero exactly when $p$ does not divide $A$. Since $p$ is prime, it is coprime to $A$ exactly when it does not divide $A$; symmetry of coprimality gives the stated equivalence.
