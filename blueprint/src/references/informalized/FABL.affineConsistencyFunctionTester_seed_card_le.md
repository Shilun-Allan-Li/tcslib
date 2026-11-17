<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.affineConsistencyFunctionTester_seed_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Tester Seed-Space Bound

**Claim.** For every positive natural number $d$, the seed space of the affine consistency tester on dimension $d$ has cardinality at most $2^{3(d+1)^2}$.

**Proof.** The seed is a pair consisting of a coordinate in $\mathrm{Fin}(d)$ and a vector in $(\mathbb{F}_2)^d$. Its cardinality is therefore $d\,2^d$. Since $d\le 2^d$, this is at most $2^d2^d=2^{2d}$. Finally, $2d\le 3(d+1)^2$, so monotonicity of powers of $2$ gives the stated bound.
