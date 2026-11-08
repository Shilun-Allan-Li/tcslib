<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/NPPoly.lean :: Randomized.NP_subset_NPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP Has Polynomial-Size Circuits

**Claim.** Every language in $\mathrm{NP}$ has a family of fan-in-two Boolean circuits of polynomially bounded size, with polynomially many witness bits, that accepts an input exactly when some assignment to those witness bits makes the circuit output true.

**Proof.** Take any language in $\mathrm{NP}$. The inclusion of $\mathrm{NP}$ in $\mathrm{BPNP}$ places it in the class to which the circuit simulation applies ($\mathrm{NP\_subset\_BPNP}$). The simulation theorem then gives a fan-in-two circuit family with polynomial size and witness bits, and the required equivalence between membership and acceptance for some witness ($\mathrm{BPNP\_subset\_NPPoly}$). Chaining these two inclusions proves the claim.

**Key facts.** `Randomized.NP_subset_BPNP`, `Randomized.BPNP_subset_NPPoly`.
