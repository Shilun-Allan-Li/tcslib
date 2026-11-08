<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.mem_AC_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Union Characterization of AC

**Claim.** A language belongs to the union of the AC levels exactly when it belongs to some AC level.

**Proof.** By definition, $\mathrm{AC}$ is the union over natural numbers $i$ of the sets $\mathrm{ACLevel}(i)$. Membership in a union is equivalent to membership in one of its constituent sets. Since membership in $\mathrm{ACLevel}(i)$ is, by definition, the predicate $L.\mathrm{InAC}(i)$, the result follows.
