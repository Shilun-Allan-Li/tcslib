<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Reductions.lean :: Randomized.NP_subset_BPNP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP Containment in BPNP

**Claim.** For a fixed verifier model $E$, every language in $\mathrm{NP}$ belongs to $\mathrm{BPNP}$, the class of languages that reduce to $3$-CNF satisfiability in the randomized reduction relation determined by $E$.

**Proof.** Let $L$ be in $\mathrm{NP}$. Since $3$-CNF satisfiability is NP-hard, there is a polynomial-time reduction from $L$ to $\mathrm{SAT3}$ ( `SAT3_NPHard`). Every polynomial-time reduction is also a randomized reduction for the fixed verifier model $E$ ( `RandReducible.of_polyTimeReducible`). Hence $L$ reduces to $\mathrm{SAT3}$ in the required randomized sense, which is exactly membership in $\mathrm{BPNP}$.

**Key facts.** `Complexity.SAT3_NPHard`, `Randomized.RandReducible.of_polyTimeReducible`.
