<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_verifier_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Non-Tautology Verification

**Claim.** The language of binary strings whose length admits a split into a formula prefix of length $i$ and an assignment suffix of length $i+1$, for which the decoded DNF evaluates to false, belongs to $\mathrm{P}$.

**Proof.** The verifier first computes the split determined by the input length. The split-search machine computes this split in time bounded by a constant times $(n+1)^3$. Composing it with the verifier machine, which checks the split and evaluates the decoded formula in time linear in the input length, gives a machine computing the verifier’s output bit in time at most twice the split-search bound plus the verification bound and a fixed overhead. The verifier language is defined by that bit being true; its characteristic indicator therefore agrees with the computed output. By the characterization of membership in $\mathrm{P}$, it remains to bound this composed running time by a polynomial of the required form. Since $n+1\le(n+1)^3$ and $1\le(n+1)^3$, the linear verification term and fixed overhead are absorbed into the cubic bound. Increasing the constant accordingly yields the claimed polynomial-time decision procedure.

**Key facts.** `Turing.FinTM.computesFunInTime_splitSolve`, `Complexity.taut_comp_on_image`, `Complexity.taut_machine_split`, `Complexity.mem_P_iff`, `Turing.FinTM.ComputesInTime.mono`.
