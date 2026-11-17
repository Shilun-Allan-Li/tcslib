<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProof.lean :: Complexity.LogProg.narm_decides -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondeterministic Logarithmic-Space Decision

**Claim.** If the register machine’s oracle languages are in logarithmic space and its runs satisfy the stated halting, precondition, register-size, and correctness assumptions, then the language it decides belongs to nondeterministic logarithmic space.

**Proof.** For each of the finitely many oracle languages, choose a deterministic machine deciding it in space at most $c_j\,\mathrm{logSpace}(n)$, and let $c_* = \sum_{j<d} c_j$. Each $c_j$ is bounded by this sum. Set $Q=4+2m+2mK$, and choose $K_2$ from the logarithmic bound for polynomials so that $\mathrm{logSpace}(Q(n+1))\le K_2\,\mathrm{logSpace}(n)$. Apply the register-machine simulation theorem `narm_decides_space` with work-space bound $W(n)=K\,\mathrm{logSpace}(n)$ and overall scale $S(n)=\mathrm{logSpace}(n)$. The register bound in the hypothesis gives the simulation’s required bound on $W$. For an oracle query on a virtual input of length $v$, the construction and the register bounds give $v\le Q(n+1)$: the input contributes at most $2n+2$ bits, and the at most $m$ register words contribute at most $m(2K\,\mathrm{logSpace}(n)+2)$ bits. Since $\mathrm{logSpace}(n)\le n+1$, this is at most $Q(n+1)$. The polynomial logarithm bound therefore yields $\mathrm{logSpace}(v)\le K_2\,\mathrm{logSpace}(n)$, so each oracle decider uses at most $c_jK_2\,\mathrm{logSpace}(n)$ space on such a query. Summing these costs and the register simulation cost gives the single bound $(K+c_*K_2)\,\mathrm{logSpace}(n)$. The simulation theorem transfers the halting and acceptance characterization to a nondeterministic Turing machine, proving membership in logarithmic space.

**Key facts.** `Complexity.LogProg.log_poly_bound`, `Complexity.LogProg.narm_decides_space`.
