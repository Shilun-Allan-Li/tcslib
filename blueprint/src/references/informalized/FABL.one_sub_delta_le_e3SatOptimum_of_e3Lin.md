<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.one_sub_delta_le_e3SatOptimum_of_e3Lin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# E3-Lin Optimum Transfers to E3-Sat

**Claim.** For a finite-variable E3-Lin instance $P$, if $0\le\delta$ and its optimum is at least $1-\delta$, then the optimum of its associated E3-Sat instance is also at least $1-\delta$.

**Proof.** The optimum of the associated E3-Sat instance is $3/4+P.\mathrm{optimum}/4$ (`FABL.optimum_e3LinToE3Sat`). Using $P.\mathrm{optimum}\ge1-\delta$, this is at least $3/4+(1-\delta)/4=1-\delta/4$. Since $\delta\ge0$, we have $1-\delta/4\ge1-\delta$, proving the claim.

**Key facts.** `FABL.optimum_e3LinToE3Sat`.

**Caveat.** The supplied informal statement describes a different approximation implication; this account follows the formal theorem and its proof.
