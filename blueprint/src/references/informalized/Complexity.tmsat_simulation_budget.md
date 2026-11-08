<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_simulation_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Simulation Budget

**Claim.** A polynomial bound on the canonizer's time implies a uniform polynomial bound on the stated simulation budget whenever the code length and simulated time are bounded by $m$.

**Proof.** Choose constants $C,e$ witnessing the polynomial bound, so $T_c(n)\le C(n+1)^e$. Set $p=\max(1,e)$. When $r\le m$, we have $r\le(m+1)^p$, and monotonicity of powers and the bound on $T_c(r)$ give $T_c(r)\le C(m+1)^p$. Thus $3r+14T_c(r)+50\le(3+14C+50)(m+1)^p$, using $(m+1)^p\ge1$ to absorb the constant term. Since $t\le m$, also $(t+1)^2\le(m+1)^2$. Multiplying the inequalities proves the claim with $A=3+14C+50$ and $d=p+2$.
