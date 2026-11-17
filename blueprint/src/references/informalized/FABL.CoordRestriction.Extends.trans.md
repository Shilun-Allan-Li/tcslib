<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.Extends.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of restriction extension

**Claim.** If η extends ρ and τ extends η, then τ extends ρ: every coordinate fixed by ρ has the same state in τ.

**Proof.** Take any coordinate $i$ where $\rho(i)$ is not free. Since η extends ρ, we have $\eta(i)=\rho(i)$, so η is also not free at $i$. Since τ extends η, it follows that $\tau(i)=\eta(i)$. Combining the equalities gives $\tau(i)=\rho(i)$, proving the extension condition.
