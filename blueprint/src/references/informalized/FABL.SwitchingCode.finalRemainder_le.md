<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingCode.finalRemainder_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Remainder Bound

**Claim.** For every integer $i\geq2$, the quantity $(4/9)^i/i!$ is at most $8/81$.

**Proof.** Because $0<4/9<1$ and $i\geq2$, the power $(4/9)^i$ is at most $(4/9)^2$. Also, $i!\geq2$. Both quantities are positive, so these bounds give $(4/9)^i/i!\leq (4/9)^2/2=8/81$.
