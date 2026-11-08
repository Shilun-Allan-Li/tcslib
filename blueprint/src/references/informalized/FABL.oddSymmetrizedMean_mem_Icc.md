<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oddSymmetrizedMean_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Symmetrized Value Bounds

**Claim.** If a real-valued function on the sign cube takes values in $[-1,1]$, then its symmetrized value is also in $[-1,1]$: it is either $f(x)$ or $-f(-x)$, according to the chosen negation flag.

**Proof.** Split according to whether negation is chosen. If it is, the value is $-f(-x)$. Since $f(-x)\in[-1,1]$, negating reverses the inequalities and gives $-f(-x)\in[-1,1]$. If negation is not chosen, the value is $f(x)$, which lies in the interval by the assumed bound on $f$.
