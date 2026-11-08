<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingCode.fullCoefficient_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full-Coefficient Tail Bound

**Claim.** For every integer $i\geq4$, with $c_i=((2^i-1)(4/9)^i)/i!$, one has $c_i\leq(32/3)(2/9)^i$.

**Proof.** First bound $2^i-1\leq2^i$. The factorial lower bound `factorial_ge_twentyFour_mul_four_pow` gives $i!\geq24\cdot4^{i-4}$. Substituting these bounds into $c_i$ yields $c_i\leq 2^i(4/9)^i/(24\cdot4^{i-4})$. Writing $i=4+t$ and collecting powers reduces this expression to $(32/3)(2/9)^i$, proving the claim.

**Key facts.** `FABL.SwitchingCode.factorial_ge_twentyFour_mul_four_pow`.
