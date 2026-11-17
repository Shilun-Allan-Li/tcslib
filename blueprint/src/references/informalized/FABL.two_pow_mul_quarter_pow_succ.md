<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.two_pow_mul_quarter_pow_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power identity

**Claim.** For every natural number $j$, $2^j(1/4)^{j+1}=(1/4)(1/2)^j$.

**Proof.** Write $(1/4)^{j+1}=(1/4)^j(1/4)$. Commuting and regrouping factors gives $2^j(1/4)^j(1/4)=(1/4)(2^j(1/4)^j)$. The product of equal powers is the power of the product, and $2\cdot(1/4)=1/2$, so the latter expression is $(1/4)(1/2)^j$.
