<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.two_pow_mul_sqrt_clog_add_one_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic exponent bound

**Claim.** For all natural numbers $n,H$, writing $r=\operatorname{clog}_2(n+1)$, one has $2^{H(\lfloor\sqrt r\rfloor+1)}\le 2^{2H}(n+1)^H$.

**Proof.** Set $L=\operatorname{clog}_2(n+1)$ and $s=\lfloor\sqrt L\rfloor+1$. Since $\lfloor\sqrt L\rfloor\le L$, we have $s\le L+1$. Monotonicity of natural powers therefore bounds $2^{Hs}$ by $2^{H(L+1)}$. Rearranging the exponent and using the laws of exponents writes the latter as $2^H(2^L)^H$. The binary ceiling logarithm bound gives $2^L\le2(n+1)$ (\texttt{FABL.two\_pow\_clog\_le\_two\_mul}), so taking the $H$th power and multiplying by $2^H$ bounds this by $2^H(2(n+1))^H=2^{2H}(n+1)^H$.

**Key facts.** `FABL.two_pow_clog_le_two_mul`.
