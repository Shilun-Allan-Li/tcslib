<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.log_48_mul_le_seven_log -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Bound for Integers at Least Two

**Claim.** For every integer $n\ge 2$, $\log(48n)\le 7\log n$.

**Proof.** Since $n\ge2$, we have $48\le 2^6\le n^6$. Multiplying by $n$ gives $48n\le n^7$. Both sides are positive, so monotonicity of the logarithm yields $\log(48n)\le\log(n^7)$. The logarithm power rule gives $\log(n^7)=7\log n$.
