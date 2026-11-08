<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.mul_logb_two_inv_lt_one_third -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic bound for small parameters

**Claim.** For $0<x\le1/10$, the quantity $x\log_2(1/x)$ is less than $1/3$.

**Proof.** Set $u=1/x$, so $u\ge10$. The function $u\mapsto\log(u)/u$ is nonincreasing once $u\ge e$; since $e<3<10$, this gives $\log(1/x)/(1/x)\le\log(10)/10$. The left side equals $x\log(1/x)$. The numerical logarithm bounds used in the proof imply $\log(10)/10<\log(2)/3$, so $x\log(1/x)<\log(2)/3$. Finally, $\log(2)>0$ and $\log_2(1/x)=\log(1/x)/\log(2)$; dividing the preceding strict bound by $\log(2)$ yields the result.
