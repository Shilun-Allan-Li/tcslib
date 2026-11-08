<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.IsHypercontractiveRandomVariable.const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling a Hypercontractive Variable

**Claim.** If $X$ satisfies the hypercontractive inequality with exponents $p,q$ and parameter $\rho$, then the function $x\mapsto cX(x)$ satisfies the same inequality.

**Proof.** Fix $a,b\in\mathbb R$. In the inequality for $X$, use the inputs $a$ and $bc$. Its left-hand expression is $a+\rho(bc)X(x)$, which equals $a+\rho b(cX(x))$; its right-hand expression is $a+(bc)X(x)=a+b(cX(x))$. Thus this instance is precisely the required inequality for the scaled function.
