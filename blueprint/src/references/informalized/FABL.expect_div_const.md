<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.expect_div_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Scaled Function

**Claim.** For a finite set, the uniform average of the function $a\mapsto f(a)/c$ equals the uniform average of $f$ divided by $c$.

**Proof.** Rewrite division by $c$ as multiplication by the constant $c^{-1}$. Linearity of the finite uniform average lets this constant factor outside, giving $(\mathbb E_a f(a))c^{-1}$, which is the stated quotient. This reasoning also covers $c=0$, since division in $\mathbb R$ is defined using the inverse, with $0^{-1}=0$.
