<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.tailShearLinearMap_involutive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involutivity of the tail shear

**Claim.** Applying the tail shear linear map twice to any element of $(\mathbb{F}_2)^m\times(\mathbb{F}_2\times\mathbb{F}_2)$ returns that element.

**Proof.** Write the element as $(x,(a,b))$ and let $s=\sum_i x_i$. The shear leaves $x$ unchanged and adds $s$ to each of the last two coordinates. On a second application, the same sum $s$ is added again, so the result is $(x,((a+s)+s,(b+s)+s))$. Addition is associative, and in $\mathbb{F}_2$ every element added to itself is zero. Hence each last coordinate reduces to its original value, giving $(x,(a,b))$.
