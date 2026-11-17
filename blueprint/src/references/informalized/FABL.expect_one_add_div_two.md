<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.expect_one_add_div_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average of an affine function

**Claim.** For a finite nonempty set $\Omega$ and $g:\Omega\to\mathbb R$, the uniform average of $(1+g(x))/2$ equals $(1+\mathbb E_x g(x))/2$.

**Proof.** Linearity of the uniform average lets us move the division by $2$ outside and split the average of $1+g$ into the average of the constant function $1$ and the average of $g$. Since $\Omega$ is nonempty, the uniform average of the constant function $1$ is $1$. Thus the result is $(1+\mathbb E_x g(x))/2$.
