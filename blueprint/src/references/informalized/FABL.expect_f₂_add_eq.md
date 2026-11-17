<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.expect_f₂_add_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Binary Affine Equation

**Claim.** For $a,r\in\mathbb F_2$, a uniformly chosen $h\in\mathbb F_2$ satisfies $h+a=r$ with probability $1/2$.

**Proof.** For each $h$, the equation $h+a=r$ is equivalent, by subtracting $a$ from both sides, to $h=r-a$. Exactly one element of $\mathbb F_2$ has this value. Thus the indicator is $1$ at one of the two possible choices of $h$ and $0$ at the other, so its uniform average is $1/2$.
