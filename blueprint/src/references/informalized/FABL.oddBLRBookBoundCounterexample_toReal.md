<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.oddBLRBookBoundCounterexample_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Form of the Counterexample

**Claim.** At every point $x$ of the two-dimensional sign cube, the real-valued negative OR function equals $\bigl(1-x_0-x_1-x_0x_1\bigr)/2$.

**Proof.** Fix a point $x$ and write $a=x_0$, $b=x_1$. Since the cube has two coordinates, $x$ is the pair $(a,b)$. Each coordinate is either $1$ or $-1$, so there are four cases. If both are $1$, the negative OR is $-1$ and the expression $(1-a-b-ab)/2$ is also $-1$. In each of the other three cases, the negative OR is $1$, and direct substitution gives $1$ for the expression as well. The monomials for the two singleton sets and their pair are respectively $a$, $b$, and $ab$, yielding the stated formula.
