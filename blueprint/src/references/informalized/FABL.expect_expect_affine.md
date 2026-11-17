<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.expect_expect_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Rule for Iterated Averages

**Claim.** For finite nonempty sets $X,Y$, the iterated uniform average of $c+d g(x,y)$ equals $c+d$ times the iterated uniform average of $g(x,y)$.

**Proof.** For each fixed $x$, averaging over $y$ distributes over addition, and the average of the constant $c$ is $c$. The scalar factor $d$ pulls out of that inner average, so it becomes $c+d$ times the inner average of $g(x,y)$. Now average this expression over $x$: addition again distributes, the average of $c$ remains $c$, and $d$ pulls out. The result is $c+d$ times the iterated average of $g$.
