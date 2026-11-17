<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.expect_majorityCoalitionSplit_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation over a split sign cube

**Claim.** For a uniformly random sign vector of length $k+m$, the expected value of a function of the last $m$ coordinates equals that function's uniform expectation on the $m$ dimensional sign cube.

**Proof.** Use the coordinate-splitting bijection between the sign cube of length $k+m$ and the product of cubes of lengths $k$ and $m$. A bijection preserves uniform expectation, so the left-hand side becomes the expectation over pairs $(u,y)$ of $g(y)$. Averaging first over $y$ gives a quantity independent of $u$; averaging that constant over $u$ leaves it unchanged. This is exactly the uniform expectation of $g$ on the tail cube.
