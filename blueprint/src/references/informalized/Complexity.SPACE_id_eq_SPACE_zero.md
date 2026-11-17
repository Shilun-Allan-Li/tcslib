<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean :: Complexity.SPACE_id_eq_SPACE_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear and zero space classes

**Claim.** The class of binary languages decidable in space bounded by a constant multiple of the input length equals the class decidable in space bounded by a constant multiple of zero.

**Proof.** Apply the vanishing-bound equality to the function $s(n)=n$. It vanishes at $n=0$, so the result gives $\mathrm{SPACE}(n)=\mathrm{SPACE}(0)$.

**Key facts.** `Complexity.SPACE_eq_zero_of_exists_zero`.
