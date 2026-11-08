<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean :: Complexity.LogProg.ExpBFS.cell_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Shifted Cell Indices

**Claim.** If $b+v$ and $b+v'$ represent the same integer, then $v=v'$.

**Proof.** The equality of the represented integers is an equality between the natural numbers $b+v$ and $b+v'$, viewed in the integers. The natural-to-integer embedding is injective, so cancel the common summand $b$ to obtain $v=v'$.
