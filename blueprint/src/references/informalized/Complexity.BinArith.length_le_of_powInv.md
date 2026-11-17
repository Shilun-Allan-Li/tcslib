<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean :: Complexity.BinArith.length_le_of_powInv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for power witnesses

**Claim.** If $S$ is a power witness for $z$ satisfying the stated conditions, then $|S|\le 9(|z|+1)$.

**Proof.** Unpack the witness, so $S$ is a nested pair encoding of the indicated second projection, $E$, $b$, and $\mathrm{acc}$. The proof needs only the stated bounds on $|E|$, $|b|$, and $|\mathrm{acc}|$; the value, canonical representation, and congruence conditions are not used. Apply the pair encoding length formula (`Turing.length_pairEncode`) to expand the lengths of the nested pairs. The component bound for $z$ and then for its total second projection (`Complexity.length_pair_components_le`) control the lengths of the projections appearing in those bounds. Substituting these inequalities into the expanded encoding length gives $|S|\le 9(|z|+1)$ by arithmetic.

**Key facts.** `Complexity.length_pair_components_le`, `Turing.length_pairEncode`.
