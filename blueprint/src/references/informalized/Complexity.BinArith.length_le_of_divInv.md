<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Div.lean :: Complexity.BinArith.length_le_of_divInv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for division witnesses

**Claim.** If $S$ is a division witness for $z$ in the stated sense, then $|S|\le 7(|z|+1)$.

**Proof.** Unpack the witness, so $S$ is the pairing of the total second projection of $z$ with a nested encoding of $R,r,q$. The proof uses only the two assumed bounds on $|r|+|R|$ and $|q|+|R|$; the value equation and remainder condition are not needed for this length estimate. The length formula for a pair encoding (`Turing.length_pairEncode`) gives the length of each nested pair by adding twice the first component's length, a fixed delimiter contribution of two, and the second component's length. Meanwhile, the component bound (`Complexity.length_pair_components_le`) gives $2|\operatorname{fst}(z)|+|\operatorname{snd}(z)|\le |z|$. Substituting the witness bounds into the nested length formula and using this component inequality yields $|S|\le 7(|z|+1)$ by arithmetic.

**Key facts.** `Complexity.length_pair_components_le`, `Turing.length_pairEncode`.
