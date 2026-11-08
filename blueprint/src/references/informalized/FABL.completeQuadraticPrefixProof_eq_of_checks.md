<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticPrefixProof_eq_of_checks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Prefix Values from Checks

**Claim.** Under the stated consistency checks, the image in $\mathbb F_2$ of the table's quadratic-prefix entry at each $k\le n$ equals the quadratic value of the first $k$ mapped coordinates.

**Proof.** Proceed by induction over the prefix index. At index $0$, the endpoint check says the table's quadratic-prefix entry is false, whose image in $\mathbb F_2$ is zero. The truncation at length zero is the zero vector, so its quadratic value is also zero. For the successor step, write the current index as $i$. The product check says that the image of the table's product entry at $i$ is the product of the image of the table's linear-prefix entry at $i$ and the image of $w_i$; here the Boolean conjunction check becomes multiplication in $\mathbb F_2$ (`pcppBoolF₂Equiv_and`). The linear-prefix entries agree with the actual linear prefix sums by `completeQuadraticLinearPrefixProof_eq_of_checks`. Meanwhile, the quadratic transition check says that the next quadratic-prefix entry is the sum of the current entry and the product entry. Applying the induction hypothesis and the product identity, this is the current quadratic value plus the linear prefix sum times the image of $w_i$. The quadratic prefix recurrence (`completeQuadraticPrefixBit_succ`) identifies this sum with the quadratic value at length $i+1$, completing the induction.

**Key facts.** `FABL.completeQuadraticLinearPrefixProof_eq_of_checks`, `FABL.pcppBoolF₂Equiv_and`, `FABL.completeQuadraticPrefixBit_succ`.
