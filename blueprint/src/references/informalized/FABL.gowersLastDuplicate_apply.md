<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersLastDuplicate_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last-coordinate duplication identity

**Claim.** Duplicating the last coordinate of a family at a value $b$ and evaluating at $s$ gives the original family evaluated at the point with the first $k$ coordinates of $s$ and last coordinate $b$.

**Proof.** By definition, last-coordinate duplication evaluates the original family at the function obtained from $s$ by replacing its last coordinate with $b$. The coordinates before the last are exactly those of the initial segment of $s$, so this updated function is the concatenation of that initial segment with $b$. Therefore the value is $F(\operatorname{snoc}(\operatorname{init}(s),b))$, as claimed.
