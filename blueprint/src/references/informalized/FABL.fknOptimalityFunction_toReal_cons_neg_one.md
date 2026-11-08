<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalityFunction_toReal_cons_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at a Negative First Coordinate

**Claim.** At the vector whose first coordinate is $-1$, the real-valued constructed function equals twice the small-set indicator minus one.

**Proof.** Split according to whether the normalized sum of the remaining coordinates exceeds the threshold. If it does, the small-set indicator equals $1$, and the constructed Boolean function selects the value $1$; its real-valued version is therefore $1=2\cdot1-1$. If it does not, the indicator equals $0$ and the function selects the first coordinate, which is $-1$; its real-valued version is $-1=2\cdot0-1$. These cases establish the formula.
