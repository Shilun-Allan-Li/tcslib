<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityLayerValues_and_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# AND Layer Value Characterisation

**Claim.** For the AND layer, the value at an index is $-1$ exactly when the parity block assignment in its corresponding pair equals the actual assignment at that pair's position.

**Proof.** Let the pair corresponding to the index have block assignment $a$ and position $g$. Split into the two possibilities: $a$ equals the actual assignment at $g$, or it does not. By the definition of the exact AND node value, a match gives value $-1$, while a mismatch gives value $1$. Thus the value is $-1$ exactly in the matching case.
