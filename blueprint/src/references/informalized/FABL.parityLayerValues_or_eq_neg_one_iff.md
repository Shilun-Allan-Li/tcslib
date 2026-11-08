<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityLayerValues_or_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# OR Layer Value Characterisation

**Claim.** For the OR layer, the value at an index is $-1$ exactly when the parity block assignment in its corresponding pair differs from the actual assignment at that pair's position.

**Proof.** Let the pair corresponding to the index have block assignment $a$ and position $g$. If $a$ matches the actual assignment at $g$, the definition of the exact OR node value gives $1$. If they differ, it gives $-1$. Hence the value is $-1$ exactly when they differ.
