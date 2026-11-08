<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.get_positionOfSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# List Position of a Supported Literal

**Claim.** For a coordinate $i$ in the support of $T$, the list entry at the position selected for that coordinate is the literal selected from $T$ at $i$.

**Proof.** By definition, the selected literal at $i$ belongs to the list of literals of $T$ (\texttt{literalAt\_mem}). The position of a list member is chosen together with the property that the list entry at that position equals that member. Applying this defining property to the selected literal yields the claimed equality.

**Key facts.** `FABL.DNFTerm.literalAt_mem`.
