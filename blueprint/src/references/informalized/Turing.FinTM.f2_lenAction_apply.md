<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_lenAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a Length-Counting Action

**Claim.** Applying the length-counting action to the configuration at input position $i$, state $q$, and extra-tape position $r$ gives the corresponding configuration at position $j$, state $q'$, and extra-tape position $s$, with the specified optional output.

**Proof.** Compare the configuration fields. The successor state is $q'$, and the input-head position is the stated one by the hypothesis on its movement. The action writes nothing on any work tape, so all tape contents are unchanged. On each of the original tapes it makes no head movement; on the extra tape the head moves from $r-1$ to $s-1$ by the assumed integer equality. Finally, the action appends the optional bit to the initially empty output, giving exactly its one-bit word or the empty word. Thus every field agrees with the claimed configuration.
