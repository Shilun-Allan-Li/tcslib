<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldAction_safe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safety Under Translated Actions

**Claim.** If a configuration satisfies the fold safety invariant, then applying the translated action using the assigned fold sides and current folded head symbols produces another configuration satisfying that invariant.

**Proof.** Check the three parts of the safety invariant. First, the translated successor state is either the encoded image of an ordinary successor state or the designated nonhalting control state, so it is never the forbidden halted encoding. Next, the new head position on tape $i$ is the old position plus the translated movement. The invariant identifies the stored origin marker with whether the old position is zero; the nonnegativity property of the folding movement (`foldMove_nonneg`) then shows that the new position remains nonnegative. Finally, fix any nonnegative tape position $p$. If the action does not write on tape $i$, its tape contents are unchanged, so the marker condition follows from the old invariant. If it writes, consider whether $p$ is the head's current position. At that position, the translated write preserves the origin marker (`foldWrite_origin`), so the invariant remains true. At any other position, the update changes nothing there, and the old invariant applies.

**Key facts.** `Turing.FinTM.foldMove_nonneg`, `Turing.FinTM.foldWrite_origin`.
