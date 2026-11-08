<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPoly_advance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advance into a Loop Level

**Claim.** One step from advance state $i$ moves head $i$ one cell to the right and enters loop state $i$, leaving the other head positions and the output unchanged.

**Proof.** The advance transition at index $i$ selects head $i$, moves it right, and changes the control state to loop $i$. The general movement calculation (the effect of `catalogPolyMove_apply`) gives the new head-position function as $h$ updated at $i$ to $h(i)+1$. Since this transition makes no writes or output, all tape contents and the output are preserved. The input head also stays fixed.

**Key facts.** `Turing.FinTM.catalogPolyMove_apply`.
