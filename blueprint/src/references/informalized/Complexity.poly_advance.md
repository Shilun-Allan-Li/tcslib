<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.poly_advance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advance to the Next Loop Level

**Claim.** From state $\mathrm{advance}_i$, one step reaches state $\mathrm{loop}_i$, preserving the tape contents and output while moving head $i$ one cell to the right.

**Proof.** In state $\mathrm{advance}_i$, the machine's transition condition holds because $i<c+1$. Its transition is therefore the movement that keeps the input head fixed, makes no tape writes, and moves only work head $i$ one step to the right, entering $\mathrm{loop}_i$. The configuration update changes the head-position function from $h$ to $\operatorname{update}(h,i,h(i)+1)$ and leaves the tape contents and output unchanged. The one-step configuration formula for this movement is precisely the fact that `polyMove_apply` supplies.

**Key facts.** `Complexity.polyMove_apply`.
