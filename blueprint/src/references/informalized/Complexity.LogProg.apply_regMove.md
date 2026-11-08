<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean :: Complexity.LogProg.apply_regMove -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moving a Register Head

**Claim.** The specified action leaves the input position, tapes, decider-head positions, and output unchanged, enters state $st'$, and advances register head $r$ by $mv$.

**Proof.** Apply the general register-movement formula (`Complexity.LogProg.apply_moves`) with zero input movement and with each register movement equal to $mv$ at $r$ and zero elsewhere. The input position is unchanged because a zero movement fixes it (`Turing.moveInputPos_zero`). The resulting head-position function is therefore the old one with position $r$ replaced by $rp(r)+mv$, which is precisely the stated update. The general formula also leaves tapes, decider heads, and output unchanged.

**Key facts.** `Complexity.LogProg.apply_moves`, `Turing.moveInputPos_zero`.
