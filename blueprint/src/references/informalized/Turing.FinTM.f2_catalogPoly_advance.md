<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPoly_advance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advance transition

**Claim.** From a configuration in state $\mathrm{advance}(i)$, one step leaves the input-head position, tape contents, and output unchanged, moves work-tape head $i$ one cell to the right, leaves all other work-head positions unchanged, and enters state $\mathrm{loop}(i)$.

**Proof.** Since $i<c+1$, the transition rule for $\mathrm{advance}$ takes its moving branch: it makes no input-head movement, writes nothing, emits nothing, moves head $i$ one cell to the right, and changes state to $\mathrm{loop}(i)$. The one-step update formula for a move on a selected work tape (`f2_catalogPolyMove_apply`) identifies the resulting head-position function as `Function.update h i (h i + 1)` and leaves the other configuration data fixed.

**Key facts.** `Turing.FinTM.f2_catalogPolyMove_apply`.
