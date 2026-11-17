<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPoly_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Copying Phase

**Claim.** For each $i\le |x|$, after $i$ steps from the initial configuration the machine is in its copy phase, with $i$ unary marks on every work tape and the input head advanced past $i$ symbols.

**Proof.** Proceed by induction on $i$. At $i=0$, the initial configuration has the copy control state, input head at its initial position, blank work tapes, heads at zero, and empty output; this is precisely the asserted copy configuration with zero marks. For the successor step, the induction hypothesis identifies the configuration after $i$ steps. Because $i<|x|$, the input symbol there is the $i$th symbol of $x$ (`inputSymbolInner`). The copy transition writes a true symbol at the current position on every work tape, moves each head right, advances the input head, and remains in the copy state. The tape update adds the next unary mark (`catalogPolyTape_write`), and the input movement is one position to the right (`moveInputPos_pos_of_ne_right`). Thus the resulting configuration is the claimed one after $i+1$ steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.FinTM.catalogPolyTape_write`, `Turing.moveInputPos_pos_of_ne_right`.
