<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRed_move -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One silent transition on a canonical frame

**Claim.** If the machine's transition in state $q$, on the indicated input and work-tape symbols, is silent, writes nothing, enters state $q'$, and has the specified head movements, then one step sends the canonical frame at position $i$ to the canonical frame at position $i'$. The counter length and tape contents and the output are unchanged.

**Proof.** Unfold the machine's one-step evolution in the given state. The canonical frame reads input symbol $x[i]$; its work-tape symbols are exactly the counter symbol at $a$ and the buffer symbol at $b$. Thus the assumed transition rule applies. Since it writes nothing and emits nothing, both tape-content functions and the output are preserved. Its input movement gives position $i'$ by the assumed clamped-move equality, and the two work-head movements give $a'$ and $b'$ by the stated arithmetic equalities. The general action-on-frame fact (\texttt{Complexity.satRedAction\_apply}) assembles these componentwise facts into the asserted next configuration.

**Key facts.** `Complexity.satRedCfg_input`, `Complexity.satRedAction_apply`.
