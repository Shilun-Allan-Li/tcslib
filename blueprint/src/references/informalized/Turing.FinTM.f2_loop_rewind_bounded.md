<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loop_rewind_bounded -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Rewind to the Initial Position

**Claim.** Under the stated transition rules, a configuration in state $a$ can reach state $d$ at input-head position $1$ within at most its initial input-head position plus $2$ steps, leaving all other components unchanged.

**Proof.** First take the prescribed transition from state $a$. The control action changes only the state and input-head position, so the resulting configuration $c$ has state $b$, its input-head position is the previous position moved one place left, and all other components are unchanged (`Turing.FinTM.controlAction_apply`). The left-move formula gives this new position as the old position minus one (`Turing.FinTM.moveInputPos_neg_val`), and in particular it is at most the input length. Starting from $c$, the scan rule in state $b$ moves left across each present input symbol and, upon reaching the absent symbol to the left of the input, moves right and enters state $d$. The rewind lemma says this reaches position $1$ after $c$'s input-head position plus one steps (`Turing.FinTM.rewind_scan`). Concatenate the initial step with this scan using the run-addition law (`Turing.MultiTapeTM.runFrom_add`). The total is $1+(c	ext{'s position}+1)$, which is at most the original position plus $2$; the resulting configuration differs from the original only in state and input-head position, as required.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.FinTM.rewind_scan`, `Turing.MultiTapeTM.runFrom_add`.
