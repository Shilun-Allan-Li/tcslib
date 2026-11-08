<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPoly_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup of the Generator

**Claim.** After $2(|x|+1)$ steps from the initial configuration on $x$, the machine is in the outermost loop state, with each work tape holding $|x|+1$ unary marks, every head at zero, and empty output.

**Proof.** First, the copy-phase result puts the machine after $|x|$ steps in copy state with $|x|$ marks on each tape and the input head at the end of the word. The next transition sees no input symbol. It adds one final unary mark to each tape, moves every head left, and enters setup. The tape update is the one-step extension of the unary tape (`catalogPolyTape_write`); the input head remains at the boundary (`moveInputPos_zero`). Thus after $|x|+1$ steps the setup configuration has every head at $|x|-1$. Run decomposition combines the copy run and this final transition (`runFrom_succ_eq_step'`). Applying the setup-rewind result with $q=|x|+1$ and $j=|x|$ takes another $|x|+1$ steps, returns every head to zero, and enters the outermost loop state. Combining the two equal-length runs gives the claimed total (`runFrom_add`).

**Key facts.** `Turing.FinTM.catalogPolyTape_write`, `Turing.FinTM.catalogPoly_copy`, `Turing.FinTM.catalogPoly_setup`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`.
