<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_hit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting from the Hit State

**Claim.** From the hit state, the machine halts with answer true in true mode, and otherwise with the bit of $h$ at the position stored in register $0$, defaulting to false; throughout, safety and the register bound hold.

**Proof.** Split on the mode. In false mode, one machine step from the hit state calls the bit oracle on the correctly formatted pairing of $h$ with the binary word for register $0$. The virtual-word formatting fact identifies this query as that pairing (`Complexity.LogProg.vword_whole₁`), and the bit oracle returns exactly the requested defaulted bit (`Complexity.drop_bit`). Depending on whether that bit is true or false, the machine proceeds to the corresponding answer state; the answer-state halting result supplies termination and the required safety and register bound (`Complexity.drop_ret`). The initial configuration satisfies the safety condition by `Complexity.drop_preS`, and one-step extension of a halting run preserves the result while accounting for this initial configuration (`Complexity.LogProg.AHalt.step`). In true mode the hit state itself is a return of true, so the return-state halting result applies directly (`Complexity.LogProg.AHalt.ret`), with safety again given by `Complexity.drop_preS`.

**Key facts.** `Complexity.drop_preS`, `Complexity.LogProg.vword_whole₁`, `Complexity.drop_bit`, `Complexity.drop_ret`, `Complexity.LogProg.AHalt.step`, `Complexity.LogProg.AHalt.ret`.
