<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine.lean :: BoolCircuit.CircuitEval.lstep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-step machine transition

**Claim.** When two consecutive input symbols are available, the evaluator machine starting in the first read state advances over both symbols in two steps and reaches the configuration specified by the local action on their pair and the scanned work-tape symbols.

**Proof.** Separate the two machine steps. At the first position, the input-symbol lookup identifies the scanned symbol as $b$. The transition from the first read state stores it in the control state and moves the input head one position to the right. The configuration update rule (`step_cf`) therefore gives the intermediate state $\mathrm{rd2}(\phi,b)$, with work tapes and output unchanged. At the next position the input-symbol lookup gives $b'$. The second read-state transition uses the hypothesis that the pair symbol determined by $b,b'$ is $s$, and so applies exactly the local action for $\phi$ and $s$. Applying `step_cf` again updates the tapes, work heads, state, and output accordingly. The input head advances once more; the bound $i+2\le |z|$ ensures neither move runs into the right boundary, so the resulting position is the one encoded by $i+2$. Composing the two transitions gives the asserted run of length two.

**Key facts.** `BoolCircuit.CircuitEval.step_cf`, `Turing.FinTM.inputSymbol_at`, `Turing.moveInputPos_pos_of_ne_right`.
