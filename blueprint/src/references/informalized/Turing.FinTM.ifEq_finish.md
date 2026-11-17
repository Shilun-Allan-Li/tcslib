<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.ifEq_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emission Phase Completion

**Claim.** If the comparator machine for $w_0,u,v$ is in the initial emission state for the selected word $z$ and its output is empty, then after $|z|+1$ steps it is halted and its output is $z$.

**Proof.** Split on $b$. If $b$ is false, the selected word is $v$ and the state is the initial state of the emission chain for $v$; if $b$ is true, these are respectively $u$ and its emission chain. In either case, the transition function on that chain agrees with the emission action at every position. The emission-halting result (`emit_halts`) therefore says that after one step per symbol, followed by the final halting step, the machine halts and appends the selected word to its existing output. Since that output is empty, the resulting output is exactly the selected word.

**Key facts.** `Turing.FinTM.emit_halts`.
