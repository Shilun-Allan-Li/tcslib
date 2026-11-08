<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.constTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant-word machine computes its output

**Claim.** For any Boolean words $w$ and $x$, the finite Turing machine that emits the symbols of $w$ in order computes $w$ from input $x$ within $|w|+1$ steps.

**Proof.** The emitting machine starts in the state corresponding to the first position of $w$. Its transition at each position emits that symbol and advances to the next position; after the final symbol, the next transition halts. The emission lemma (`emit_halts`) therefore shows that after $|w|+1$ steps the machine is halted and its output is the initial output followed by $w$. The initial output is empty, so the output is exactly $w$. Taking the actual space used by the run supplies the space witness required by timed computation.

**Key facts.** `Turing.FinTM.emit_halts`.
