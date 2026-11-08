<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.b3a_overwrite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overwriting the First Buffer Symbol

**Claim.** The specified one-tape machine, started in its writing phase with $w$ on its work tape, reaches after exactly four steps the done configuration with work-tape content $\mathrm{true}::\mathrm{tail}(w)$. Its state is not done at any earlier time $u<4$, and its total space use through step four is at most $2$.

**Proof.** The general behavior of the constant-word writer (`writeConstTM_run_ofCfg`) says that writing a word of length one and returning its head to the origin takes $2\cdot1+2=4$ steps, reaches the done state, and does not reach that state earlier. Its tape update replaces the cell at the initial head position with the one-symbol word $[\mathrm{true}]$. Here that position is zero, so the resulting buffer agrees at every integer cell with $\mathrm{true}::\mathrm{tail}(w)$, by the buffer-overwrite identity (`b3a_buffer_overwrite`). Finally, the writer visits at most the two positions from $0$ through $1$; the one tape therefore accounts for at most two visited cells.

**Key facts.** `Turing.writeConstTM_run_ofCfg`, `Complexity.b3a_buffer_overwrite`.
