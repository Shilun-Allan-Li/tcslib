<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_eq_parse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing the Doubled Prefix

**Claim.** If $y=pre\,\langle u,v\rangle$, then the comparator starting in parser state at position $|pre|+1$, with work word $a$ and head at $|a|$, reaches rewind state after $2|u|+2$ steps, at position $|pre|+2|u|+3$, with work word $au$ and head at $|au|-1$.

**Proof.** Proceed by induction on $u$. If $u$ is empty, the encoded pair begins with the separator $01$, and the separator transition takes the comparator from parser to rewind state with the specified position and head placement (`a3n_eq_separator`). For the inductive step, write $u=b::u'$. The encoding begins with the doubled bit $bb$, followed by the encoding of $(u',v)$. The two-step doubled-bit transition reads $bb$, appends $b$ to the work word, and returns to parser state (`a3n_eq_double`). Apply the induction hypothesis to the remaining encoding, with prefix extended by $bb$ and work word extended by $b$. The run-addition law concatenates these two phases, giving the stated total number of steps and final configuration (`runFrom_add`). The positions and work-head coordinate then simplify to the claimed expressions.

**Key facts.** `Complexity.a3n_eq_separator`, `Complexity.a3n_eq_double`, `Turing.MultiTapeTM.runFrom_add`.
