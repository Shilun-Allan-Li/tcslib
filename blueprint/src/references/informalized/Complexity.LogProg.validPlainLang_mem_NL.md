<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMExample.lean :: Complexity.LogProg.validPlainLang_mem_NL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Valid plain encodings are in NL

**Claim.** The language of valid plain encodings is recognized by a finite-state nondeterministic Turing machine that halts after a common input-dependent number of choices on every choice sequence, uses logarithmic space, and accepts exactly the valid encodings.

**Proof.** Apply the general nondeterministic register-machine simulation theorem (`narm_decides`) to the fixed machine `guessValidA`, with no oracle languages and space constant $K=1$. Its finite set of four states satisfies the required pre-state condition: each state with zero register counters and either output-residue value meets the machine's precondition, as checked directly from its definition. The machine's halting bound is supplied by `guessValidA_halts`, and its acceptance condition is exactly validity by `guessValidA_ans`.

For the space bound, the only counter is initially zero, so the encoded counter has value $0+1=1$. Its binary representation has length at most $1$ by `length_bits_le`. Also $\mathrm{logSpace}(|x|)=\lfloor\log_2 |x|\rfloor+1$ is at least $1$, including for empty input. Thus the counter uses at most $1\cdot\mathrm{logSpace}(|x|)$ space, as required by the simulation theorem. The resulting NL machine has the asserted halting, space, and exact-recognition properties.

**Key facts.** `Complexity.LogProg.narm_decides`, `Complexity.LogProg.guessValidA_halts`, `Complexity.LogProg.length_bits_le`, `Complexity.LogProg.guessValidA_ans`.
