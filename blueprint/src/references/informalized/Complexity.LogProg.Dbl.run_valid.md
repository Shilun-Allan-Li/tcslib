<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean :: Complexity.LogProg.Dbl.run_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of the doubled-word run

**Claim.** On the pair encoding of $n$ ones and a canonical word $w$, the doubled-input machine has a run from its initial configuration to input-head position $1$, work-tape head $0$, and state yes exactly when $w$ is the binary expansion of $2n$ (and no otherwise); before the endpoint its work-tape head stays between $-1$ and the length of that binary expansion.

**Proof.** Write $W$ for the length of the binary expansion of $2n$. The pair-encoding length formula (`length_eq`) ensures that the input positions used in the run are valid. The proof concatenates five phases, using the fact that run segments compose while preserving the stated work-head bound (`Rch.trans`).

1. The format-checking phase runs from the initial state to the counting state. The verified plain-input routine (`valPlain_run`) establishes this segment and bounds the head position by $-1$ and $W$. Its validity hypotheses are supplied by the input encoding and the assumption that the last bit of nonempty $w$ is true.
2. The counting phase advances across the $2n$ doubled unary symbols, ending in the counting state with the input head at position $1+2n$ and the work tape holding the binary expansion of $2n$. This is the content of `count`, applied at its maximal index $2n$.
3. At the next input position the separator is false: `sym_eq` identifies the symbol at position $2n$. Therefore the transition from the counting state enters the rewind phase. The one-step transition formula (`step_x`) gives the resulting configuration, and the zero-movement input-head fact (`moveInputPos_zero`) keeps its position fixed. At this one-step segment the head bound follows directly from the configuration.
4. The rewind routine (`rewind_x`) returns the input head to position $1$ and enters the comparison state. Throughout this segment the work-tape head remains at its starting position, so it satisfies the required bounds.
5. The plain comparison routine (`jeqPlain_run`) compares $w$ with the binary expansion of $2n$, returns to input-head position $1$ with the work-tape head at $0$, and selects yes precisely on equality, no otherwise. Its intermediate configurations satisfy the required bounds. Composing these five segments gives the claimed run and bound.

**Key facts.** `Complexity.LogProg.Dbl.length_eq`, `Complexity.LogProg.Dbl.Rch.trans`, `Complexity.LogProg.valPlain_run`, `Complexity.LogProg.Dbl.count`, `Complexity.LogProg.Dbl.sym_eq`, `Complexity.LogProg.Dbl.step_x`, `Turing.moveInputPos_zero`, `Complexity.LogProg.Dbl.rewind_x`, `Complexity.LogProg.Dbl.jeqPlain_run`.
