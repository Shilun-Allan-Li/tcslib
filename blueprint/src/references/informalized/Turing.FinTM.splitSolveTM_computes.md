<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitSolveTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Split Solver Computation

**Claim.** For every $C,e\in\mathbb N$, the split solver halts on each Boolean word $w$ after exactly $20\bigl((C+1+5e)2^e+46\bigr)(|w|+1)^{e+2}$ steps and produces the specified encoding for the least valid split, or the empty word when no valid split exists.

**Proof.** First, `split_sources` supplies a source machine $M$, a starting state, and a round-time bound: on a candidate of length $\ell$, the source produces $C(\ell+1)^e$ tally bits within the stated polynomial bound. The round analysis `split_hyps` turns this into a split-body computation: it initializes at the anchor, tests successive candidates, and either accepts the first candidate satisfying the length equation or advances to the next one, with each round and initialization bounded by $((C+1+5e)2^e+45)(|w|+1)^{e+1}$. The length-counter machine supplies the fuel required by the loop construction (`split_fuel`). Applying the loop-finding theorem (`loopHostTM_finds`) therefore gives a computation with the desired output, with time bounded by $10\bigl(((C+1+5e)2^e+45)(|w|+1)^{e+1}+1\bigr)(|w|+2)$. The output is identified with the specified least split by `splitLoop_result`. Finally, `splitLoop_bound` and elementary arithmetic show this time is at most the claimed polynomial bound; monotonicity of computation time (`ComputesInTime.mono`) lets us state the result at that bound.

**Key facts.** `Turing.FinTM.split_sources`, `Turing.FinTM.split_hyps`, `Turing.FinTM.split_fuel`, `Turing.FinTM.loopHostTM_finds`, `Turing.FinTM.splitLoop_result`, `Turing.FinTM.splitLoop_bound`, `Turing.FinTM.ComputesInTime.mono`.
