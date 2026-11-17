<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_center_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return to the Guide Origin

**Claim.** Starting in the return-center phase at guide position $-R$, after $R+1$ steps the simulator is in macrostep-check at guide position $0$ and unary position $u+1$. Its state register is the successor state selected by the source action; the answer, saved reads, neighbor registers, data tapes, and output are unchanged.

**Proof.** First prove by induction that for every $n\le R$, the run of $n$ steps remains in the return-center phase, with guide head at $-R+n$, unary head at $u$, and all data registers, tapes, and output unchanged. The zero-step case follows from the identity run (`runFrom_zero`). For the induction step, the guide position is not $0$ when $n<R$. The return-center schedule transition therefore continues the return sweep and advances the guide head by one (`macroCfg_center`). The guide tape identifies the symbol at the current guide position (`macroCfg_guide`), and the visitor preserves the data and output during this non-origin step. The one-step formula for the decorated machine (`dataCfg_step`) then gives the claimed configuration for $n+1$.

Now take $n=R$, so the guide head is at $0$. One more step uses the origin branch of the return-center transition: it enters macrostep-check, advances the unary head to $u+1$, and leaves the guide head at $0$ (`macroCfg_center`). The guide origin is precisely the symbol read at position $0$ (`guideTape_origin`), and at this position the visitor updates the state register to the state selected by the source action while preserving the answer, saved reads, neighbor registers, data tapes, and output. Applying `dataCfg_step` yields the stated endpoint.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Complexity.dataCfg_step`, `Complexity.macroCfg_center`, `Complexity.macroCfg_guide`, `Complexity.guideTape_origin`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
