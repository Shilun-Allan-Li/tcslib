<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_inner_prepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner Preparation Run

**Claim.** Under the stated bounds and register conditions, the machine reaches the length-bound state, with register $8$ set to $n+1$ and register $7$ set to $C(n+1)^e$, leaving all other registers unchanged and maintaining the prescribed invariant.

**Proof.** Set $B=8(2C+3)(|h|+1)^{e+1}$. The machine first clears register $8$, then copies the value in register $4$ into it. Since register $4$ equals $4n+4$ and $n\le|h|$, the copy is within the bound; `Complexity.LogProg.register_update_le` verifies the resulting register bounds. Two successive halvings of register $8$ change $4n+4$ to $2n+2$ and then to $n+1$.

From the resulting configuration, the polynomial-run lemma (`Complexity.comp_poly_run`) with the inner flag false computes the remaining register value as $C(n+1)^e$ and reaches the length-bound state. Its required power and product bounds follow from the power-bound lemma (`Complexity.comp_power_bound`), using $n+1\le |h|+1$. The hypotheses that registers $6,7,10,11$ are zero remain available because the preceding changes affected only register $8$, and the other conditions required by the polynomial run follow from the new value $n+1$ of register $8$. The reachability step and concatenation principles (`Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.trans`) join the clearing, copying, halvings, and polynomial run. The prescribed instruction invariant is supplied throughout by `Complexity.comp_preS`.

**Key facts.** `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.register_update_le`, `Complexity.comp_copy_run`, `Complexity.comp_poly_run`, `Complexity.comp_power_bound`, `Complexity.comp_preS`.
