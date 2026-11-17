<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_from_blocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time Bounds from Related Computation Blocks

**Claim.** Under the stated initial-relation, bounded-block, simultaneous-halting, and equal-output hypotheses, the decoded machine and the universal machine have the asserted time-bounded simulation and converse output-computation properties.

**Proof.** Fix a code string $\alpha$ and take the linear-time constant to be $C=S(\alpha)+B(\alpha)$. The block-run lemma, applied with the relation for this $\alpha$ and each input $x$, gives at every source time $t$ a related universal-machine configuration at some time $v$ with $t\le v\le S(\alpha)+B(\alpha)t$ (`universal_block_run`).

If the decoded machine computes output $w$ at time $t$, its configuration then is halting and has output $w$. The related configuration at time $v$ is also halting by simultaneous halting, and has the same output by output preservation. Thus the universal machine computes $w$ at time $v$. Since $v\le S+Bt\le (S+B)(t+1)=C(t+1)$, monotonicity of computation time extends this to the claimed bound (`ComputesInTime.mono`). The equivalence between the computation predicate and the run's halting state and output supplies the conversion in both directions (`computesInTime_iff`).

Conversely, suppose the universal machine computes $w$ at some time $t$. Apply the block-run lemma at this target time to obtain a related source configuration at time $v$ with $v\le t$. The universal machine is still halted at time $v$: once a machine is in its halting state, its step leaves the configuration fixed. Monotonicity therefore transfers the given computation back to time $v$. The related source configuration is halting by simultaneous halting and has the same output, so the source machine computes $w$ at time $v$, again using the computation characterization.

**Key facts.** `Turing.universal_block_run`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
