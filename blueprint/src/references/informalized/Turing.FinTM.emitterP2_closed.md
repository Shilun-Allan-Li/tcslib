<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_closed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Construction of the Width-Parametric Splitter

**Claim.** A finite Boolean-alphabet machine computes the specified split encoding, within a constant multiple of $(|w|+1)(T_E(|w|+1)+|w|+2)$ steps.

**Proof.** Choose a machine that computes the binary length of its input in linear time (`Turing.FinTM.computesFunInTime_lengthBits`). Install call routines for the given machine $E$ and for this length machine, using the bounded-call construction (`Turing.FinTM.exists_installCallTM`). The resulting body first prepares the computation, then in each round calls $E$ on the candidate prefix and the length machine on the remaining suffix; the body-round theorem (`Turing.FinTM.emitterP2_body_round`) supplies the round's endpoint, its first-return behavior, and the acceptance or rejection outcome. The body starts in the required anchor configuration by the initialization lemma (`Turing.FinTM.emitterP2_body_start`).

Apply the body-to-splitter theorem (`Turing.FinTM.emitterSplit_of_body`) with a constant chosen to dominate the round and initialization costs. For each input, the initialization witness is time zero. For any candidate prefix $s$ with $|s|\le |w|+1$, the width-budget lemma (`Turing.FinTM.emitter_width_budget`) bounds both the time for $E$ and the length of its binary output by quantities controlled by $T_E(|w|+1)$. The suffix length is at most $|w|$, and the length routine's output on that suffix has length at most $d(|w\mathbin{\mathrm{drop}}|s||+1)$: this follows from its promised output and the general bound that a machine's output length after $t$ steps is at most $t$ (`Turing.MultiTapeTM.output_length_le`). The call bounds from the two installed routines therefore give costs at most $2c_C H$ and $c_D(2d+1)H$, respectively, where $H=T_E(|w|+1)+|w|+2$. The remaining round overhead is at most $10(d+8)H$. Adding these bounds yields the claimed constant multiple, with constant $A=2c_C+c_D(2d+1)+10(d+8)$.

**Key facts.** `Turing.FinTM.computesFunInTime_lengthBits`, `Turing.FinTM.exists_installCallTM`, `Turing.FinTM.emitterP2_body_start`, `Turing.FinTM.emitterSplit_of_body`, `Turing.FinTM.emitter_width_budget`, `Turing.FinTM.emitterP2_body_round`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`.
