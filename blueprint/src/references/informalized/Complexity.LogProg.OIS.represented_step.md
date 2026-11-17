<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.represented_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Simulated Machine Step

**Claim.** Under the stated oracle conditions, a live machine configuration and its representation in the compiled program are related by a finite simulation of one machine step; the resulting representation corresponds to the next original configuration, and all strictly earlier compiled configurations satisfy safety.

**Proof.** 1. Unpack the representation: there is an index $i\le |v|$ such that the compiled configuration is the encoding of $c$ at index $i$, with phase determined by whether the original input head is at the left boundary. Since $c$ is live, write its state as $s$. The index relation in the representation and the input-symbol characterization (`inputSymbol_eq`) identify the symbol under the original input head as blank at the left boundary and otherwise as the symbol of $v$ at index $i$.

2. First supply this input symbol to the compiled machine. At the left boundary, the representation is already in the appropriate work phase, so zero steps suffice. Otherwise, the input symbol is obtained through the two oracle calls: `ask_step` queries whether $i<|v|$, and when that holds `bit_step` retrieves the $i$th bit. The oracle hypotheses give the prescribed answers, and the list-index relation identifies that bit with the symbol under the original head. If $i$ is not below $|v|$, the length query instead yields the blank symbol. Thus in either case the compiled machine reaches the work phase carrying $c$'s input symbol. The intermediate query configurations are safe by `imageCfg_safe`.

3. Execute one original transition. The work-phase transition simulates the transition of $M$ on $c$ and preserves the encoded index; this is `work_step`. If the resulting machine state is halting, that configuration already represents the next machine configuration, and the stated head bound follows directly from the hypothesis on the next configuration. Otherwise, its input-head movement may require adjusting the stored index. The relation between the new input symbol and the boundary flags identifies the right-boundary flag. Apply `adjust_index` to move the encoded index to the new input-head position and set the correct next phase. This yields a finite run to a representation of the next configuration; every intermediate state in this adjustment is safe.

4. Concatenate the input-supply run and the work-and-adjustment run using the run-addition law `rrun_add`. The endpoint representations match, and any time strictly before the combined endpoint belongs to one of the two component runs, where safety has already been established. The zero-length boundary case and run origin are interpreted using `rrun_zero`.

**Key facts.** `Complexity.LogProg.OIS.ask_step`, `Complexity.LogProg.OIS.bit_step`, `Complexity.LogProg.OIS.imageCfg_safe`, `Complexity.LogProg.OIS.work_step`, `Complexity.LogProg.inputSymbol_eq`, `Complexity.LogProg.OIS.adjust_index`, `Complexity.LogProg.rrun_add`, `Complexity.LogProg.rrun_zero`.
