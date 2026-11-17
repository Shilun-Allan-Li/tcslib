<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/StepDecider.lean :: Complexity.Codec.step_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step-program simulation

**Claim.** Under the stated register bounds and encoding hypotheses, the step-mode register program halts without exceeding its register bound and returns the step predicate evaluated on the given input, accumulator, head positions, and the indicated prefixes of the two work tapes.

**Proof.** Put $B=(8W+8)(|y|+1)$. The bound hypothesis gives a bound by $B$ for every register, and the encoding lengths and the hypothesis on $s$ provide the room needed for the program's scans. If the virtual accumulator is not accepting, the step predicate is false; the program's first branch rejects immediately, so its answer is correct. Otherwise, the program enters the simulation branch. The zero-reading routine, using the prescribed input-symbol code in register $Z$, reaches the position-comparison routine with the symbol under the input head correctly represented (`z_run`).

The position-comparison routine is run twice, once for each nondeterministic choice. Each run computes whether the machine's resulting input-head position equals the target position, using the transition's head movement and the input-end convention (`pm_run`). These two truth values are retained as $f_0$ and $f_1$.

Next the program scans the two tape prefixes of length $W(2s+1)$ in paired chunks. The equal-length prefixes and the register offsets ensure that the bits read from the encoded input are exactly the corresponding bits of each prefix; the encoding-position facts are supplied by `getD_w` and `getD_w2`. The scan simulation (`s_run`) shows that the program reaches its final scan state with both simulated accumulators equal to folding the paired symbols through the update rule, and that the updated registers remain within $B$. The arithmetic bounds needed here follow from the supplied register bound and `bnd_ge`; the explicit hypotheses on $Q3$, $Q4$, and $E$ give the required initial offsets and scan capacity.

The resulting final-state computation returns the disjunction of the two cases: for each choice, its head-position comparison flag conjoined with the corresponding simulated step-success flag. This is precisely `stepAns`, since its accumulator-acceptance factor is true in this branch. Chaining the initial transition, zero-read run, both position runs, and scan run gives a bounded guarded reach to the appropriate return instruction. The return principle (`AHalt.ret`) supplies halting with that Boolean answer, while composition of the reaches (`Reach.trans`) and the register-bound facts preserve the guard throughout.

**Key facts.** `Complexity.Codec.Regs.Bd.val_le`, `Complexity.Codec.bnd_ge`, `Complexity.Codec.gd_of`, `Complexity.Codec.z_run`, `Complexity.Codec.pm_run`, `Complexity.Codec.s_run`, `Complexity.Codec.Reach.cast`, `Complexity.Codec.Reach.trans`, `Complexity.LogProg.AHalt.ret`, `Complexity.Codec.AReach.halt`, `Turing.length_pairEncode`, `Complexity.Codec.getD_w`, `Complexity.Codec.getD_w2`, `Complexity.Codec.Regs.val_Q3`, `Complexity.Codec.Regs.val_Q4`.
