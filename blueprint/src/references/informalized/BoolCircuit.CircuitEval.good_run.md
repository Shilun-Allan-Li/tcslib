<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.good_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded halting run

**Claim.** For either Boolean mode and words satisfying the specified encoding of $z$, the evaluator machine halts within $12(|z|+1)^2$ steps and outputs the singleton word containing its verdict on $z$.

**Proof.** First use the encoding of $z$ to compute $|z|=2|code|+2+|x|$, identify the delimiter positions, and rewrite the verdict as the stated condition on $code$, $x$, and the abstract run. The initialization lemma (`init_eq`) identifies the machine's starting configuration with its scan configuration. The scan simulation (`setup_scan`) processes the doubled code, and the scan recurrence (`scanF_n0`) determines whether the code contains a zero. Split accordingly.

If the code contains no zero, the verdict condition fails. The scan reaches the delimiter in phase $n0$; the two-step transition calculation (`lstep`) then rejects, outputting false. The total time is $2|code|+2$, which satisfies the claimed quadratic bound.

If the code contains a zero, the scan enters the separator phase with the count $n$ of leading ones. The separator transition, given by `lstep`, begins the mark-tape rewind. The rewind fact (`rew`) positions the machine for copying the first $n$ symbols of $x$, and the copy simulation (`copy_run`) tracks this process. If $n>|x|$, copying runs out of input and the machine rejects; the verdict condition also fails, and this run fits the quadratic bound.

It remains to consider $n\le |x|$. After copying those $n$ symbols, if exact mode is on and $n<|x|$, the machine rejects at the next input position; in this case the verdict condition again fails. Otherwise, the machine rewinds its value tape using `rew`, then returns the input head to the start of the remaining computation. The timed input rewind lemma (`Turing.FinTM.timed_rewind`) bounds this return. The main simulation theorem (`main_run`), applied to the abstract state with phase $skipN$ and values $x.take(n)$, then gives a halting run outputting the abstract evaluation. The encoding identity `pairDecode_pairEncode` and the relation `pairEncode_eq_dbl` justify the verdict's decoding, and the leading-ones bound ensures its condition holds in this remaining case. Combining the scan, copy, rewind, and main-run time bounds, and using $|z|=2|code|+2+|x|$, yields a total at most $12(|z|+1)^2$ steps. The run decomposition law `Turing.MultiTapeTM.runFrom_add` concatenates these consecutive phases, while the one-step and zero-step run identities identify the final configuration.

**Key facts.** `BoolCircuit.CircuitEval.init_eq`, `BoolCircuit.CircuitEval.setup_scan`, `BoolCircuit.CircuitEval.scanF_n0`, `BoolCircuit.CircuitEval.lstep`, `BoolCircuit.CircuitEval.rew`, `BoolCircuit.CircuitEval.copy_run`, `Turing.FinTM.timed_rewind`, `BoolCircuit.CircuitEval.main_run`, `Turing.pairEncode_eq_dbl`, `Turing.pairDecode_pairEncode`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
