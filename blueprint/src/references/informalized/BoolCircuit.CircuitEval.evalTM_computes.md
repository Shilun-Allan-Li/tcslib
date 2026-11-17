<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.evalTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic running time of the evaluator

**Claim.** For every Boolean input $z$ and either mode, the evaluator halts after exactly $12(|z|+1)^2$ steps, outputs the one-bit verdict, and uses some finite amount of work-tape space.

**Proof.** First establish a halting run with the required output at some time no greater than the stated bound. Split on pair decoding. If decoding fails, the malformed-encoding characterization writes $z=\mathrm{dbl}(w)\mathbin{++}t$ with one of the three specified tails (`Turing.pairDecode_eq_none`). The bounded rejection result gives a halting run outputting $0$ (`BoolCircuit.CircuitEval.bad_run`), which is the verdict in this case. Its time is bounded by $12(|z|+1)^2$ using $|w|\le |z|$. If decoding succeeds with pair $(\mathrm{code},x)$, recover the encoded word from its decoded pair (`Turing.eq_pairEncode_of_pairDecode`) and rewrite the pair encoding as $\mathrm{dbl}(\mathrm{code})\mathbin{++}[0,1]\mathbin{++}x$ (`Turing.pairEncode_eq_dbl`). The good-encoding run theorem then supplies a halting run with output the verdict within the same quadratic bound (`good_run`).

Let $t$ be the time of the resulting run. Extend it to the exact target time by decomposing the run into $t$ steps followed by the remaining steps (`Turing.MultiTapeTM.runFrom_add`). Once the machine is halted, further steps leave its configuration unchanged (`Turing.MultiTapeTM.runFrom_of_halt`). Thus at the exact target time it is still halted with the same output. The equivalence between a computation-time claim and halting with the specified output at that time gives the desired computation, including its space witness (`Turing.FinTM.computesInTime_iff`).

**Key facts.** `Turing.pairDecode_eq_none`, `BoolCircuit.CircuitEval.bad_run`, `Turing.eq_pairEncode_of_pairDecode`, `Turing.pairEncode_eq_dbl`, `BoolCircuit.CircuitEval.good_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.FinTM.computesInTime_iff`.
