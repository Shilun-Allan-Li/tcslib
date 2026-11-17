<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.MultiTapeTM.step_output_prepend -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Preservation Under a Step

**Claim.** Prepending a finite string to a configuration’s output before one step has the same effect as prepending it to the output after the step.

**Proof.** The state, input-head position, work tapes, and work-head positions of the prefixed configuration are unchanged. Thus its input and work-head symbols are the same as those of the original configuration, so in a nonhalting state the machine uses the same transition action. That action appends its output to the configuration’s existing output; associativity of list concatenation gives $(p\mathbin{++}c.output)\mathbin{++}a.output=p\mathbin{++}(c.output\mathbin{++}a.output)$. All other configuration fields therefore agree. In the halting state, a step leaves the configuration unchanged, and the claimed equality follows directly as well.
