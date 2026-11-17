<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalCapture_interpreter_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interpreter run in the capture wrapper

**Claim.** For any $t$, the capture wrapper started from the right-block embedding of an interpreter configuration runs for $t$ steps to the right-block embedding of the interpreter’s $t$-step run, while retaining the assigned left-block tape contents and head positions.

**Proof.** The wrapper’s transition on a state embedded from the interpreter is exactly the interpreter’s transition, placed in the right block and with its state embedded by the same map. This is the transition compatibility required by the right-block simulation lemma (\texttt{rightCfg\_run}). That lemma therefore applies for every number of steps: the interpreter’s state, input-head position, output, and right-block tapes evolve as in its own run, while the separately assigned left-block tapes and head positions remain fixed. The resulting equality is precisely the one asserted.

**Key facts.** `Turing.FinTM.rightCfg_run`.
