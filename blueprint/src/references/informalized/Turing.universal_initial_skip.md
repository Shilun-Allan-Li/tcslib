<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_initial_skip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial State Skip Duration

**Claim.** When the table has the form $l1^n0r$, the interpreter starting in the initial-state skipper at cursor $|l|$ reaches the record-group phase after $n+1$ steps, with cursor $|l|+n+1$ and the other configuration data unchanged.

**Proof.** Induct on $n$, allowing the prefix $l$ to vary. If $n=0$, the table symbol at cursor $|l|$ is the delimiter $0$ (Turing.universal_table_read). The interpreter therefore changes from the initial-skip phase to the record-group phase and advances the table head once; the zero-step and one-step run identities identify this with the claimed run of length one. For the induction step, the current symbol is $1$, so one interpreter step stays in the initial-skip phase and advances the cursor. Rewrite the table as $(l\,1)1^n0r$ and apply the induction hypothesis to this extended prefix. The resulting total duration and cursor are respectively $(n+1)+1$ and $|l|+1+n+1$, as required; other configuration data remain fixed throughout these transitions.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.universal_table_read`, `Turing.universalEval_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
