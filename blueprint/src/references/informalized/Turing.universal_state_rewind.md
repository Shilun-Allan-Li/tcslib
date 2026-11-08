<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_state_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marker-Directed State Tape Rewind

**Claim.** Under the stated transition rules and marker conditions, starting at state cursor $j$ in control state $q$, after $j+1$ steps the control is $q'$, the cursor is $1$, and the table, tape, and other configuration data are unchanged.

**Proof.** Induct on $j$. At $j=0$, the cursor is at zero, where the tape contains the marker. Thus the stopping transition applies: it enters $q'$, moves the state cursor right once, and makes no other change. The one-step evaluation rule (`universalEval_step`), together with the zero-step run identity (`runFrom_zero`), gives the result. For the successor case, start at cursor $j+1$. This is a positive position, so the tape does not contain the zero marker there. The scan transition therefore stays in $q$ and moves the cursor left once, leaving everything else fixed. After that step the cursor is $j$; the induction hypothesis completes the rewind in $j+1$ further steps, ending in $q'$ at cursor $1$. The run decomposition into one step followed by the remaining run (`runFrom_succ_eq_step`) combines these stages.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.universalEval_step`.
