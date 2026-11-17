<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_state_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marker-Directed State Rewind

**Claim.** Under the stated marker and transition hypotheses, starting with the state head at any natural position $j$ takes $j+1$ steps to reach control $q'$ with the state head at $1$.

**Proof.** Induct on $j$. At $j=0$, the state tape contains the marker $0$ at position zero, so the stopping transition hypothesis applies. The one-step evaluation result (`Turing.timedCut_Eval_step`), together with the zero-step and successor run laws (`Turing.MultiTapeTM.runFrom_zero` and `Turing.MultiTapeTM.runFrom_succ_eq_step`), shows that one step enters $q'$ and moves the head right to position $1$. For the successor case, the head begins at $j+1>0$. By the non-marker hypothesis, the symbol there is not the stopping marker, so the scanning transition applies: it keeps control $q$ and moves the head one cell left. The evaluation result describes this step and places the head at $j$. The induction hypothesis then completes the rewind in $j+1$ more steps. Together with the first step, this is $(j+1)+1$ steps, with the asserted final control and head position.

**Key facts.** `Turing.timedCut_Eval_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
