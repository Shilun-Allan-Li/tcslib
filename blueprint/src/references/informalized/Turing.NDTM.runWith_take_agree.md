<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.runWith_take_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement on Truncated Inputs

**Claim.** If two configurations on $x$ and on its first-$m$-symbol prefix initially agree in all five components, and the original input-head position plus the choice-word length is at most $m+1$, then their runs under that word agree in all five components.

**Proof.** Induct on the choice word, generalizing over the starting configurations. The empty word returns each starting configuration, so the assumed componentwise equalities give the result. For a word beginning with a bit, the length bound implies that the original input-head position is at most $m$. The one-step agreement theorem (`Turing.NDTM.stepWith_take_agree`) applies: the two configurations initially agree, and the head is within the portion of the input shared by $x$ and its truncation. It gives equality of all five components after this step, along with the bound needed for the remaining word. Unfold both runs by one step (`Turing.NDTM.runWith_cons`) and apply the induction hypothesis to these successor configurations. The original length inequality, after accounting for the first bit, supplies the induction hypothesis's length condition.

**Key facts.** `Turing.NDTM.stepWith_take_agree`, `Turing.NDTM.runWith_cons`.
