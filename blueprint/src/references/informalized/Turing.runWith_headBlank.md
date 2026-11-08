<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.runWith_headBlank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head and blank-region bounds during a run

**Claim.** If initially every work-tape head lies within distance $n$ of the origin and every cell at distance at least $n$ is blank, then after following the choices in $w$, every head lies within distance $n+|w|$ and every cell at distance at least $n+|w|$ is blank.

**Proof.** Induct on the choice word. For the empty word, the run leaves the configuration unchanged, so the assumed head and blank-cell bounds give the result. For a word $b::w$, first apply the one-step radius bound (`Turing.OracleTM.step_radius`) to the configuration after choice $b$. It enlarges the radius from $n$ to $n+1$, controlling both head positions and blank cells. The choice-dependent step is the corresponding fixed-choice oracle-machine step (`Turing.OracleNDTM.stepWith_eq_fixChoice_step`), so the same bounds hold for the actual run. Apply the induction hypothesis to the remaining choices $w$ with radius $n+1$. The resulting radius is $(n+1)+|w|=n+|b::w|$, as required; the run recursion and the empty-word identity are given by `Turing.OracleNDTM.runWith_cons` and `Turing.OracleNDTM.runWith_nil`.

**Key facts.** `Turing.OracleNDTM.runWith_nil`, `Turing.OracleNDTM.runWith_cons`, `Turing.OracleNDTM.stepWith_eq_fixChoice_step`, `Turing.OracleTM.step_radius`.
