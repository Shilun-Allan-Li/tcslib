<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRed_maxFormula -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum scan of a formula

**Claim.** For a serialized CNF formula between a prefix and suffix, the machine reaches state $7$ at the stated final input position in at most twice the serialization length. Its counter length becomes the maximum of its initial length and the largest occurring variable index plus one, with value zero if no variable occurs; the counter head, second tape, second-tape head, and output are unchanged.

**Proof.** Induct on the formula. For the empty formula, its encoding is the single false delimiter. One transition from state $2$ reads that delimiter, keeps the input-head position fixed, and enters state $7$. The counter length remains $n$, and the one-step bound holds.

For a formula with first clause $C$ and tail formula $\varphi$, its encoding begins with a true clause marker, followed by the serialization of $C$, then the serialization of $\varphi$. The marker transition advances the input head and changes state $2$ to state $3$, leaving the work tapes and output unchanged. Next, the maximum-scan result for one clause (\texttt{Complexity.satRed\_maxClause}) scans $C$, reaching state $2$ just after it and updating the counter length to $\max(n,\mathrm{satClauseVars}(C))$. Apply the induction hypothesis to $\varphi$ from there. The resulting counter length is $\max(\max(n,\mathrm{satClauseVars}(C)),\mathrm{numVars}(\varphi))$, equal to the claimed maximum for the whole formula by the decomposition of the number of variables (\texttt{Complexity.sat\_numVars\_cons}). The input-position arithmetic places the head at the required position after the whole encoding. Concatenating the marker step and the two runs uses the run-addition law (\texttt{Turing.MultiTapeTM.runFrom\_add}); their step bounds sum to at most twice the total encoding length.

**Key facts.** `Complexity.satRed_move`, `Turing.moveInputPos_pos_of_ne_right`, `Complexity.satRed_maxClause`, `Complexity.sat_numVars_cons`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.satRed_one`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
