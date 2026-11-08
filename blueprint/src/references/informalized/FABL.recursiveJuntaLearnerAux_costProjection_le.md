<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.recursiveJuntaLearnerAux_costProjection_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Learner Cost Bound

**Claim.** If every supported node-finder outcome has projected cost at most $B$, then every supported recursive-learner outcome at fuel $r$ has projected cost at most $T(r)B$, where $T(0)=1$ and $T(r+1)=1+2T(r)$.

**Proof.** Induct on the recursion fuel, uniformly over the fixed-coordinate set and assignment. At fuel zero, the learner maps a node-finder outcome to its output tree without changing its cost. The support description for mapped runs therefore reduces the claim to the assumed node-finder bound (\texttt{FABL.LearningProgram.runWithCost_map}). At successor fuel, the support description for a bind first supplies a supported node-finder outcome and then a supported continuation; mapped outputs likewise preserve their costs (\texttt{FABL.LearningProgram.runWithCost_bind} and \texttt{FABL.LearningProgram.runWithCost_map}). The node outcome contributes at most $B$. If the node returns no decision or a constant decision, the continuation is pure and has zero cost, whose projection is zero by the hypothesis on the projection. If it returns a relevant coordinate, the recursive procedure runs two children, one for each assignment of that coordinate. Each child is a supported outcome at the smaller fuel, so the induction hypothesis bounds each projected cost by $T(r)B$. Additivity of the projection bounds their combined cost by $2T(r)B$. Adding the node cost gives $(1+2T(r))B=T(r+1)B$, by the recursion for the call count (\texttt{FABL.juntaTreeCallCount_succ}).

**Key facts.** `FABL.LearningProgram.runWithCost_map`, `FABL.LearningProgram.runWithCost_bind`, `FABL.juntaTreeCallCount_succ`.
