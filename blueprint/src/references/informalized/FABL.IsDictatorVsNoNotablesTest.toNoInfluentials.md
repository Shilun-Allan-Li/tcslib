<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.IsDictatorVsNoNotablesTest.toNoInfluentials -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# From No Notables to No Influentials

**Claim.** A tester family satisfying the no-notables soundness condition also satisfies the no-influentials soundness condition, with the same allowed predicates, completeness bound, and error function.

**Proof.** Retain each hypothesis of the no-notables tester property for the corresponding field of the desired property. For soundness, fix a dimension, an admissible threshold $\varepsilon$, and a bounded function whose influences at parameter $1$ are at most $\varepsilon$. The fact that such a function has stable influences at parameter $1-\varepsilon$ also bounded by $\varepsilon$ (\texttt{HasSmallInfluences.hasSmallStableInfluences}) makes it eligible for the original no-notables soundness bound. Applying that bound gives the required acceptance estimate.

**Key facts.** `FABL.HasSmallInfluences.hasSmallStableInfluences`.
