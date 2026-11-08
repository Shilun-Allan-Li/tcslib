<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.isRelevant_of_isRelevantJuntaRestriction_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relevance of the Unrestricted Function

**Claim.** If the empty-set restriction has two free assignments differing only at coordinate $i$ on which its values differ, then the original function has positive influence at coordinate $i$.

**Proof.** Take the two witnessing free assignments and combine each with the fixed assignment on the empty set to obtain ambient cube points $x_0,x_1$. Combining on the empty set preserves every free coordinate (\texttt{FABL.combineJuntaAssignment_apply_free}); hence the points agree at all coordinates except possibly $i$. Their values under the target function remain distinct. The coordinate values at $i$ must themselves differ, since otherwise the points would agree everywhere. Thus setting coordinate $i$ of $x_0$ to its own value recovers $x_0$, while setting it to the value of $x_1$ recovers $x_1$; these identities follow from the coordinate-update facts (\texttt{FABL.setCoordinate_eq_self}, \texttt{FABL.setCoordinate_apply_self}, and \texttt{FABL.setCoordinate_apply_of_ne}). As the coordinate values are signs, they are $1$ and $-1$ in one order or the other. The function therefore differs between the two corresponding coordinate updates. Injectivity of the real-valued sign map preserves that inequality. The characterization of positive influence by such a pair of updates now yields the claim (\texttt{FABL.isRelevant_iff_exists_setCoordinate_ne}).

**Key facts.** `FABL.combineJuntaAssignment_apply_free`, `FABL.setCoordinate_eq_self`, `FABL.setCoordinate_apply_self`, `FABL.setCoordinate_apply_of_ne`, `FABL.signValue_injective`, `FABL.isRelevant_iff_exists_setCoordinate_ne`.
