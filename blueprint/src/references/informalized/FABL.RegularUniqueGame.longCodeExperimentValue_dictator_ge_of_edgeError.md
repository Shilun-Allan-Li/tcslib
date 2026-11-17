<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.longCodeExperimentValue_dictator_ge_of_edgeError -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictator value under low edge error

**Claim.** If every predicate used by the tester has arity at most $r$, dictator completeness at least $\beta$ and edge error at most $\delta$ imply that the dictator long-code experiment has value at least $\beta-r\delta$.

**Proof.** Fix a vertex and a seed. The dictator responses read directly from the label at that vertex would have acceptance indicator at most the operational check value of the dictator long code plus the predicate arity times the vertex's local edge error (\texttt{FABL.RegularUniqueGame.dictatorIndicator\_le\_operationalCheckValue\_add\_error}). The local error is nonnegative (\texttt{FABL.RegularUniqueGame.localEdgeError\_nonneg}), so the arity bound lets us replace that multiplier by $r$. Average this inequality over seeds. The dictator acceptance probability in this average is the tester's acceptance probability on the corresponding dictator function (\texttt{FABL.RegularUniqueGame.randomizedValue\_ofBoolean}); linearity of expectation separates the operational value and the constant error term (\texttt{FABL.pmfExpectation\_add}, \texttt{FABL.pmfExpectation\_const}). By completeness, the resulting average over vertices is at least $\beta$. Averaging the operational term over vertices and seeds gives the experiment value, by the iterated operational expression (\texttt{FABL.RegularUniqueGame.longCodeExperimentValue\_eq\_iteratedOperational}). Hence $\beta\leq$ the experiment value plus $r$ times the global edge error. Since the global edge error is at most $\delta$ and $r\geq0$, rearrangement yields the claim.

**Key facts.** `FABL.RegularUniqueGame.dictatorIndicator_le_operationalCheckValue_add_error`, `FABL.RegularUniqueGame.localEdgeError_nonneg`, `FABL.RegularUniqueGame.randomizedValue_ofBoolean`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.RegularUniqueGame.longCodeExperimentValue_eq_iteratedOperational`.
