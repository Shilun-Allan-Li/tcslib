<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.arbitraryPropertyPCPPSystem_close_of_acceptanceProbability_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closeness from High Acceptance

**Claim.** If the constructed verifier accepts with probability at least $1-\frac{1}{1000}\varepsilon$, where $0\le\varepsilon\le1$, then the input string is within relative Hamming distance $\varepsilon$ of a string satisfying the property.

**Proof.** Write $\Pi$ for the Boolean function represented by the proof. The verifier is an equal mixture of two tests. Its assumed acceptance lower bound is $1-(1/500)(\varepsilon/2)$, so the component bound for a uniform mixture implies that each test accepts with probability at least $1-(1/500)\varepsilon$ ($\texttt{component_acceptanceProbability_ge_of_uniformMixture_ge}$). The property-test component lifts to the test on $\Pi$ with the same acceptance probability ($\texttt{boolTruthTableLiftTester_acceptanceProbability}$). Rescale the error parameter to $\varepsilon/5$, which lies in $[0,1]$; then this lower bound is exactly the hypothesis needed for the dictator-subclass local-test guarantee, whose rate is $1/100$ ($\texttt{dictatorSubclass_isLocalTester}$). That guarantee supplies an accepted dictator close to $\Pi$, with distance at most $\varepsilon/5$. Its index corresponds to some string $w_0$ in the property: membership in the property index set is equivalent to the corresponding string satisfying the property ($\texttt{mem_propertyIndexSet}$). In the proof, the case that the property has no member is therefore impossible.

The closeness bound is also $200(1/1000)\varepsilon$. The dictator local-correction estimate then says that for every coordinate $j$, correction recovers the bit $w_{0,j}$ with probability at least $1/2$ ($\texttt{equation_7_1}$). Meanwhile, the consistency test's rejection probability is at most $(1/500)\varepsilon$, by the component acceptance bound. The coordinate-consistency estimate converts this into $(1/2)\operatorname{dist}(w,w_0)\le(1/500)\varepsilon$ ($\texttt{half_relativeHammingDist_le_coordinateConsistency_rejection}$). Multiplying by $2$ gives $\operatorname{dist}(w,w_0)\le(1/250)\varepsilon\le\varepsilon$, since $\varepsilon\ge0$. As $w_0$ satisfies the property, this proves the claim.

**Key facts.** `FABL.component_acceptanceProbability_ge_of_uniformMixture_ge`, `FABL.boolTruthTableLiftTester_acceptanceProbability`, `FABL.dictatorSubclass_isLocalTester`, `FABL.mem_propertyIndexSet`, `FABL.equation_7_1`, `FABL.half_relativeHammingDist_le_coordinateConsistency_rejection`.
