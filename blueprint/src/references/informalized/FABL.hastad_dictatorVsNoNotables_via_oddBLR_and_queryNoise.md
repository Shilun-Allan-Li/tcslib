<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.hastad_dictatorVsNoNotables_via_oddBLR_and_queryNoise -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd BLR Query-Noise Test

**Claim.** For every $0<\delta<1/2$, the odd BLR query-noise test is a $(1/2,1-\delta)$ Dictator-vs.-No-Notables test using three-variable 2-linear equations as predicates.

**Proof.** The proof verifies the defining properties of such a test in turn. First, the allowed predicate set is finite, and the parameter inequalities $0<1/2<1-\delta\le1$ follow from the bounds on $\delta$. The soundness error lies in $[0,1]$ for every input in that interval by the range theorem for the Håstad soundness error (`hastadSoundnessError_mem_Icc`), and it tends to zero at the origin by its limit theorem, applied with the positive query-noise cutoff (`hastadSoundnessError_tendsto_zero`, `oddBLRQueryNoiseCutoff_pos`).

Every preprocessed check retains its original predicate. Since each original check uses an equation predicate of the form specified by the allowed predicate set, the preprocessed test does too (`SignTester.noisePreprocessed_usesPredicates`). For completeness, the query-noise parameter bounds give acceptance at least $1-\delta$ for every dictator (`oddBLRQueryNoise_parameter_bounds`).

Finally, fix a function with all stable influences at most $\varepsilon$. If $\varepsilon$ is no greater than the cutoff, the soundness part of those same parameter bounds gives acceptance at most $1/2+\sqrt{\varepsilon}/2$; the error function in this case is exactly $\sqrt{\varepsilon}/2$. If $\varepsilon$ exceeds the cutoff, acceptance is at most $1$ because it is a probability (`SignTester.acceptanceProbability_mem_Icc`), which is the required $1/2$ plus the error value $1/2$. These two cases establish soundness for every allowed $\varepsilon$.

**Key facts.** `FABL.maxE3LinPredicates_finite`, `FABL.hastadSoundnessError_mem_Icc`, `FABL.hastadSoundnessError_tendsto_zero`, `FABL.oddBLRQueryNoiseCutoff_pos`, `FABL.SignTester.noisePreprocessed_usesPredicates`, `FABL.oddBLRQueryNoise_parameter_bounds`, `FABL.SignTester.acceptanceProbability_mem_Icc`.
