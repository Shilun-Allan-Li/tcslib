<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.isRealSumOfLinearThresholds_of_count_profile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count Profiles as Sums of Thresholds

**Claim.** If a Boolean function's value is determined by applying a profile $a$ to the number of positive coordinates in $S$, then its real-valued version is a constant plus a sum of $2n$ linear threshold functions.

**Proof.** Take the $2n$ gates supplied by the profile decomposition and use $\operatorname{signValue}(a(0))$ as the constant term. Each gate is a linear threshold function by \texttt{FABL.profileDecompositionGates_isLinearThreshold}. Their real-valued sum, at any input $x$, equals $\operatorname{signValue}(a(\mathrm{count}(x)))-\operatorname{signValue}(a(0))$ by \texttt{FABL.sum_profileDecompositionGates}. The count-profile hypothesis identifies $f(x)$ with $a(\mathrm{count}(x))$; adding back the constant gives exactly the real-valued value of $f(x).

**Key facts.** `FABL.profileDecompositionGates_isLinearThreshold`, `FABL.sum_profileDecompositionGates`.
