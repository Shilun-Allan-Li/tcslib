<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Estimation.lean :: FABL.goldreichLevinTraceEstimate_accurate_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accuracy of a Covered Trace Estimate

**Claim.** If every record in a finite trace estimates its corresponding restricted Fourier weight with error strictly less than $\tau^2/4$, then for any covered frequency prefix contained in the coordinate set $J$, the trace estimate at $J$ and the free part of that prefix has error strictly less than $\tau^2/4$.

**Proof.** Coverage supplies a record in the trace whose coordinate set is $J$ and whose frequency prefix is the chosen set. Since that prefix is contained in $J$, its free part lifts back to the prefix itself ($\texttt{liftFreeFrequency_freeFrequencyPart_eq_of_subset}$). Thus the trace estimate at the free part searches for a record matching exactly this prefix. The search cannot find no record, because the supplied covering record matches. Any record it does find belongs to the trace and has the same coordinate set and prefix. Its accuracy hypothesis therefore gives the required strict error bound, with its restricted Fourier weight identified with the one in the conclusion.

**Key facts.** `FABL.liftFreeFrequency_freeFrequencyPart_eq_of_subset`.
