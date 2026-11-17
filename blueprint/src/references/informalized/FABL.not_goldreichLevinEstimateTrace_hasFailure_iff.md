<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.not_goldreichLevinEstimateTrace_hasFailure_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trace Accuracy and Absence of Failures

**Claim.** A trace has no inaccurate record if and only if every record in the trace has estimate error strictly below the stated threshold.

**Proof.** A failure is precisely a record in the trace that is not accurate. Negating the existence of such a record says that every record in the trace is accurate. By the definitions of record accuracy and trace accuracy, this is exactly the asserted equivalence.
