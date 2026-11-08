<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.restrictedFourierWeightObservationBatchOutput_eq_ofFn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Batch of Restricted Fourier Observations

**Claim.** The batch output is the list, in index order, of the rational restricted Fourier weight observations formed from the three input sequences and the target labels.

**Proof.** Apply the auxiliary batch-output identity (FABL.restrictedFourierWeightObservationBatchOutputAux_eq_append_ofFn) with the initial observation list empty. Its reverse is empty, so appending it leaves exactly the list of input-derived observations indexed by $i<m$. This is the claimed batch output by its definition.

**Key facts.** `FABL.restrictedFourierWeightObservationBatchOutputAux_eq_append_ofFn`.
