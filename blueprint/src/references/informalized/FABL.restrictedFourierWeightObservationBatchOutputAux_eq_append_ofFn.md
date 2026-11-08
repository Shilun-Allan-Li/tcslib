<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.restrictedFourierWeightObservationBatchOutputAux_eq_append_ofFn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Batch Output as an Appended List

**Claim.** Starting the auxiliary batch procedure with a list $O$ returns the reverse of $O$ followed by the index-ordered list of the rational restricted Fourier weight observations formed from the input triples and target labels.

**Proof.** Proceed by induction on the batch size $m$, allowing the initial list $O$ to vary. When $m=0$, the procedure returns $O$ reversed, and the list of observations is empty. For the induction step, the procedure processes the first input triple, prepends its observation to $O$, and recurses on the tails of the three input sequences. By induction, the recursive result is the reverse of this prepended list followed by the observations from the remaining inputs. Reversing the prepended list places the reverse of $O$ first and then the new observation; the index-ordered observation list likewise consists of this first observation followed by the observations from the tails. Thus the result has the asserted appended-list form.
