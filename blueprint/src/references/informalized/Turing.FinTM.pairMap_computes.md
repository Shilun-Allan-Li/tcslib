<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.pairMap_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threaded map time bound

**Claim.** If $M$ computes $f(x)$ within $T(|x|)$ steps for every Boolean word $x$, then the threaded-map controller computes the encoding of the successfully decoded first component paired with $f(x)$, or the empty word when decoding fails, within $4(T(|x|)+|x|+3)$ steps.

**Proof.** Fix $x$. Since $M$ outputs $f(x)$ within $T(|x|)$ steps, its output length is at most $T(|x|)$ (`output_length_le`). The startup lemma (`mapStart`) runs the simulation of $M$ and leaves the controller positioned to validate the pair code, within $T(|x|)+|f(x)|+|x|+5$ steps. The validation lemma (`mapValidate`) then scans the input: if decoding fails, it halts with empty output after at most $|x|+1$ further steps. The computation-time characterization (`computesInTime_iff`) and time monotonicity (`ComputesInTime.mono`) give the desired result in this case.

If decoding succeeds as $(a,b)$, the decoded-word characterization gives $x=\operatorname{pairEncode}(a,b)$, and its length is $2|a|+2+|b|$ (`eq_pairEncode_of_pairDecode`, `length_pairEncode`). The validation phase leaves the controller in a state from which the rewind lemma (`catalogRewind`) returns the input head to the beginning within at most the current head position plus two steps. The replay lemma (`mapPrefix_replay`) then processes the encoded prefix for $a$, reaching the payload stage with output prefix $\operatorname{pairEncode}(a,[])$. Finally, the payload completion lemma (`mapPayload_finish`) emits the stored output of $M$, namely $f(x)$, and halts. The run concatenation law (`runFrom_add`) combines these phases. The resulting output is $\operatorname{pairEncode}(a,[])\mathbin{++}f(x)=\operatorname{pairEncode}(a,f(x))$. Using the bounds above, $|f(x)|\le T(|x|)$, and the encoded input length, the total time is at most $4(T(|x|)+|x|+3)$; computation-time monotonicity (`ComputesInTime.mono`) gives the claimed bound.

**Key facts.** `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.mapStart`, `Turing.FinTM.mapValidate`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`, `Turing.eq_pairEncode_of_pairDecode`, `Turing.FinTM.catalogRewind`, `Turing.FinTM.mapPrefix_replay`, `Turing.FinTM.mapPayload_finish`, `Turing.MultiTapeTM.runFrom_add`, `Turing.length_pairEncode`.
