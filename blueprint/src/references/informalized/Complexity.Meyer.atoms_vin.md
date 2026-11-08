<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSigma.lean :: Complexity.Meyer.atoms_vin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Atom Valuations on Valid Encodings

**Claim.** On a nested encoded instance whose length-validity atom is true, evaluating every atom agrees with the stated numerical valuation using the decoded counters, input length and index, marked word, and bounded-time answer function.

**Proof.** The nested-pair projections recover the components of the instance: the input $x$, marked word derived from $U$, counters $t_w,a_w$, index word $j_w$, and padding word $p_w$ (`vx_vin`, `vD_vin`, `vt_vin`, `va_vin`, `vj_vin`, `vp_vin`). The true length-validity atom therefore gives the prescribed lengths for $t_w,a_w$ and the padded index word, as well as $|j_w|\le |x|+1$.

The padding condition and `bits_pad` identify the marked index word with the fixed-width encoding of $|j_w|$. The counter words themselves are their fixed-width encodings of their counter values by `enumWord_ctrVal`. The bound `ctrVal_lt`, together with the lengths supplied by validity, puts both counter values in the width range. Incrementing any such encoded counter gives the encoding of its successor when that successor remains in range, by `incFixed_enumWord`; when it is maximal, the increment is undefined, since `incFixed_eq_none_iff` characterizes exactly the all-ones word. The zero and all-ones encodings are given by `enumWord_zero` and `enumWord_ones`, and `wordOf_of_lt` identifies every in-range word with its fixed-width encoding.

Consequently, each time selector produces the encoding of its specified time value, and each auxiliary selector produces the encoding of its specified counter or index value. For answer atoms, substituting these identifications into the definition of the encoded answer yields the bounded-time answer function. The length-validity atom agrees directly with its numerical counterpart. For the two “not all ones” atoms, the increment is nonempty exactly when the successor remains in range. The zero-counter atom agrees because the counter value is zero exactly when its word is all zeros, using `ctrVal_enumWord` and the zero encoding. The index-bound, index-zero, and index-equality atoms reduce directly to the corresponding numerical comparisons. Finally, the input-bit atom is the defining membership test for the bit predicate derived from $x$ and the index. Since these cases exhaust the atom constructors, their valuations agree as functions.

**Key facts.** `Complexity.Meyer.vx_vin`, `Complexity.Meyer.vD_vin`, `Complexity.Meyer.vt_vin`, `Complexity.Meyer.va_vin`, `Complexity.Meyer.vj_vin`, `Complexity.Meyer.vp_vin`, `Complexity.Meyer.bits_pad`, `Complexity.Meyer.enumWord_ctrVal`, `Complexity.Meyer.ctrVal_lt`, `Complexity.Meyer.incFixed_enumWord`, `Complexity.Meyer.incFixed_eq_none_iff`, `Complexity.Meyer.enumWord_zero`, `Complexity.Meyer.enumWord_ones`, `Complexity.Meyer.wordOf_of_lt`, `Complexity.Meyer.ctrVal_enumWord`.
