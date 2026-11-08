<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.cfgRecord_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Configuration Records

**Claim.** Under the stated window and blankness assumptions, two configuration records are equal exactly when the encoded state, input-head position, work-tape contents, work-tape head positions, and tags agree.

**Proof.** Suppose first that the records are equal. Comparing their outer list fields gives equality of the state fields, the input-digit fields, and the remaining fields. Since the digit constructor is injective, the two lists of binary digits agree. Both input-head values are below $2^{\mathrm{posWidth}(|x|)}$: the bound follows from the finite input-position bound and the fact that $|x|+1<2^{\mathrm{posWidth}(|x|)}$ (`record_pos_lt`). Equality of equal-width binary digit lists therefore implies equality of their represented values (`record_digits_inj`), hence equality of the input-head positions. Splitting the remaining lists at the tag field gives equality of the tags and equality of each work-tape cell field. For any cell indexed within the window, injectivity of the cell constructor recovers both its content and its head mark. Every position with absolute value at most $s$ is represented by such an index, namely the natural number corresponding to $z+s$; outside the window, both tapes are blank by the hypotheses. Hence the work-tape functions agree everywhere. Applying the same cell-mark information at each configuration's own head position, which lies in the window, shows that the head positions agree. Conversely, if the states, input positions, work-tape functions, head positions, and tags agree, substitution into the record construction makes the records equal field by field.

**Key facts.** `Turing.record_pos_lt`, `Turing.record_digits_inj`.
