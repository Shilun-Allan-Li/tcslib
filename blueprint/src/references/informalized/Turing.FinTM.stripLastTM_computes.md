<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.stripLastTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last-True Stripper Runtime

**Claim.** The fixed Boolean finite Turing machine outputs the encoding of the first component paired with the prefix before the last true bit when the input decodes as a pair and its second component has a true bit; in every other case it outputs the empty word. Its running time is at most $150(n+1)$ on inputs of length $n$.

**Proof.** First, extract the second component of the decoded pair. The pair-extraction machine does this in time $5(n+1)$ (`pairExtractTM_snd`). Next, apply the Boolean scan that reports whether this component contains a true bit; it returns that answer in a one-bit word and takes time one more than the scanned word’s length (`anyTrue_computes`). Since this scan’s time bound is monotone, the buffered-composition bound applies: extracting and scanning together computes the predicate “the decoded second component contains a true bit” in the corresponding buffered time (`bufferedCompTM_computesFunInTime`).

The timed conditional now runs the raw last-true stripper when that predicate holds, and otherwise writes the empty word. The raw stripper returns the prefix before the last true bit, or the empty word if there is no such bit (`rawStrip_computes`); the empty-output branch takes one step (`constTM_computes`). Thus the conditional has the specified output and the time bound given by `timedCondTM_computes`.

To verify the output of the combined machine, split according to whether decoding succeeds. If decoding fails, the required output is empty. If it succeeds with components $(a,v)$ and $v$ has no true bit, both the prescribed result and the conditional branch output are empty. If $v$ has a true bit, `catalogMarker_cases` supplies a prefix $u$ before its last true bit and guarantees that prepending any prefix preserves this last-true decomposition. The decoded input is exactly the encoding of $(a,v)$ (`eq_pairEncode_of_pairDecode`); applying the preservation property with the encoded first component therefore shows that stripping the last true bit from the encoded input produces the encoding of $(a,u)$. This identifies the conditional machine’s output with the claimed function. Finally, the runtime bound simplifies using $\max(4(n+1),1)=4(n+1)$ and elementary arithmetic to at most $150(n+1)$; enlarging a valid time bound preserves the computation (`ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.pairExtractTM_snd`, `Turing.FinTM.anyTrue_computes`, `Turing.FinTM.bufferedCompTM_computesFunInTime`, `Turing.FinTM.rawStrip_computes`, `Turing.FinTM.constTM_computes`, `Turing.FinTM.timedCondTM_computes`, `Turing.FinTM.catalogMarker_cases`, `Turing.eq_pairEncode_of_pairDecode`, `Turing.FinTM.ComputesInTime.mono`.
