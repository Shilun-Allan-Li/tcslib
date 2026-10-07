# Continue epoch 2 batch C: timed verifiers for Exercise 2.1

Read `briefs/ch2-epoch2-batchC.md` on the exact campaign branch first. Its
repository rules, frozen statements, proof routes, and verification protocol
remain binding. This continuation does not authorize a different route.

Base of the original batch: `6c09453e6af59ff1575060b66196d28812800d24`.
This checkpoint: `3a7201b13789c5c2f051e69203257f03d3d494c1`.
Import its patch or bundle without replacing newer unrelated work. No remote
branch was pushed. Both HALT targets are already proved; preserve them.

## Exact remaining proof goals

In `TCSlib/Complexity/ClassNP/NP.lean`, the two inline admissions inside
`mem_NP_iff_exists_length_le` have these contexts and goals:

```lean
C c : ℕ
V : Language Bool
hV : V ∈ P
⊢ pairedVerifier C c V ∈ P
```

```lean
C c : ℕ
V : Language Bool
hV : V ∈ P
⊢ paddedVerifier C c V ∈ P
```

The semantic parts of the public proof are finished and compile. No new
helper contains an admission. Do not replace either missing machine proof
with a computability claim, an informal polynomial-time assertion, or an
out-of-scope admitted theorem. This target must have no `sorryAx` at completion.

## Forward machine

Implement the exact `pairedVerifier` predicate:

1. Scan the aligned `pairDecode` grammar; reject malformed words.
2. Recover both components, count their lengths, and test equality to the
   explicit formula `C * (n+1)^c`, with the original `C,c`.
3. Assemble the concatenation and run the old polynomial-time decider.
4. Prove the actual finite machine's completed output is the singleton
   indicator and its runtime is polynomial in the entire input length.

`pairedVerifier_pair` supplies correctness on genuine pairs;
`pairedVerifier_malformed` covers failed grammar parsing. The pinned API
includes `pairDecode_pairEncode` and `pairEncode_injective`; reuse them.

## Reverse machine

Implement the exact `paddedVerifier` predicate:

1. Given total input length, search indices up to that length for
   `n + (C+1)*(n+1)^c = totalLength`. Reject if there is no solution.
2. Split at the recovered index. Restrict marker search to this suffix.
3. Strip at its last true bit; reject if the suffix is all false.
4. Recheck the **original** bound on the stripped witness length.
5. Assemble `pairEncode x u` and run the old polynomial-time decider.
6. Prove the singleton-indicator output and a polynomial time bound for
   the finite machine on **all** strings, including failed searches.

Useful completed lemmas:

- `certificateTotal_strictMono`: uniqueness, including degree zero.
- `certificate_room`: the repaired exact width has space for the marker.
- `certificateSplit_spec`, `certificateSplit_zero`: exact search semantics.
- `stripCertificate_spec`, `stripCertificate_pad`, `stripCertificate_false`.
- `paddedVerifier_append`: the search recovers the original input boundary.
- `paddedVerifier_witness`: the required existential witness equivalence.
- `paddedVerifier_no_split`, `paddedVerifier_no_marker`,
  `paddedVerifier_too_long`: all audited rejection obligations.

The missing infrastructure is **timed machine construction** for fixed-degree
length arithmetic, bounded search, scans/copies, and verifier execution.
The present list-level functions do not constitute that construction.
`PolyTimeComputable.comp` and `FinTM.computesFunInTime_comp` are proved and
usable for timed composition. Do not substitute `exists_comp_partial` or
untimed `exists_cond` where a polynomial runtime is required. The private
counter in `ClassP/TimeConstructible.lean` is a reference implementation,
not a public polynomial-evaluation theorem.

## Verification and acceptance

Use the pinned Lean and cache. Never run `lake build`. Run the owned module
check and all later modules after edits; finish with the full committed
53-module order and the final axiom audit. The checkpoint has 30 admitted
declarations; closing this target alone reduces that to 29, assuming no
concurrent changes.

Update the diagnostic in `verification/Axioms.lean`: require an empty direct
admission-root list for `mem_NP_iff_exists_length_le`. Currently it explicitly
expects and reports that target's own admission, solely to document this
checkpoint. Keep the two HALT roots restricted to `NP_subset_EXP` until the
concurrent batch-A proof is integrated; after integration those must also
become empty.

Rerun statement-freeze checks against the original base, enumerate all new
private declarations, refresh the report and checksums, and deliver the
required ZIP. Do not close the batch until all three headline proofs meet
the brief's axiom requirements.
