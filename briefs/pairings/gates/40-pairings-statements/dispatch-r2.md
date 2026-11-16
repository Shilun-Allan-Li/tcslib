# Dispatch · Gate 40 round 2

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/56eff06a8619dfbac945f37e5ccefb1f5e77c8db/outbox/gates/40-pairings-statements-gate-r2)
is staged on the exchange (pushed).
Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 40 (pairing campaign statements),
round 2, in https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 56eff06a8619dfbac945f37e5ccefb1f5e77c8db.
   Read outbox/gates/40-pairings-statements-gate-r2/README.md, pack-r2.md and
   bundle.md. Verify the pack using SHA256SUMS. The round-1 pack is
   outbox/gates/40-pairings-statements-gate/ at exchange
   870bed6ca6d79f43599ab2972f74834137672b2a.
2. Re-audit draft PR #331 at Lean head 9e7a96481785d6cac4dea3b2e990c49ac278b060,
   with campaign records b356e50b1b908b26c1379f2fa9e53d604dabfe41, using the pack.
   Round 1 was HOLD at 110c2f9db810d243693b9a5e8976a5ad205f1bab: G40-01 (major)
   the generic IBEScheme encodings had no fidelity law, so a
   plaintext-revealing scheme with a constant ciphertext encoding was Correct
   and SIDSecure; G40-02 (major) canonical Rule 10 seals covered only three
   modules; four minors (G40-03 T4 sampler parameters, G40-04 source text,
   G40-05 proof-sketch markers, G40-06 README and PR description). Check that
   G40-01 is closed by the fields encPP_inj, encSK_inj and encCT_inj of
   ruling G40-01 (injectivity on reachable objects, not efficient decoding):
   that they rule out the round-1 countermodel, are faithful to BB04's
   adversary view, and that the BB1 proofs bb1_encPP_inj, bb1_encSK_inj and
   bb1_encCT_inj and the bb1Scheme fields are sound, with T1-T4 and
   bb1_sidSecure unchanged. Check G40-02 against the LE-gate40 evidence: the
   canonical suite on 10 owners (seals strict and coe A/B 40/40, paired
   controls ALL_OK, explicit-unfold scan 0 foreign) and its binding to the
   head. Check the doc fixes G40-03 to G40-05, the README and the drafted PR
   description (G40-06), the merge
   39d42e235a62b7085ffc19b01f371015c20d7795 of the records tip into the PR
   (the shared-facade union and no other change; the diff against the tip is
   #331's 13 files; PR base 673a27158338437896c624df32bf5421c6ba45cf),
   LE-doc-abs against the DW-7 BB04 transcription (section 3.1), the build
   evidence (661/661 on the tip, admissions 237 -> 241, axioms) and lint (two
   check-8 WARNs with existing readers). Say whether anything new is
   undisclosed, whether the round-1 confirmations still hold, and whether each
   round-1 finding is closed. The two Gate 40 notes for the later fills (T2's
   relational simulation lemma, the T4 fill route) are not round-2 items. The
   merge interaction with #327 and #324 is a maintainer merge condition, not
   an audit item.
   Supplement (after the pack): records commit
   98a068069adf25d5cac64eb687e8a4163dbe8626 adds
   briefs/pairings/gates/40-pairings-statements/seals-merged/, a re-run of the
   canonical seal suite at the head 9e7a9648 on the merged tree (the pack's
   seal evidence predates the merge). Verify it and say whether it answers
   the pack's question about seals on the merged tree.
3. Return gate40-pairings-statements-r2-findings.md as Markdown in this chat.
   If you need multiple evidence files, return a ZIP containing that Markdown
   and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

Done before dispatch: the records (pin `b356e50b`, then this dispatch commit) and the exchange commit `56eff06a`
(on the exchange tip `f1ccf616`) are pushed; #331's description is set from `pr-description-r2.md`; the current
checkpoint of `briefs/pairings/README.md` is refreshed to this head (after the pin, so the pack still lists it as a
slip).

**Ready to dispatch**
