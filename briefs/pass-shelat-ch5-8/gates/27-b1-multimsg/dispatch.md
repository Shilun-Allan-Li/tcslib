# Dispatch · Gate 27

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/2776272b61fcc7a1adf3f743c735c7e45be5045c/outbox/gates/27-b1-multimsg-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 27 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 2776272b61fcc7a1adf3f743c735c7e45be5045c.
   Read outbox/gates/27-b1-multimsg-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #311 at Lean head 46b780dc1b286f59da18e2d10f188b0faaab8088,
   with campaign records 1ea6503c82b12fd7e49c2e621fcae4cd29d9d08c, using the pack.
   This is a statement audit under ruling B1: the sorried joint, length-generic
   multi-message lemma sliceMultiMessageSecure_of_prfOut (special encryption
   with slices, [PS10, §6.2.2, Definition 93.1, Theorem 99.2]) against the
   needs of yaoHybrid_simulators step 3, its truth with the slices chosen
   after ε, the fit hypothesis, the general L, the proved corollary
   specialScheme_multiMessageSecure_of_joint, the three bridges and three
   readers (Rule 10), and what the sc-garble prover still needs.
3. Return gate27-b1-multimsg-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
