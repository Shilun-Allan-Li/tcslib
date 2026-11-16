# Dispatch · Gate 42

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/747b61e7d95d44461639c5884aed33aa4908fc00/outbox/gates/42-sc-yao-gate)
is staged on the exchange (pushed). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 42 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 747b61e7d95d44461639c5884aed33aa4908fc00.
   Read outbox/gates/42-sc-yao-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #341 at Lean head e9b03c437aca251846430ff23b40ee5ff3d3347a,
   with campaign records f22e0f6798815b9263893e61928b4f16452f74ee, using the pack.
   Seyoon's rulings on SY-F01 to SY-F03 are recorded after the pin, at
   67423db6c9d6448ae531b04f42c315585d00d502 (records only):
   fills/sc-yao/final-r1/rulings.md, ledger row DL-51 and the DL-49
   extension in briefs/pass-shelat-ch5-8/duplication-ledger.md.
   A records-only wording correction at
   d6fe1ddd4f38b9bd29d2c707dcb4b60129b4586e replaces "verbatim" in the DL-49
   extension and the post-merge addendum: the two encodeMsgs_eq_encWords
   copies are identical up to bound-variable names, and their docstrings differ.
   This is a proof audit of sc-yao, Yao's garbled-circuit protocol in the
   bit-transfer (OT) hybrid model (PS10 Protocol 162.6, Theorem 163.7):
   the soundness of yaoHybrid_polyTime and yaoHybrid_simulators (and the
   derived yaoHybrid_hbcSecure) against the frozen statements and the book;
   frozen-statement integrity (in Yao.lean only the six approved regions
   change, plus LE-title's title line; Uniform.lean gains only the seven
   SY-3 rfl/Iff.rfl readers; DAGCircuit.lean is unchanged against the tip);
   the landing edits LE-bullet, LE-reuse (SY-F05), LE-title (optional) and
   LE-doc (docstring-only, SY-F04); duplication (an undisclosed duplicate of
   a public lemma is a major; SY-F01 is confirmed, the four helper imports;
   SY-F02 is ruled ledger then promote, DL-51; SY-F03 is ruled ledger for
   both copies, DL-49 extended with sc-yao's and #327's
   encodeMsgs_eq_encWords; check those ledger rows against the code; SY-F05's
   remaining OTAnswerWords pair against #324's HybridProtocol.length_answersA/B
   is still open, proposed as a ledger row with a re-point after #341 merges
   and awaiting Seyoon's acknowledgement, so grade that disposition; grade
   SY-F01 to SY-F12); Rule 10 (seal A on Yao.lean 0; seal B's 9 new errors
   attributed to PolyExpr.eval; Uniform.lean's 4 inherited errors; helpers
   coe-A 68/68 with sampled variants; the paired controls; the
   explicit-unfold scan); and the docstring and sketch rules, the sources
   rule (no fabricated tags) and evidence completeness, under the rulings in
   the pack. The integration build of the head on the current tip, which
   now has #327 and #324 (201bf57a), is running separately; it is a
   maintainer merge condition, not an audit item.
3. Return gate42-sc-yao-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `f22e0f67`; the rulings `67423db6`; the wording correction `d6fe1ddd`; the gate directory `895bc778`;
then this dispatch commit) and the exchange commit `747b61e7` (on the exchange tip `14e681e6`) are pushed. The exchange
commit was amended locally to add the rulings before it was pushed; it replaces the unpushed `e5390b37`.

**Ready to dispatch**
