# MIG-0a gate: resolutions (round 1 → round 2)

**Gate:** MIG-0a, the proposed `TCSlib/Complexity/TuringMachine/Build/Contract.lean`
(`audits/mig0a-pack.md`; round-1 bundle SHA-256
`2147706acf81c096d4d9820772596fc9499df8d6b771f21e41c8f965460aa130`, 31 sections).
**Round 1** (`audits/mig0a-findings.md`, preserved verbatim): **0 blockers, 1 major, 5 minors,
14 notes; does not close.** No proved statement was found false.

**No statement or proof of the file changes in round 2.** The repaired file is
`audits/evidence/mig0/Contract-proposed-r2.lean.txt`, 1,100 lines. Removing comments,
docstrings and module docs from both versions leaves identical code apart from the import lines
(`audits/logs/mig0a-r2-code-identity.log`). It elaborates with no errors and no warnings, and its
27 axiom prints are identical to round 1's (`audits/logs/mig0a-r2-{elaboration,axioms}.log`). The
documentation repairs were drafted by a maintainer sub-agent and reviewed by the maintainer, who
checked the code identity, the elaboration and the axioms, and spot-checked the new sketches
against their proofs.

## Major

1. **The direct-replacement claims were wrong.** A first-exit `Contract` does not directly replace
   three kinds of existing specification:
   - `CfgRecord`'s `RecordRun` segments: fixed-length runs avoiding a forbidden set, whose
     endpoint need not be a first visit;
   - return-or-escape rounds, such as `RecordTable`'s `rt_find_round_entry` and the counter
     loop's;
   - `CounterLoop`'s joint head-vector relation `counterSpan`.

   **Resolved in the records:**
   - design §16a, *MIG-0a gate, round 1*, explains the three gaps with the auditor's examples;
   - **MIG-0b now explicitly covers, before any dependent migration,** a segment layer (with
     same-machine concatenation and a bridge to `Contract`), a round layer (positive cuts against
     the anchor and the escape), and a joint-trajectory layer (derived like `Frames`);
   - backlog MIG-12, MIG-13, MIG-15 and MIG-17 are corrected, and now depend on MIG-0b;
   - the file's header lists these layers under *Later rows*, and calls `Contract` the
     first-exit specialization; its `trans` entry no longer calls itself the `RecordRun`
     pattern.

   The auditor's alternatives were MIG-0b or a separate prerequisite. The maintainer chose
   MIG-0b, since the counter loop was already MIG-0b's.

## Minors

2. **Imports and layering.** The unused `CounterLoop` import is replaced by what the file uses:
   `Seam`, `Catalog`, and `Mathlib.Tactic.Linarith`. `linarith` used to arrive through
   `CounterLoop`; each of the three imports was blanked in turn, and each removal breaks
   elaboration. `CounterLoop` is now outside the file's closure, while `Loop` is still inside it
   through `Catalog`. The layering split (a core module that `Loop` and `CounterLoop` can import)
   is MIG-0b item 4. `MultiTapeTM.spaceUsedByTape_le_card_Icc` moves down first.
3. **Proof sketches.** Literal `**Proof sketch.**` paragraphs, 15 in all, now accompany:
   - `trans`, `seq`, `inPhase`, `embed`, `release` and `branch`;
   - their trajectory helpers `seq_traj`, `inPhase_traj` and `branch_traj`;
   - `embedEmitCfg_select`, `clearTM_contract` and `clearTM_contract_frames`.

   `frames_iff` states its equivalence in prose.
4. **Attribution.** The `[AFM26]` entry gives the authors (Anthropic, PBC), the repository
   `anthropics/formal-math` and project `3sum-apsp`, commit `e1a4e650`, and the Apache-2.0
   licence. It names the adapted upstream modules as the vendored headers do:
   - `Lang/Regions.lean` for `SameOutside` and `.keep`;
   - `Lang/Calls.lean` for specification-only calls;
   - `Lang/Logic.lean` for `Ends`.

   The tag is on `Contract`, `Cfg.SameOutside`, `keep_word`, `keep_blank` and `Contract.Frames`.
5. **`ReturnContract`.** The docstring and the header no longer say "whose entry is also its exit".
   The install and emit calls quantify separate anchors that may coincide, so they split on
   `entry = exit`. The advancing writer, in `Build/Scan.lean`, genuinely returns. Design §16a's
   classification is corrected to match.
6. **Records.**
   - The draft count is corrected to 843 lines (design §16a).
   - The pointwise release export `seamReleaseTM_runFrom_pos` is deferred to MIG-0b, in the
     design and in the file; it was never in the file.
   - Both exports' relocation notes now say they move with MIG-0b's layering split, not at
     MIG-14.

## Notes

All notes record no finding. The maintainer swept these documentation points:
- note 9, the routing (seam, branch, phase host);
- note 10, `inPhase`'s condition, now described as sufficient rather than necessary;
- note 12, `select`/`embed`'s output normalization;
- note 14, `SameOutside` as an endpoint relation;
- note 17, the axiom log now headed "27 explicit public declarations";
- note 20, the alphabet-reduction and robustness adapters, now assigned to MIG-0b.

The suggested sanity lemmas (the zero-time characterization, positivity of the compositions) are
MIG-0b item 7, since adding them would change the file's code. Note 16's stronger freeze
comparison is the code-identity check above.

## Round 2: CLOSED (2026-10-13)

`audits/mig0a-r2-findings.md`, preserved verbatim: **0 blockers, 0 majors, 1 minor, 13 notes.
The gate closes, and `Contract.lean` lands unchanged in code**, with its status text updated
and the `TuringMachine` facade import. The auditor:
- reran the code-identity script, getting 667 and 668 code lines, with only the three import
  lines differing;
- checked all 15 sketches against their proofs;
- confirmed the attribution against the vendored headers (full commit
  `e1a4e6508154ea59f030480661590a9fe3018011`), and the corrected `ReturnContract` classification;
- confirmed that MIG-0b's revised scope resolves round 1's major at the design and prerequisite
  level.

**Minor 1, swept:** backlog MIG-15 now says `counterSpan` is a segment property that admits time
zero, so it migrates to the segment and joint-trajectory layers, while the loop body's
interface uses the round layer. MIG-17 says `splitSafe`/`SafeRun` use the segment layer with
endpoint-inclusive avoidance, and become first-exit Contracts only where a first exit is proved.
The auditor's acceptance obligations for MIG-0b (notes 3–4) are recorded in design §16a.
