# Gate 133 round 2 · readers for Call, Clean and the Oblivious consumers (PR #300)

**Not yet clear to merge** · PR #300 is a draft. Seyoon dispatches and merges.
The Lean commit is `4ddce70c45e0a397fbc4d9a25ac925da80e05cda`, against campaign Lean
`b313afe522991f2114390952f26ffe7de825bace` (the campaign after #301, which added
`SAT_exists_linear_verifier` to `ClassNP/SAT.lean`, a file this PR does not touch). Round 1 audited
`829648df` and returned HOLD with one major, G133-01, and one minor, G133-02 (`findings.md`,
verbatim). This round checks their resolutions (`resolutions-r2.md`) on fresh evidence.

## What changed since round 1

- `4ddce70c`: `dataTM_ready` reads `obliviousScheduleCfg` through `obliviousScheduleCfg_eq_id` and
  `id_eq` in both places where round 1 read it by `change` and `rfl` (`patch/round1-to-head.patch`
  in the carrier; one declaration).
- The base side of the seal comparison no longer seals declarations that exist only at head.

The scope, rulings, API and statement changes are those of round 1's `pack.md` (bundled).

## Brief for the auditor

1. **G133-01.** Check the repaired passages, and the focused seal (`focused/` in the carrier):
   every head of `dataTM_ready`'s whole-proof seal is sealed, `obliviousScheduleCfg` included,
   except the two legacy header transports `obliviousSchedule` and `decorateTM`, through which the
   unchanged header elaborates. The head body passes (exit 0, no errors); the round 1 body, under
   the same seal, fails at its `change` (`round1.log`).
2. **G133-02.** Check the corrected base comparison (`seals-cmp-base/` in the carrier): no
   guard error remains. 10 of 12 owners pass in full at head, 7 at base. No new failing root. Six
   roots pass at head that fail at base: `call_run`, `regPos_box`, `cleanTM_run`,
   `obliviousSchedule_ready`, `obliviousSchedule_halts`, `setupCfg_finish`.
   `clockStageCfg_captures` passes at both. Two roots fail at both, `dataTM_ready` (its unchanged
   header) and `setupCfg_initializes` (ObliviousSetup's unchanged private cross-type steps), as
   disclosed in G133-06.
3. **Fresh evidence.** Replay, seals, controls, metadata, lint and the copy screen at the round 2
   head on the new base.

## Evidence

- `r2-evidence/REPLAY.json`: the merged-tree replay of the 202-module downstream closure on the
  campaign snapshot after #301 (876 objects; prospective tree
  `e5dc4dfc04957c18f4229d9b5b5467bb133722ed`). 202 passed, 0 failed; the 27 admissions are
  inherited from the campaign.
- Seals: 70 bodies at head; 62 sealed definitions with 124 paired control identities in two
  parts, each closing natively and failing sealed. Metadata: all 70 selected proofs use standard
  axioms only. Lint: no new style finding; the campaign lint's check-8 rows only shrink.
- Copy screen on the same 12 files: BASE `declarations screened: 275; copy pairs: 258; reproduced
  text: 42,997 chars` (on the new base; the 12 files are byte-identical to round 1's base), HEAD
  `274; 256; 42,681`, the same four changed pairs as round 1 (`r2-evidence/PAIR-DISPOSITIONS.json`).
- `r2-evidence/DATA-CARRIER.json` and its recovery map hold 812 logical files: everything round 1's
  carrier held, refreshed, plus the focused seal and the round 1 patch. Decode each gzip+base64
  blob and check its SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate133-call-clean-oblivious-readers-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
