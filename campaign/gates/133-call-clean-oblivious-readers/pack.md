# Gate 133 · readers for Call, Clean and the Oblivious consumers (PR #300)

**Not yet clear to merge** · PR #300 is a draft. Seyoon dispatches and merges.
The Lean commit is `829648df28ddfe34af4a7f92a0c0227ba41cec0c`, against campaign Lean
`5ab222167eb12664d97d255766c5def15b6d5d50` (the campaign after #296). This is the first audit.

## Scope and rulings

Gate 122 held four proofs out of #242 as open rule-10 fronts: `Call.call_run`,
`Clean.cleanTM_run`, `obliviousSchedule_ready` and `obliviousSchedule_halts` (ledger, "Gate 122
held Call and Clean fronts"). Seyoon's rulings of 2026-11-14 in that ledger section govern this PR:
- **one PR, full rule-10 repair:** every other-file TCSlib definition the four proofs read gets a
  reader beside it; readers are one lemma per constructor or branch, field lemmas for
  configuration constructors and an iff per predicate, none `@[simp]`;
- **the API as drafted** (53 readers), plus `regBox_iff`, `rlen_of_doubled`/`_of_plain`;
- **`Call.regPos_box` re-proved** and **`off_zero` moved** beside `off` in Layout;
- **the Oblivious transport:** `obliviousScheduleCfg` and six readers in ObliviousSchedule, with
  the run equations of `clockStageCfg_captures`, `setupCfg_initializes` and `setupCfg_finish`
  restated through it, and `obliviousSchedule_ready` (private) stated as a run to
  `obliviousScheduleCfg W a c` with conditions on `c`.

`patch/campaign-to-head.patch` in the carrier is the whole Lean change (12 files). The PR body lists
every new declaration.

## Counts

- `evidence/SOURCE.json`: 72 changed or added declarations in 12 files; 61 added (60 readers and
  the transport definition, counting `off_zero` at its new home); one removed (`off_zero` from
  Call); four statement changes (the three producers and `obliviousSchedule_ready`); no other
  definition changes.
- Seal targets: 70 theorem or lemma bodies at head, 11 at base (the base lacks the new readers).

## Brief for the auditor

1. **Rule 10 in the four targets and `regPos_box`.** Check that each reads other files' TCSlib
   definitions only through published equations, both sealed (every other-file definition reached
   made irreducible, `[-simp]` on the `@[simp]` ones) and in its `rw`/`simp`/`unfold` arguments.
2. **The readers.** Each states what its definition says, sits beside it, is not `@[simp]`, and
   is proved from its own file. Check the case and branch readers cover their definitions'
   cases.
3. **The transport.** `obliviousScheduleCfg` is the identity at the schedule's types;
   `obliviousScheduleCfg_eq_id` exposes that. Check the restated producers mean what they meant
   before and that their only users are the two consumers (`clockStageCfg_captures` and
   `setupCfg_initializes` at Oblivious and ObliviousLedger, `setupCfg_finish` at ObliviousLedger).
4. **Seals and the base comparison** (`seals/`, `seals-cmp-base/` in the carrier). 10 of 12 owners
   pass in full at head, 6 at base. No new failing root. Seven roots pass at head that fail at
   base: `call_run`, `regPos_box`, `cleanTM_run`, `obliviousSchedule_ready`,
   `obliviousSchedule_halts`, `clockStageCfg_captures`, `setupCfg_finish`. Two roots fail at
   both:
   - `dataTM_ready` (Oblivious, adapted to the restated `obliviousSchedule_ready`): its `change`
     and closing `rfl` read through `prepInvariant_run`, whose unchanged statement applies
     `prepInvariant` to a configuration of `obliviousSchedule W a`;
   - `setupCfg_initializes`: after `obliviousScheduleCfg_eq_id`, its proof rewrites with
     ObliviousSetup's private steps (`setupCfg_reset`, `setupCfg_copy`, …), whose unchanged
     statements run `(obliviousSchedule W a).tm` on `setupCfg` configurations.

   Both are pre-existing transports in unchanged statements, outside this PR's ruled scope.
5. **Controls:** 124 paired identities for 62 sealed definitions in two parts; each closes
   natively and fails sealed.
6. **Copy screen** on the 12 files: BASE `declarations screened: 275; copy pairs: 258;
   reproduced text: 42,997 chars`, HEAD `274; 256; 42,681`. Check the four changed pairs'
   dispositions (`evidence/PAIR-DISPOSITIONS.json`).

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the 202-module downstream closure on the
  campaign snapshot after #296 (876 objects; prospective tree
  `9ab1319821611f61db8460350d5954d684ffd5f7`). 202 passed, 0 failed. The 27 admissions are
  inherited from the campaign; the changed proofs have none.
- Metadata: all 70 selected proofs use standard axioms only. Lint: no new style finding; the
  campaign lint's check-8 rows only shrink (definitions that gained readers leave them).
- `evidence/DATA-CARRIER.json` and its recovery map hold 795 logical files: replay receipts and
  logs, seal and control sources and logs on both sides, metadata, QA, both screens with their
  population files and scorer, the campaign versions of the owners, the patch, the transport's
  route probe, and the drivers. Decode each gzip+base64 blob and check its SHA-256 and byte count.
- The checks ran on the cloud machine with the approved wrappers.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate133-call-clean-oblivious-readers-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
