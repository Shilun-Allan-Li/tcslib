# Gate 147 resolutions

Round 1 CLEAR: 0 blockers, 0 majors, 2 minors, 4 notes (`findings.md`, verbatim).

- **G147-01 (minor), tracked as a follow-up** (the audit's proposed fix). Nondeterminism's
  epoch-3A note names `e3_split_of_body`, and its A3 completion note names `a3n_prevalidation`.
  - They are corrected when the reader follow-up gives `NTIME`/`NEXP` published readers.
  - At that point `ntime_expPow_subset_NEXP` and `EXP_eq_NEXP_of_P_eq_NP` can be edited without
    exposing their anonymous destructuring. Until then, editing the notes pulls those proofs into
    the changed set (the first head's seal failure).
  - Recorded in `campaign/backlog.md` (§1, "Nondeterminism historical notes") and in the ledger's
    R3a entry.
- **G147-02 (minor), fixed in procedure.** From the next dispatch on, a bundle includes the source
  file of every public lemma a changed proof newly cites. For this PR those are
  `TuringMachine/BufferWords.lean` and `ClassNP/PolyTimePairing.lean`; the auditor checked both
  at the audited head. Recorded in `campaign/maintainer/WORKFLOW.md`.
- Notes G147-03–06: no action. The audit's distinction between audited execution records and an
  independent Lean rerun is retained.
