# E-D's landing (PR #188, a fill gate): resolutions

**Staged (2026-11-04):** `pack.md`, at #188's head `dae7929c`. Bundle
`93-ed-diagonalizer-fill-bundle.md`, SHA-256
`1c85d70970af764652cdd7b0282c3b6ea80b1274fc425f9472bc4a3434d8ba29` (376 sections), the records at
`8c2ffc38`; in the exchange `arora-barak-ch3-4/outbox/gates/93-ed-diagonalizer-fill-gate/` on
`exchange/pass-shelat-ch5-8`. `replay-led` passed (3 of 3, static-equal; `oleans-led`).
**Dispatched (user, 2026-11-04);** the folder moved to `arora-barak-ch3-4/archive/gates/`.

**Round 1** (`pack.md`, head `dae7929c`). **Findings** (`findings.md`, verbatim, SHA-256
`9da4682e00e783d3973154748a90e08ccaf4485146710e901ebf60e87f5a3bad`; received 2026-11-04): **DO NOT CLOSE, 0
blockers, 2 majors, 2 minors, 11 notes.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | `dz_first` re-derives `Segment.time_eq` (first-exit uniqueness) inline. | **True. Ruled (user, 2026-11-04): fix in #188, round 2.** `a64f513d`: `dz_first` packages the run's first verdict as a second segment and cites `Segment.time_eq`; the statement is unchanged. |
| 2 | major | `dz_split`'s separator cell re-derives `FinTM.bufferTape_append_mid` inline. | **True; fixed in round 2** (`a64f513d`): `FinTM.bufferTape_append_mid s₁ [sp] w 0 Nat.one_pos`, simplified by `hG`. |
| 3 | minor | The brief's malformed-output sentence overstates the implemented behavior (the top tests the first symbol). | **True; corrected** in the brief by an erratum note. The machine needs no change: `hBF` makes every relevant output a singleton. |
| 4 | minor | The census "about 7 of 342" does not match its enumerated union. | **True; corrected** in the ledger ("E-D's delivery"): 8 of 342, deduplicated; E1 retires `qy_call_bound`'s step; findings 1–2 are removed, not counted. |
| 5–15 | note | Integrity, uniformity, the middle, the top, boundaries, the route, screens, rule 10, rule 11, text, the evidence's limits. | Agreed. On note 15, the elaboration, the seal and the axioms are re-run at round 2's head (`evidence/round2/`). |

**Round 2 (2026-11-04):** #188 at `02030b70` (the fix `a64f513d`, then a merge of the campaign
after #184). Checks at the fix:
- the file elaborates against `oleans-led` with no output;
- the reviewer's seal re-run: 350 definitions, sealed copy 0 errors, 350 of 350 controls pass
  unsealed and fail sealed, none passes sealed;
- axioms: `dz_first`, `dz_split` and `exists_diagonalizer` on the standard three.

`replay-led2` is written (3 modules from `oleans-ledge`).

**Round 2 staged (2026-11-04):** `pack-r2.md`, at #188's head `02030b70`. Bundle SHA-256
`15ce490ba941df5345e6585b2e0da96cd9f5d17c8e7f066cda0f54b4b29ff69e` (22 sections), the records at `330ba0dc`.
**Dispatched (user, 2026-11-04);** the folder archived.
**`replay-led2` passed** (2026-11-04): 3 of 3 at `02030b70`, 0 failed, static-equal; snapshot `oleans-led2`.

**Round 2** (`pack-r2.md`, head `02030b70`). **Findings** (`findings-r2.md`, verbatim, SHA-256
`3b4bd408aadbb46a901229f7e1d7c5cc5695be5d674e7d59528aa422b00b4918`; received 2026-11-04): **DO NOT CLOSE, 0
blockers, 2 majors, 0 minors, 6 notes.** Round 1's two repairs and both record corrections are
accepted.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | `dz_split_tape`'s prefix branch re-derives `FinTM.bufferTape_take`. | **True. Ruled (user, 2026-11-04): fix both, and acknowledge the kind.** `49ffc047`: the branch cites `bufferTape_take` with `List.take_left'`. |
| 2 | major | `dz_top_run`'s `hsame` re-derives `MultiTapeTM.runFrom_output_eq_of_halt`. | **True; fixed** (`49ffc047`): `have hsame := MultiTapeTM.runFrom_output_eq_of_halt BF.tm c0 hle hst0`. |
| 3–7 | note | Round 1's repairs; the records; integrity; the seal evidence. | Agreed. |
| 8 | note | The round-2 bundle lacked the replay's log. | Agreed: `replay-led2` passed after the bundle was staged; its log is in `evidence/round2/merged-tree/`. Round 3 attaches its own replay's log. |

**The kind, acknowledged by the user (2026-11-04):** any further inline step in
`NTimeDiagonalizer` that re-derives a published run, buffer or segment lemma is a member of one
family, **ED-IN**, for the dedup window (12.2c), scoped by kind. A later find is an accounting
minor. **A sweep for the kind at round 3's head** (`evidence/round3/sweep.txt`): every
`bufferTape_eq` unfolding, `Nat.exists_eq_add_of_le`, `runFrom_add`, `lt_trichotomy` and
`Nat.find` in the 106 new declarations. It found three more instances of `bufferTape_nat`
(`dz_cell0`, the top's flag cell, the setup's block cell), now cited in `49ffc047`.

**Round 3 (2026-11-04):** #188 at `935245f4` (the fix `49ffc047`, then a merge of campaign records).
Checks at the fix:
- the file elaborates against `oleans-led` with no output;
- the seal re-run: 350 of 350 definitions discriminated, none passing sealed;
- axioms: `dz_split_tape`, `dz_top_run`, `dz_cell0`, `dz_first`, `dz_split` and
  `exists_diagonalizer` on the standard three.

`replay-led3` is written (3 modules from `oleans-ledge`).

**Round 3 staged (2026-11-04):** `pack-r3.md`, at #188's head `935245f4`. Bundle SHA-256
`7b82b58654eb9ed1edb625c5fc2896b2f6a192b3222b561c33341f3472d2ba96` (27 sections), the records at `50809827`.
**Dispatched (user, 2026-11-04);** the folder archived.
**`replay-led3` passed** (2026-11-04): 3 of 3 at `935245f4`, 0 failed, static-equal (no sorry warning); snapshot `oleans-led3`.

**Round 3** (`pack-r3.md`, head `935245f4`). **Findings** (`findings-r3.md`, verbatim, SHA-256
`e2e4efda07ebc44f5b48ea1360a1a67bebdfc1f1d6fe327adce9119331c31f91`; received 2026-11-04): **CLOSE, 0 blockers,
0 majors, 2 minors, 6 notes.** All five replacements accepted.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `qy_patch_end`'s prefix branch re-derives `FinTM.bufferTape_take`, inside ED-IN. | **True; recorded** in the ledger as an ED-IN member, with BW-1's note that `_take` has no counterpart corrected. It is re-pointed in the dedup window, as the user's by-kind ruling sets out. Census 9 of 342. |
| 2 | minor | The record said round 3 attaches its replay log; the bundle had only the script. | **True; corrected:** `replay-led3` passed after the bundle was staged (3/3, static-equal), and its log is now in `evidence/round3/merged-tree/`. |
| 3–8 | note | Integrity; the five replacements; the sweep; ED-IN; the seal. | Agreed. On note 6, two of the three `bufferTape_nat` sites use `simpa`, and the third an explicit `rw`. |

**Gate 93 closes (round 3, CLOSE, 2026-11-04).**
