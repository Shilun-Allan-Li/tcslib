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
