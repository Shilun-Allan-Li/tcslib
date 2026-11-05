# NF's landing (PR #191, a fill gate): resolutions

**Staged (2026-11-05):** `pack.md`, at #191's head `e8994dc1` (the campaign after #190 merged in).
Bundle `95-nf-landing-fill-bundle.md`, SHA-256 `15b5843f3f265051df45e46ad3c020a56adb143de72ae468d4ffed7e4ea1baf8` (415 sections), the records at
`1500583b`; in the exchange `arora-barak-ch3-4/outbox/gates/95-nf-landing-fill-gate/`.

**Replay (2026-11-05): `replay-lnf` passed**, 4 modules, 0 failed, 0 `sorry`; the static check 0
mismatches (`evidence/merged-tree/`). `NTimeHierarchy`'s theorems are on the standard axioms
(`evidence/axioms/NTHAx.out`).

#191 is clear to merge once gate 95 closes with zero blockers and zero majors.

**Dispatched (2026-11-05, the user)**, bundle SHA-256 `15b5843f…`, findings file
`nf-landing-fill-findings.md`.

## Round 1 findings (received 2026-11-05)

`findings.md`, verbatim from the exchange inbox (`arora-barak-ch3-4/inbox/nf-landing-fill-findings.md`,
exchange commit `4da7789c395d2bad6d86d1520d7faf3709d13af9`), SHA-256
`7aa285060b2bd9d5a5c7c6f957f78c00bd7ea5098f9c8a160565650c6a4413f8`.

**Verdict: does not close.** 0 blockers, 1 major (F1, three inline re-derivations of
`BufferWords` identities in `NDNormalForm`), 4 minors (F2–F5), 4 notes (F6–F9). Dispositions
follow below as the repairs land.

**Not yet clear to merge: #191** (gate 95 has a major open).

## Round 1 dispositions (the repair commit `10c015177fde0f9f2b020c010cf44f0f3b3dd37f`)

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Repaired, by the user's ruling (2026-11-05: repair).** The three sites cite `BufferWords`: `nf_bClear`'s `hw` is `rw [h, FinTM.bufferTape_drop R i h0, add_comm]`; `nf_aReturn`'s `hw` and `nf_region`'s cell `\|R\|` cite `FinTM.bufferTape_eq_none_of_not_mem` (in `nf_region` with its side condition `List.length_ofFn`). Statement-preserving body edits (`evidence/round2/freeze/`). The sweep is re-run with the buffer and time-split patterns (finding 5). |
| 2 | minor | **Fixed.** The seal is regenerated on the repaired blob, with candidates taken at its seven imports, so `Build/Contract/Basic`'s definitions (`Turing.Segment` among them) are sealed with controls: 277 candidates (the Lean audit's list = the textual one), both sealed copies 0 diagnostics, all 277 discriminated (272 by generic controls, the 5 derived instances by source controls), 43 of 43 source controls failing sealed (`evidence/round2/seal/`). `NFAx` is re-run on the repaired blob, and the plain elaboration log is shipped (`evidence/round2/axioms/`, `evidence/round2/elab/`). The round-1 pack's rule-10 and axiom lines described `c528e375` plus the seal; that is recorded here as an erratum. |
| 3 | minor | **Fixed.** `nf_pack`'s `hinit` is `(Cfg.mapState_eq_of_fields _ e _ …).symm`, as `nf_tag`. The other eleven `Cfg.ext` blocks are configuration-record equations, not renamings (the auditor's classification, confirmed in the sweep). RN-1's accounting is corrected in the ledger. |
| 4 | minor | **Fixed.** The headline's proof sketch follows the implemented route: the display of `2k + 4`-bit records (choice bit, claimed reads, end flag) on tape `0`, the control sweep, the replay sweeps against two-cell blocks on tape `1`, the constant, the two transfers, the relabeling. "Fill obligations, named: …" is dropped. Docstring only. |
| 5 | minor | **Fixed.** The screen is re-run with `TuringMachine/BufferWords` in the population (`evidence/round2/screen/`): 1,444 declarations, 13 pairs, 5,191 characters at the repaired head; 0 new and 0 gone against both round-1 runs; the one changed pair lost the hand-written buffer indexing the repair removed. The sweep adds `bufferTape_nat`, `List.getElem?_*`, `runFrom_add` and the hand-rolled time splits, with a disposition per hit (`evidence/round2/sweep.md`): the three sites cite `BufferWords`; `nf_pack` cites `CfgFacts`; NF has no RN-1 member left; every other hit is an idiom (the thirteen time-split lines over windows that are not `Segment`-typed; four of the nine sites sit inside one leaf machine, not across a phase redirect, a correction to finding 5's wording). |
| 6 | note | Recorded; no change (history text). |
| 7 | note | Recorded; no change. |
| 8 | note | Recorded; no change. |
| 9 | note | **Recorded in the ledger:** both first-halt sites (`nf_forward`, `ExhaustiveReplay`) in the row candidate; `CodeSimulator`'s private `canonStageBuffer_none` for re-pointing in 12.2c; one numbering for F2 and F8. |

**Replay of the repaired head:** `replay-lnf2` passed, 4 modules, 0 failed, 0 `sorry`, static 0
mismatches, chained from the first cloud snapshot `oleans-cloud0` (`evidence/round2/merged-tree/`),
at #191's head `ac934f99cc5d5009b8027fc0516ab2fd5be0042d` (the repair, then a merge of the campaign
that changes no `.lean` file).

**Round 2 (2026-11-05):** `pack-r2.md`, at #191's head `ac934f99cc5d5009b8027fc0516ab2fd5be0042d`.
