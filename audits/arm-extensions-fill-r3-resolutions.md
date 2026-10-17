# ARM-extensions fill gate: resolutions (round 3; gate CLOSED)

**Round 3** (`audits/arm-extensions-fill-r3-findings.md`, verbatim; pack
`audits/arm-extensions-fill-r3-pack.md`; bundle SHA-256
`b0e9f8f23937abd5e1747b88add2ea58e0cda19b0034eb6a6e10be47607af834`, 243 sections, dispatch folder
25; evidence `audits/evidence/arm-fill/r3/`): **PASS, 0 blockers, 0 majors, 2 minors. The gate
closes.**
- **L066 closes by acknowledgement.** The user's confirmation of 2026-10-15 is recorded verbatim
  in the findings (§3). L066 stays G / K18 / ARM-2 (a), counted in every ledger. Its
  implementation debt remains: `arm_reach` and `DblLang.Rch.trans` cite ARM-2 (a)'s generic
  guarded-run composition lemma once it lands, designed with Hydroxyi.
- **R2-1 to R2-8 close.** L049 is paid back; the other round-2 findings close as tabled in the
  findings' §6. R2-5 closes at the factoring-plan level; the actual ARM-2 factorings are still
  to come.
- **The payback (PR #101) is gated post-merge.** Its 28 restatements (23 theorem signatures and
  five definition bodies) are exactly the D1 window substitution, `InWin` to `Cfg.InWindow`,
  which is logically equivalent. Its 20 additions and seven removals are as stated, and no
  restatement is unfaithful.
- **Still to gate:** the larger received hosts H7–H13 need their own contract gates before
  further consumers.

The auditor could not run Lean. The elaborations, the replay and the axiom checks remain
supplied evidence. Their re-runs agree with the bundle: the patch reconstruction (zero fuzz), 85
of 86 payback manifest entries, the ledgers and dispositions byte for byte, 349 of 353 and 310 of
314 pair measurements, and the v3 screen over the 73 added files at both trees.

## Findings

| # | Severity | Finding | Resolution |
|---|---|---|---|
| R3-1 | minor | Design §14 H10/H11 still describe parts of the merged payback as future work: H10 names the removed `InWin`, and H11 calls `Codec/Engine` a D7 copy. Backlog ARM-1 gives net −938 lines; the patches give −1,010 | **Fixed.** Two parts were already done at the tip (`135ac413`, after the bundle was built): ARM-1's figure is −1,010, and the H10/H11 status clauses are in the past tense. This commit refreshes the rest. H10's contents no longer list `InWin`; its codes are over `Turing.Cfg.InWindow` (`Build/CfgRecord.lean`). H11's contents name `indicator_inputBitLang`/`indicator_inputLenLang`, `boundedDecodeStride_loop` (with `boundedDecode_loop` its stride-one instance) and `arm_chain`. Its users column now says `Codec/Engine`'s decoder and chains are instances. The "received, ungated; accepted exception" status of the larger hosts stays. Historical packs and landing notes are unchanged |
| R3-2 | minor | Ledger-map rows L002 and L057 name the original side `drop_len`, but both pairs are `orc_len` ~ `QueryReshape.drop_bit`. `drop_len`'s pairs are the new L3-002/L3-004 | **Fixed in the generator** (`r3/payback/scripts/ledger.py`). L002 and L057 leave `ORIG_FOR`, so their original side is `drop_bit` at `QueryReshape.lean:403`, as in `pairs.tsv`. The original-side action now says that `drop_bit` cites `indicator_inputBitLang`, and that `drop_len` separately cites `indicator_inputLenLang`, giving new pairs L3-002 and L3-004. The generator also writes a dated correction note into the map. Regenerated: `payback/ledger-map.md`, then `dispositions.tsv` and `ledger-r3-tables.md` (round 3's `transitions.py` and `tables3.py`, unchanged). Each changes in exactly the two rows; `transitions.tsv` is identical. No classification or total changes |

## The R3-2 regeneration, recorded

- The unmodified generator first reproduced the landed map byte for byte, run on a copy of the
  landing folder with the base export (`eb750e63`). The corrected generator was then run the
  same way.
- `payback/SHA256SUMS` now lists the corrected `ledger-map.md` and `scripts/ledger.py`. The
  as-landed hashes were:
  - `ledger-map.md`: `f8d5f635c2ad2ffe5d1c1e58ce37e004172dd72127201e0aa148b80bf561bce5`
  - `scripts/ledger.py`: `1d794518315e6b33950e7656a8fbcf7b58deda3a30300c572d520b05a68924f5`
- The other 84 entries are unchanged. The 57 that are not `tree/` files check against this
  folder. The 27 `tree/` entries check against the campaign tip `14c2fc19`, since
  #102 and #103 touch none of the 27 files.
- `payback/logs/land.out`, which the bundle omitted, is now included. It matches its manifest
  entry, so all 86 entries check.
- `BUNDLE-FILES.txt`, the bundle's file list, is now at `r3/` beside the evidence it lists.
  It describes the bundle as dispatched: its sizes are the pre-correction ones for the four
  regenerated files.

## Next

- **ARM-2 (a), K18:** the generic guarded-run composition lemma, designed with Hydroxyi. That
  takes a brief, then a PR, then its gate. `arm_reach` and `Rch.trans` then cite it.
- **ARM-2's factorings (R2-5):** I032 into `ConfigGraph`, I040 into `Parse`, and I064 over a
  slot- and result-aware query.
- **The H7–H13 contract gates,** before any further consumer.
