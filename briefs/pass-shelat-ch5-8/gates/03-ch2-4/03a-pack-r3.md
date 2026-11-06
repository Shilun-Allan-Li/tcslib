# Gate 03a ([PS10] ch. 2–4, probabilistic machines, closure, ensembles: the interface), round 3: delta audit pack

**What is audited:** the repair of round 2, on `cryptography/pass-shelat-ch2-4` at
`3f40dfbc32481ebf28b6eb485f7593fa30bf4d1e`. That is the merge of
[Shilun-Allan-Li/tcslib#205](https://github.com/Shilun-Allan-Li/tcslib/pull/205); its Lean files are
#205's head `0cebd6aa`, which also contains #204.
- **Round 2** audited `e28773ef` and found **0 blockers, 2 majors, 3 minors**, all documentation
  (`gate03a-r2-findings.md`, in the bundle, verbatim). The new public interfaces
  (`exists_compParam`, the public `polyTimeComputable_stateFind`) were confirmed.
- **The repair:**
  - #205 changes four docstrings: in `Complexity/Randomized/PPT.lean`, the module docstring and
    `NUPPT.Computes`; in `Cryptography/Asymptotic/Adversary.lean`, the inverter deviation; in
    `Cryptography/Asymptotic/Ensembles.lean`, `Ensemble` and `Ensemble.push`.
  - #204 corrected `FunFamily.ofString`'s example (R2-2's main part, shared with gate 03b). Gate
    03b round 3 verified that correction, and gate 03b is closed.
  - The records changes: DESIGN D3, ledger DL-9, and an erratum in the 03a review.
  - The diff is `evidence-repairs/03a-r2/repair.diff.txt`, the resolutions
    `resolutions-03a-r2.md` (both in the bundle).
- **The deliverable:** **`gate03a-r3-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12). Book pp. 23–24 (Defs 23.4, 23.5, 24.6) and pp. 69–73 (Defs 69.3, 69.4, Lemma 71.5) are the
relevant pages.

## Brief for the auditor

1. **Verify the five round 2 resolutions:** fixed, or not resolved and why.
   - **R2-1 (major):** do `PPT.lean`'s two docstrings and DESIGN D3 now state exactly what
     `A.Uniform ∧ A.Computes f` gives: efficient computation of `f` on the encodings `⟨1^n, y⟩`,
     with the converse `Computes.polyTimeComputable` for `z ↦ f ⟨1^{|fst z|}, snd z⟩`? Is any
     claim about `f` off those encodings left?
   - **R2-2 (major):** `Adversary.lean`'s parenthetical; and `FunFamily.ofString`'s example
     (`OneWay.lean`, as corrected in #204; context, already verified at gate 03b round 3).
   - **R2-3, R2-4, R2-5 (minors):** `Ensemble`'s dyadic sentence; ledger DL-9's `Ensemble.blocks`;
     and the 03a review's erratum and `Ensemble.push`'s "can be lossy".
2. **Check that nothing else changed:** no statement and no other docstring. The diff is the whole
   Lean change.

Pack 03a's severity guide applies. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Round 2 findings, resolutions, the diff | `findings/gate03a-r2-findings.md`, `resolutions-03a-r2.md`, `evidence-repairs/03a-r2/repair.diff.txt` |
| Under audit, at the pin | `TCSlib/Complexity/Randomized/PPT.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Ensembles}.lean` (the changed docstrings) |
| Records under audit | `briefs/pass-shelat/DESIGN.md` (D3), `briefs/pass-shelat-ch5-8/duplication-ledger.md` (DL-9), `review/gate03a-review.md` (the `Fin 3` erratum) |
| Context | `TCSlib/Cryptography/Asymptotic/OneWay.lean` (the corrected `ofString`), `resolutions-03a-r1.md`, `03a-pack-r2.md` |

## Attestations (maintainer execution claims; `evidence-repairs/03a-r2/`)

- **Elaboration** (`replay.log`): the 79 modules downstream of the three files (facades excluded),
  then `audits/pass-shelat/Checks`, each checked alone into a copy of the tree at #203's merge:
  **80 of 80 pass, 0 errors**. The `sorry` warnings are unchanged (63 before, 63 after).
- **Lint** (`lint.log`): `scripts/style_lint.py` reports 0 findings on each of the three files.
- **Axioms:** no statement changed. The round 2 print stands: 164 prints, one `sorryAx` (D11's
  optional `decides_of_decidesWithAdviceInTime`) (`evidence/a2/axioms.log`).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 2 finding: `R2-<n>: fixed / not resolved — <reason>`.

The gate closes at **0 blockers and 0 majors**.
