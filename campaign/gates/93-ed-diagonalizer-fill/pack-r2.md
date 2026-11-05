# External audit pack, round 2: E-D's landing (PR #188, a fill gate)

**Round 1** (`pack.md`; findings `findings.md`; resolutions `resolutions.md`) was **DO NOT CLOSE,
0 blockers, 2 majors, 2 minors**, with no soundness defect in `exists_diagonalizer`. Both majors
were inline re-derivations of imported lemmas. **Ruled (user, 2026-11-04): fix in #188, round 2.**

**The PR now:** #188 on `lean/ed-diagonalizer`, head `02030b70102a1d03f8a523a93e36e29639a0015a`:
- `a64f513d`, the fix (`evidence/round2/patches/`);
- then a merge of the campaign after #184, which changes no line of the owned file.

## What changed since round 1 (verify)

| Finding | Change |
|---|---|
| 1, `dz_first` | packages the run's first verdict (`hacc`, `hcut`) as a second `Segment` over `dzQF κ` and cites `Segment.time_eq` for `t = TQ`; the endpoint equation and `Option.some_inj` give the verdict. Statement unchanged |
| 2, `dz_split`'s `hsep` | `FinTM.bufferTape_append_mid s₁ [sp] w 0 Nat.one_pos`, simplified by `hG`, `Nat.add_zero` and `List.getElem_cons_zero` |
| 3, the brief | an erratum note in `campaign/fills/eq/briefs/eq-fill-diagonalizer.md`: the top tests the output's first symbol; `hBF` makes the target unaffected |
| 4, the census | `campaign/duplication-ledger.md`, "E-D's delivery": 8 of 342, deduplicated. E1 retires `qy_call_bound`'s step, and findings 1–2 are removed, not counted |

No other line of the owned file changes since round 1's head.

## Brief for the auditor

1. **Findings 1–2:** are the re-proofs correct and statement-preserving? Do they read other
   files' definitions only through published lemmas (rule 10)?
2. **Further re-derivations.** Round 1's findings were inline sub-steps that whole-statement
   searches had missed. Does any other inline step re-derive a lemma in the closure?
3. **Findings 3–4:** are the record corrections right?

## Repository-side attestations (verify or challenge)

- **Elaboration:** the fixed file elaborates against `oleans-led` with no output.
- **Rule 10** (`evidence/round2/seal/`): the review's seal generator re-run on the fixed file;
  350 definitions and 4 `simp` erasures. The sealed copy elaborates with 0 errors. 350 of 350
  definitions have a control that passes unsealed and fails sealed, and none passes sealed
  (`summary.txt`).
- **Axioms** (`evidence/round2/axioms.out`): `dz_first`, `dz_split` and `exists_diagonalizer` on
  `[propext, Classical.choice, Quot.sound]`.
- **Replay:** `replay-led2` (`evidence/round2/merged-tree/`) covers `NTimeDiagonalizer`,
  `NTimeHierarchy` and `Diagonalization`, chained from `oleans-ledge` (the campaign after #184).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/93-ed-diagonalizer-fill/findings-r2.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `ed-diagonalizer-fill-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
