# External audit pack: dedup AS-1, `LogProg.astep_call₁` through `astep_call` (PR #214, a dedup gate)

## Why this PR

The dedup window (12.2c), opened on 2026-11-06 by the user, retires the ledger's acknowledged
families one PR at a time. **AS-1** (`campaign/duplication-ledger.md`) covers machine-specific
step lemmas that re-prove the general `astep_*` equations of `SpaceComplexity/Machines/ARM`. Its
six members:
- `Complexity.LogProg.astep_call₁`, in `SpaceComplexity/UnaryLogspace`;
- `BoolCircuit.AdjScan.astep_rd`, `astep_hit` and `astep_jeqFst`, in
  `CircuitComplexity/LogspaceUniformScan`;
- `BoolCircuit.AdjWalk.astep_call₁` and `astep_call₂`, in `CircuitComplexity/LogspaceUniformWalk`.

`CircuitComplexity/` is colleague-owned and needs the owner's authorization, so this PR retires
only the first member. The other five stay in the ledger. `UnaryLogspace` is Hydroxyi's; the user
allowed mechanical edits there, with an FYI.

**The PR:** #214 on `lean/dedup-as1`, head `0bc71211` (full hash in the bundle header): the
change `73629daf`, then a records-only merge of the campaign. One file, one proof
(`evidence/landing/as1.diff`): `simp only [astep, hl]; rw [vword_unary₁]` becomes
`rw [astep_call hl, vword_unary₁]`.

## Brief for the auditor

1. **The member:** does `astep_call₁` still unfold `astep` anywhere, and is its statement
   unchanged?
2. **Completeness:** outside `CircuitComplexity/`, does any other machine-specific step lemma
   re-prove a general `astep_*` equation? The scope search found none. It also found that many
   proofs compute single steps inline with `simp [astep, …]`. Those are not named step lemmas and
   were not counted; say whether they should be.

## Repository-side attestations (verify or challenge)

- **Freeze** (`evidence/freeze/`): 26 → 26 public; only `astep_call₁`'s body changed.
- **Lint** (`evidence/lint/`): the campaign lint on `SpaceComplexity`, 0 FAIL, 80 WARN over 111
  files, as at the base. The policy linter: 0 findings on the file.
- **Replay** (`evidence/merged-tree/`): `replay-las1` at `0bc71211`, over the downstream closure
  of `UnaryLogspace` (7 modules), chained from the campaign's `oleans-lnth`: **7 modules, 0 failed,
  0 `sorry`**; static 0 mismatches.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/105-as1-dedup/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `as1-dedup-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
