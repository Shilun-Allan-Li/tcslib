# have→lemma Triage Pipeline

Working directory for the have→lemma cleanup pass over TCSlib. The goal is to convert
`have` steps into named lemmas **only when they are substantial** — statements a textbook
would name — per Mathlib's contribution guidelines. One-line haves and anything closed by
a single automation tactic stay inline.

## Pipeline

```
/have-triage <file|folder>
  1. lean-have-scanner  → manifests/<Module>.json      (mechanical facts per have)
  2. lean-have-judge    → verdicts filled in manifest   (extract / keep-inline / replace-with-mathlib)
  3. lean-have-primer   → QUEUE.md                      (stub triggers, PENDING-METAPROGRAM)
/have2lemma-run         → ⛔ gated: refuses until the metaprogram exists
```

The manifest JSON is the contract between stages. Schema: see
`.claude/agents/lean-have-scanner.md`. Verdict criteria: see `.claude/agents/lean-have-judge.md`.

## Substantiality criteria (summary)

Extract only when most of these hold:
1. **Standalone meaning** — the type reads as a textbook-displayable fact outside the proof.
2. **Nontrivial proof** — multi-step body; NOT `bodyLines ≤ 1` and NOT closed by a single
   `simp/simp_all/omega/linarith/ring/norm_num/positivity/decide/aesop/exact/gcongr/field_simp`.
3. **Reusable** — used ≥2 times, or an instance of a pattern useful elsewhere in TCSlib.
4. **Clean lifted interface** — ≲5 lifted local hypotheses; no dependence on mid-proof
   `intro`/`obtain`/`set` variables that can't be generalized.
5. **Not already in Mathlib** — otherwise verdict is `replace-with-mathlib` (cite, don't duplicate).

Default when torn: `keep-inline`.

## Metaprogram interface requirements

The conversion metaprogram (to live in `tcstcslib/TCSlib/Tactics/`) currently exists only
as a plan and is expected to operate on a **whole file**. Before `/have2lemma-run` can fire
the queue, it needs:

1. **Selective targeting** — an allowlist of haves, scoped to declaration (have names repeat
   across declarations): proposed syntax
   `#haves_to_lemmas only [h_parseval] in blr_soundness naming [fourierCoeff_sq_sum_eq_one]`.
   Whole-file behavior stays as the no-argument default.
2. **Name override** — use the judge's `proposedLemmaName` (Mathlib naming conventions)
   instead of auto-generated names.
3. **Anonymous-have handling** — positional targeting (declaration + line) for entries marked
   `needsNaming: true`, or a pre-pass that names them.
4. **Manifest-driven batch mode** — a driver that reads `manifests/<Module>.json`, converts
   exactly the `status: "queued"` entries, and writes back `status: "converted"` per entry,
   so the queue stays the source of truth and the pass is resumable.
5. **Verification without builds** — post-conversion checking goes through the VS Code
   LeanInfoView / lean-info MCP diagnostics, never `lake build` (project-wide rule).

When these are satisfied, set `metaprogramReady: true` in the manifests and mark this
section satisfied; `/have2lemma-run`'s gate checks both.

## Status legend (QUEUE.md)

☐ queued · ⏳ needs-review (low confidence — human veto before conversion) · ✔ converted · ✗ rejected/failed
