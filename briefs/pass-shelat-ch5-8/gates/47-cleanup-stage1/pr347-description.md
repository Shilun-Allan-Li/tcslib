This PR resolves deferred item **DW-5** (`briefs/pass-shelat-ch5-8/deferred-work.md`), finding F-01 of the derand fill review. Seyoon ruled "debt now, fix after" on 2026-11-16.

**Head:** `daa6e173cdd94cad1475b9a96eca613bce53ba61`. **Base:** `cryptography/pass-shelat-ch2-4`. It merges cleanly onto the current tip.

## Changes (proof-only re-derivations plus 9 readers)
- **Readers** (SR-02), each with a formula docstring. None is `@[simp]`.
  - `Turing.ModuleHost`: `hostTMView` with `_eq` and `_q₀`, plus `hostTMView_step_inl`, `host_call_view` and `host_clean_view`.
  - `Complexity.IterateFind`: `copyTMView` with `_eq`, plus `copy_clean_view`. `copyTMView` fixes the start state `0`, because `host_call_view` starts the module at `q₀`.
- **E1 `computesFunInTime_find`** now runs the host and the copier through the views.
- **`polyTimeComputable_find`** is re-derived from E1, by the route pre-approved at derand F-03. This removes a 196-line copy of the old proof.
- Every header and its prose is byte-identical. Both proof sketches are refreshed because the route changed.

## Checks on the merged tree TS1 (`briefs/pass-shelat-ch5-8/cleanup-stage1/final-r1/phase2.md`, 2026-11-17)
- TS1 = records tip `e1d39836` × this PR × #355 = tree `1eaf940b938bb52e3919f5569893b58522df599b`, replayed on olean snapshot #5: **556/556 modules rc 0**, 0 errors, state **1429/1429 OK**; admissions 196 = 196 per module; axioms standard (this PR's 27 constants, census of 21 owners 1224 constants, no `sorryAx`).
- Rule 10 at TS1: `IterateFind` **20 → 0** in strict A/B and coe A/B; the 12 seal rows of this PR's owners equal DW-5's head; controls 10 probes / 30 negatives ALL_OK per variant; 0 foreign unfolds in the changed declarations.
- Since then #357 merged and olean snapshot #6 was adopted at `8060f6b7`: this PR and #355 re-replay on #6 before merge.

## Checks on its own tip (`briefs/pass-shelat-ch5-8/maintenance/dw5/`, 2026-11-16)
- **Rule 10.** F-01's **20 IterateFind seal failures go to 0** in strict A, strict B, coe A and coe B.
  - Paired controls: ALL_OK.
  - Explicit-unfold scan: 0 foreign unfolds in the changed declarations.
- **Build.** 706/706 modules give rc 0 with 0 errors, through root `TCSlib` and both `Checks`. The state check passes 1342/1342.
- **Axioms.** Both theorems, the 9 readers and everything downstream use the standard three only.
- **Statements.** Admissions are unchanged. decls2 shows +9 / 0 / 0. Lint is unchanged, and there is no name clash.

## Disclosures
- E1 restates the dispatch, branch and halt steps in-proof, because the public `host_*` lemmas read `hostTM`'s fields. The view readers restate `host_call`, `host_clean`, `hostTM_step_inl` and `copy_clean` by design (SR-02).
- `host_dispatch`, `host_branch`, `host_halt`, `IterateFind.hostTM` and `copyTM_k` are now unused.
- **Scope ruling (Seyoon, 2026-11-16):** the 26 **pre-existing** seal failures in `ModuleHost` (10) and `IterateFindHost` (16) are unchanged by this PR. They become deferred item **DW-9**.

## Gate
**Gate 47** (Codex) audits this PR together with #355. Seyoon merges.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
