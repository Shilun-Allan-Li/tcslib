# Check 1: the C1 draft against the drafting brief's §5 and the model `c1-fill-core-cont2.md`

Draft: `campaign/fills/c1/drafts/c1-fill-replaycanon.DRAFT.md` at `6e8db28f` (516 lines).
Line numbers below are the draft's.

## §5, element by element

| §5 element | Draft | Verdict |
|---|---|---|
| Repository section with `@ANCESTOR@` | 15–73; `@ANCESTOR@` at 19, 52, 53; plus a blob check (54–56, `e2cdab7b…`, verified) | present (stronger than the model) |
| `⟨BASE⟩`, `⟨IN-FLIGHT⟩`, banner as placeholders | 77, 80, 9–13 | present; the banner carries drafting text "(the cover's proposal)" (12) and lacks the model's "then deliver this item's zip, partial if need be, and start item 2" (F6) |
| Statement and docstring frozen verbatim | 100–121 | **identical** to `NDCodeSimulator.lean:80–99` at the base (`out/01a-frozen-statement.txt`, line by line) |
| Owned file and regions with base line numbers | 166–189: home = blank line 79 (bridge ends 78, docstring starts 80), body = `sorry` 99, status paragraph = before ` -/` at the end of 95 | correct at the base (and at the tip) |
| Route naming every public declaration cited | 191–301 | present; the route is sound and feasible (check 3) |
| Rule 10 with the 2026-10-23 scope bullet | 343–376; scope bullet 354–358 | present; its seal list omits `optBoolBits`, `optStateBits` (F3) |
| Rule 11 | 377–381 | present |
| No new public declarations | rule 3 (328) | present |
| Landable checkpoints and a budget | 383–392; budget 3 h (banner) | present |
| Duplication: v3 screen, population, no new cross-file pair, ≥ 90% in-file justified | 394–434 | present (check 5) |
| Proof sketches for proofs over 20 lines; public-facing docstrings | region (c), 178–184 | present; the recommended `rc_widen` (235) has no docstring although "every new declaration has a docstring" (F5) |
| Environment: v2.5, roots-only cache, never `lake build`, `lean_check_tree.sh`, order list, base sorries | 436–468 | present |
| Checklist with megafill A's lessons | 479–495 | present: shared logs in the zip (482), per-module memory (65–67, 445), seal not run / no controls a failure (372–374, 491), input-rewind population rule (431–432) |

## The model, section by section

| Model section (`c1-fill-core-cont2.md`) | Draft | Note |
|---|---|---|
| Banner (item k of N, cover file, budget, then the next item) | 9–13 | weaker (F6) |
| Repository and branch; delivery list; checkpoint zips | 15–73 | stronger (blob check; shared logs; per-module memory). The delivery list's shared logs (65–66: "preflight, cache store, roots, cache fetch, manifest check") are fewer than the cover's (55–56: also the cache check) and omit the toolchain and re-check logs: say "every file under `evidence/logs/`" (F6) |
| "If Lean never runs … deliver the environment report only" | 45–48: "do not draft proofs blind" only | weaker (F6) |
| Base, line numbers, in flight | 75–83 | the drafting note on #156 ("`Build/Seam`") is stale since `0e5f210b` (F9) |
| Parallel batches | 85–88 | equal |
| What this is; where it stands; proved modulo; read first; pre-ship | 90–164 | equal or stronger |
| Owned regions | 166–189 | equal |
| Route; promotion candidates | 191–301 | stronger (contracts, recommended definitions, probe-backed identities) |
| Gate guidance | 303–310 | equal (quote of gate 66 note 8 verified verbatim) |
| Cited infrastructure | 312–321 | the claim "all in `C1RCImportProbe.lean.txt`" / "every declaration this brief cites" (150, 312) is not exact (F2) |
| Ground rules 1–11 | 323–381 | rule 6 allows "a Mathlib import only if a needed lemma requires it", contradicting the frozen imports (186–187) and unsafe under the queue's shared cache (F4) |
| Phases / checkpoints | 383–392 | equal |
| Duplication | 394–434 | equal |
| Environment and verification | 436–468 | equal |
| Out-of-scope sorries | 470–477 | extra (good); matches the base set |
| Checklist | 479–495 | stronger |
| Known pitfalls | 497–516 | good; three more found by the review (F5) |

RESULT: complete. Weaker points: F2, F3, F4, F5, F6 (all minor), and F9's stale in-flight note.
