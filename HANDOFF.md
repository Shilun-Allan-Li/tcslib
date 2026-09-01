# HANDOFF — have→lemma extractor campaign (ExtractHavesFile.lean)

**Mission**: make `TCSlib/Tactics/ExtractHavesFile.lean` (`#extract_haves_iter_decl`)
able to convert **every** `have` in TCSlib into lemmas (or gated have→let swaps) with
0-error outputs, through the tool alone — no skiplists, no hand edits to outputs.

**Read first**: memory file `project_extracthaves_iter_mechanic.md` (entries #62–#69 are
this campaign; the numbered-entry history is the debugging bible), and
`.claude/skills/adversarial-extract` (the cycle protocol). Ledger:
`python3 scripts/adversarial_scan.py --ledger` (state), `--top N` (candidates),
`--record <file> <decl> "<result>" <note...>`, `--cleanup` (delete scratch outputs).

## Status right now (2026-08-23)

Every formerly-open failure class is CLOSED, validated on its original instance:

| Instance (July status) | Now | Mechanism |
|---|---|---|
| CircuitTreeManip `exists_circuit_depth_reduction` (5/10) | 10/10, 0 err | #66 `pp.fieldNotation false` + #66b stale-ladder |
| CircuitDegree `pi_coordinate_bad_mul_le` (2/3) | 3/3, 0 err | #59 struct-field routing |
| Circuit `buildFullDTree_depth` (1/3, self-recursive) | 3/3, 0 err | rung L let-swap — **self-recursion class closed** |
| Circuit `toNAnd_toNOr_size_le` (2/5) | 5/5, 0 err | rung T |
| RoundTrip `go_roundtrip_gen` (18/23) | 23/23, 0 err | modern rungs |
| KargerMinCut `mincut_preserved_of_non_crossing` (20/27) | 27/27, 0 err | huLift/hvLift ×4 via rung L (AST eq-param arc NOT needed) |
| SATTo3SAT `transformClause_soundness` (skip-baseline) | 4/4, ZERO diagnostics | **#67 optimistic let-swap + real-file gate — in-file-only class closed** |
| LowDegreeObstruction `function_hammingBall_card_le_binomial` (12/14) | 14/14 DONE | this session; output NOT yet verified/recorded |
| CircuitHelpers `depth2OrToDNF_eval` (6/7) | 7/7, 0 err | **#69 binder-aware have-header split — parameterized-have class closed** |
| LinearCodes `uniformity_lemma` (untested) | 89/89, 0 err | sweep window 12 — largest decl; first organic #69 exercise (6 parameterized haves) |
| RazborovSmolensky `paddedResidueInput_modQTarget_eq_residueIndicator` (untested) | 40/40, 0 err | sweep window 13 — first-attempt clean |
| TVDistance `tvDistance_eq_tvDistanceSup` / `tvDistanceSup_eq_half_sum` (untested) | 5/5 + 7/7, 0 err | sweep window 14 — #69 organic coverage, subtype-braced binder |
| Entropy whole file | have-free, 197 aux lemmas, 0 err | #63–#65 campaign (output deleted after verification per protocol) |

## IN FLIGHT — exact resume point (updated 2026-08-27)

**Windows 10–14 CLOSED, ledger at 69.** All outputs verified 0 errors, `--record`ed,
`--cleanup`ed; `Test.lean` stubbed to `-- idle` + the import. Nothing in flight.

| Window | Decl | Result |
|---|---|---|
| 10 | `ThreeSATToClique :: ThreeSAT_to_Clique_soundness` | 7/7 first-attempt clean |
| 10 | `CircuitHelpers :: depth2OrToDNF_eval` | 6/7 → **7/7** after #69 |
| 11 | `Simple :: innerProduct_le_L43_L4` | 11/11 first-attempt clean |
| 12 | `LinearCodes :: uniformity_lemma` | **89/89, 0 FAILED** — largest decl of the sweep |
| 13 | `RazborovSmolensky :: paddedResidueInput_modQTarget_eq_residueIndicator` | **40/40, 0 FAILED**, ~40min |
| 14 | `TVDistance :: tvDistance_eq_tvDistanceSup` + `:: tvDistanceSup_eq_half_sum` | **5/5 + 7/7, 0 FAILED**, ~4min |

## ⚡ FAST FEEDBACK LOOP — run this before committing a window

```
zsh scripts/shape_regress.sh          # ~7s green / ~12s red, 8 shapes, 31 haves
```
`TCSlib/Tactics/ShapeFixtures.lean` is a shape corpus covering every have-HEADER form in
TCSlib, grounded in a census (151 files, 4711 have headers): colon-newline-wrapped 551,
untyped 433, anonymous 310, bullet-attached 266, explicit-paren binder 18, destructuring 4,
implicit-brace 2, inst-/strict-implicit 0 (forward-coverage). Memory entry #70.

**It is VALIDATED**: against the pre-#69 metaprogram 6 of 8 shapes go red; all 8 green after
the fix; the two binder-free shapes (s4, s5) stay green in both builds — no false positives.
Window 14 added `s8_bracketed_binder_types` (binder whose TYPE carries `{…}`/`[…]`, from
TVDistance `hset_le (S : {S : Set Ω // MeasurableSet S})`). Note the gate counts BOTH
`EXTRACTED` and `TERM-EXTRACTED` as lemma extraction — rung T is a real route, not a
fallback; only `LET-SWAPPED` is the degradation #69 hid behind.

Safe to run mid-window: it uses its own driver `TCSlib/Tactics/ShapeRegress.lean`, never
`Test.lean`, and REFUSES to rebuild the olean while a `bin/lean` run is in flight
(`--force` overrides).

**SCOPE**: parse/assembly only (header split, binders, callsite rewrite, naming, nesting).
It does NOT reproduce semantic failures — `grind` failed, typeclass stuck, ladder blowup —
which need real Mathlib context. **Green is necessary, not sufficient; it does not replace
a window.**

Three traps that made two earlier revisions of this corpus INERT (all fixed, see #70):
`lemma` is a Mathlib macro so a Mathlib-free fixture never reaches the assembly path;
#69's symptom is route degradation (EXTRACTED→LET-SWAPPED) not failure, so a success-only
gate cannot see it; and `attempts=0` looks identical to "all passed" (the decl name must be
AS WRITTEN in the source, unqualified).

## #69 PARAMETERIZED HAVES — CLOSED, organically validated, regression-guarded

`have h (c : T) (hc : P c) : Q c` — both `originalTypeText` sites split the header with
`splitOn " : "`, matching the colon inside the FIRST BINDER GROUP and shipping an
unbalanced-paren type. Every rung died on `PARSE: expected end of input` before any
mathematics. Fix: `splitHaveHeaderBindersType` (binder-aware, built on `scanBinderGroups`)
at both sites, plus binder text re-emitted on the 9 callsite one-liners, gated to fire only
when the emitted type is the have's own SOURCE type (`wonUnfold`/`wonTele` captured
`retType` has already prenexed those binders into leading `∀`s).

**Scope nuance**: the 20 parameterized haves across 9 files are CANDIDATE sites, not 20
breakages — #69 fires only when the winning route uses the source type; rung-T/`wonTele`
routes were never affected (`depth2AndToCNF_eval` passed 13/13 with a parameterized
`h_child` back on 2026-08-13). Untested candidate decls remain: `TVDistance` ×2
(`tvDistance_eq_tvDistanceSup`, `tvDistanceSup_eq_half_sum`), `ACpGates` ×2
(`approxOr_totalDegree`, `count_bad_S`), `Simple :: hypercontractivity_algebra`,
`Kruskal/Exchange :: reduce_to_rest`, `Pinsker`, `FuncDisjointnessLowerBound`,
`GilbertVarshamov :: prob_leq_ball_size`.

**⚠ #69b — STALE OLEAN, read before any driver run in a non-MCP session.**
`scripts/lean_check.sh` resolves `import TCSlib.Tactics.ExtractHavesFile` from the prebuilt
**olean**, not source — so after editing the metaprogram a driver run silently exercises the
OLD code and reproduces the old failure byte-for-byte (this cost one wasted re-grind that
appeared to disprove a correct fix). `shape_regress.sh` now handles this automatically;
for a manual run rebuild first (NOT `lake build` — still banned as a verification path):
```
LP=".lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
LEAN_PATH="$LP" lean -o .lake/build/lib/lean/TCSlib/Tactics/ExtractHavesFile.olean \
  TCSlib/Tactics/ExtractHavesFile.lean     # ~22s
```

**NEXT WINDOW (15)** — from `--top`, still prioritising #69 organic coverage:
- `BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxOr_totalDegree` and
  `:: count_bad_S` (parameterized haves, incl. `have h_term (k) :` — binder with no
  ascription)
- `CommunicationComplexity/DeterministicCC/Hamming.lean :: piece_card` (6)
- `BooleanAnalysis/Hypercontractivity/Bonami.lean :: min_prob_b_reasonable` (5)
Remaining #69 candidate decls after that: `Simple :: hypercontractivity_algebra`,
`Kruskal/Exchange :: reduce_to_rest`, `Pinsker`, `FuncDisjointnessLowerBound`,
`GilbertVarshamov :: prob_leq_ball_size`.

**Verification path in a non-MCP session**: `zsh scripts/lean_check.sh <file.lean>`
(direct `lean`, same path the #67 real-file gate uses). 0 `: error` lines is the gate;
warnings fine. ~90s mid-size output, ~50min for an 89-have grind.

## The operating loop (per window)

1. Preflight: `df -g /` (≥8G to start; kill stale `lean --server` procs to free swap —
   disk recovers within seconds of `pkill -f "bin/lean"`).
2. Write `TCSlib/Tactics/Test.lean`: imports (`Mathlib.Tactic.ExtractGoal`,
   `TCSlib.Tactics.ExtractHavesFile`, the target modules), `open ExtractHavesFile`,
   then 1–2 `#extract_haves_iter_decl "<src>.lean" "<src>_iter_output.lean" "<decl>"`
   lines (1 if disk < 8G or decl is big).
3. `lean_restart_server` → `lean_check_file` Test.lean.
4. Background monitor (bash, `run_in_background`): loop every 20s —
   - disk < 3G → stub Test.lean to `-- idle`, `pkill -f "bin/lean"`, break
     (checkpoint survives; only the in-flight attempt is lost);
   - `.progress` mtime stale > 40min → same stub+pkill ("wedge-stop");
   - DONE detection: count `DONE-DECL` lines (count-INCREASE vs baseline, never
     bare grep — stale DONE lines from prior windows).
5. Tally from `.progress`, VERIFY output via `lean_check_file` (0 errors mandatory —
   classes invisible to every probe surface only here), `--record`, delete outputs.

**Hard rules**: NEVER `lake build` (lean-info MCP is the only verification path).
ALWAYS compile-check ExtractHavesFile after editing it (stub Test.lean with just the
import; a docstring-ordering parse error once wasted a 5h window). A have line whose
3-line window contains `_aux_` is a CONVERTED one-liner callsite — census must not
count it. Windows are swap-bounded (~20–45 conversions each); resume-from-checkpoint
is the design, not a failure.

## Metaprogram mechanisms added this campaign (all in ExtractHavesFile.lean)

- **#63a** `debraceByBlocks` — decl-HEADER `:= by{` only (inner braces unsound to
  rewrite); baseline-gated with **revert-AND-CONTINUE** (braced decls proceed via
  rung T); `extendForBraces` makes the driver's `findAnySpan` brace-aware.
- **#63b** `probeTextGuard` (⋯-elision + 256KB) in `elabCheckFirstError`/`Seq` and
  (#65) `elabGetDeclInfo` — the h_t3/h_decomp wedge lived in the ONE unguarded helper;
  a giant-closure have's ladder candidates reject fast and **rung T converts it**
  (precise `collectFVars` closure ⇒ small lemma).
- **#63c** `<output>.skip` sidecar — retired, superseded; do not use.
- **#63d** `freshAuxName` — cross-window dup guard at the naming site.
- **#65c** `nameAnonymousHaves` nested-rebinder `this`-scope (skip nested block until
  indent < rebinder's, resume after).
- **#66** rung-T renderers: `pp.fieldNotation false`. **#66b** STALE-LADDER fast-path:
  a have with ≥2 unterminated attempt lines in the progress file skips the goal-route
  ladder → rung T first (progress file = cross-window memory).
- **#69** `splitHaveHeaderBindersType` — BINDER-AWARE have-header split (keyword+name off,
  `scanBinderGroups` off the `()`/`{}`/`[]`/`⦃⦄` groups, type = tail after the remaining
  top-level colon). Replaces the `splitOn " : "` drop-first at BOTH `originalTypeText`
  sites, which matched the first BINDER's colon on a parameterized have and shipped an
  unbalanced-paren type → `PARSE` rejection on every rung. Binder text is re-emitted on the
  9 callsite one-liners, gated on `emittedTy == originalTypeText` (the `wonUnfold`/`wonTele`
  captured `retType` already prenexed those binders as leading `∀`s).
- **#67** OPTIMISTIC LET-SWAP + REAL-FILE GATE: baseline-failed (in-file-only) decls
  get ungated pre-passes+swaps, validated by spawning `IO.appPath` (= bin/lean,
  LEAN_PATH inherited) on the whole candidate file; 3 tiers: full candidate →
  pure-swap → pristine positive control. Lean errors are on STDOUT.
- `ptrace` file-only tracing brackets every elaboration helper → wedges name their
  site+input size in `<output>.probelog`.

## After Derandomization: remaining work

1. Whole-library sweep: `--top` still lists untested decls (Simple
   `innerProduct_le_L43_L4` 11, RazborovSmolensky `padded_modQ...` 8, TVDistance
   `card_nat_in_Ico` 7, HammingBound `hamming_bound` 5, …). Same loop; expect mostly
   clean passes; any new failure = new class = fix the GENERAL class (never the
   instance), following the numbered-entry discipline.
2. Known open (nothing currently blocked on them): standalone mid-proof `{ … }` focus
   blocks (only ladder-shapes inside them affected; rung T covers), and the
   hybrid rung idea — rung-T's precise fvar closure + the have's original tactic text
   as proof body (best-of-both; discussed with user, not built).
3. `sqrt_sub_sqrt_floor_le_one`/`am_gm` etc. were converted inside the (deleted)
   Entropy output only — the SOURCE files across TCSlib still contain their haves by
   design; outputs are proofs-of-capability, deleted after verification. If the user
   wants converted outputs kept, skip the deletion step.

## User context

The user (they/them) wants **complete resolution — "partial progress does not count"**.
Report per-class closure with the mechanism named. They asked good questions about
dependency closures: the answer that landed — ladder candidates balloon from printed
CONTEXT (not the have's own text); rung T's proof-term closure is the precise-
dependency mechanism; the 256KB cap is a router to rung T, not a wall.
