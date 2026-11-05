# External audit pack: the deepening's API (PR #@PR@, an API gate)

## Why this PR

The general `savitch` (`NSPACE S ⊆ SPACE (S · S)` for every `S ≥ logSpace`, [AB09, Theorem 4.14])
is proved by iterative deepening on the radius over Savitch's midpoint search. The design is
`campaign/items/ch34/savitch-general/SAVITCH-deepening-design.md`; its §9 and §10 are the pre-ship
on the merged tree. The fill writes a register machine `D` that, at radii `s = 1, 2, …`, embeds the
search block `A E` twice: once asking whether an edge code is reachable (decider `2` rerouted to the
edge language), once asking for acceptance. It proves two window lemmas:
- **termination:** beyond the space bound no edge code is reachable;
- **window exactness:** with no reachable edge code, membership is midpoint reachability at radius
  `s`.

Rule 10 forbids the fill to read other files' definitions except through published equations.
The pre-ship found eleven facts the route needs that have no published form. This PR adds them
beside their definitions, so the fill cites rather than re-derives:
- seven definitions' `Iff.rfl` equations;
- two register-file equations;
- a window step lemma;
- a path-shortening lemma.

With them, the maintainer's probes close the route's two hard joints on the PR's tree under rule-10
seals:
- **the window lemmas, in full** (`evidence/route/WindowRouteReal.lean.txt`, 0 diagnostics; sealed
  over 24 definitions);
- **the block fit** (`evidence/route/BlockFitReal.lean.txt`, 0 diagnostics, sealed over 19
  definitions): the search block, embedded with `AHalt.embed_guardLe` and entered with the
  setup's registers, exits with exactly the deepening's question, whether an edge code is
  reachable at radius `s`, in the codec's terms.

**Ruled by the user:**
- (2026-10-27) the general Savitch's generalization of `SavitchARM/*`, `Machines/*` and `Codec/*`,
  by PR and gate, FYI only;
- (2026-11-05, decision 4 of the design) `Iff.rfl` equations for `WalkLe` in `Logspace/PathWalk`
  and for `RCode` and `WinRun` in `ExpBFS/Radius`, FYI only.
  - The ruling named four equations. This PR adds three, because `Logspace/ISCountMath` already
    publishes `WalkLe`'s last-edge form (`ISCount.walkLe_succ_iff`), which
    `reach_of_reflTransGen` cites instead of a second successor equation.

**The PR:** #@PR@ on `lean/deepen-window-api`, head `@HEAD@` (`evidence/patches/`, eight commits,
one per file). It is additive: no statement changes and nothing is removed (`evidence/freeze/`).

## What changed (verify)

| File · declaration | Owner | Statement | Proof |
|---|---|---|---|
| `TuringMachine/Build/CfgRecord` · `Turing.Cfg.InWindow.apply_of_lt` | campaign | `C.InWindow s → (∀ i, \|C.workTapePos i\| < s') → s ≤ s' → (a.apply C).InWindow s'` | reads `Cfg.InWindow` (same file); `Action.apply` only through `Action.apply_workTapes` and `workTapePos_apply_le` |
| `SpaceComplexity/Codec/Bridge` · `Complexity.Codec.stepRel_iff_mem` | Hydroxyi (2026-10-27) | `StepRel`'s body | `Iff.rfl` |
| `SpaceComplexity/Logspace/PathWalk` · `Complexity.walkLe_zero_iff` | Hydroxyi (decision 4) | `WalkLe E n 0 c t ↔ c = t` | `Iff.rfl` |
| `SpaceComplexity/ExpBFS/Radius` · `Complexity.ExpBFS.winRun_iff`, `rcode_iff_reflTransGen` | Hydroxyi (decision 4) | the two definitions' bodies | `Iff.rfl` |
| `SpaceComplexity/SavitchARM/Reach` · `Complexity.LogProg.SavitchARM.reach_of_reflTransGen` (+ private `chain_of_walkLe`) | Hydroxyi (2026-10-27) | `(∀ a b, R a b → a < K ∧ b < K) → u < K → ReflTransGen R u v → K ≤ 2 ^ i → Reach K R i u v` | `reach_iff_walkLe` (from `walkLe_short`), `walkLe_zero_iff`, `ISCount.walkLe_succ_iff`, `reach_of_chain`; imports `Logspace/ISCountMath` |
| `SpaceComplexity/SavitchARM/Recursion` · `rel_iff_orc` | Hydroxyi (2026-10-27) | `Rel`'s body | `Iff.rfl` |
| `SpaceComplexity/SavitchARM/Setup` · `setSt_toV` | Hydroxyi (2026-10-27) | `(setSt s w).toV = update (update (update 0 rs s) rw w) rK (2 ^ w)` | reads `setSt` (same file); `Machine`'s `St.toV`, `St.zero` and register names only through `St.toV_zero` and `St.upd_*` |
| `SpaceComplexity/SavitchARM/Search` · `initO_iff_orc`, `accO_iff_orc` | Hydroxyi (2026-10-27) | the two definitions' bodies | `Iff.rfl` |
| `SpaceComplexity/SavitchARM/Search` · `outerSt_toV` | Hydroxyi (2026-10-27) | `(outerSt s w u v M).toV = update (update (update (setSt s w).toV rU u) rV v) rM M` | reads `outerSt` (same file); `setSt` sealed, `St.upd_*` |

**Names** (`evidence/names/`): none of the eleven is used on any ref (the campaign, `main`, every
PR head). Three choices avoided clashes:
- `stepRel_iff`, because `Randomized/BPLInPCount` opens `Codec` and defines its own;
- `walkLe_succ_iff`, because `ISCountMath` has one;
- `rel_iff`, because Mathlib has several in opened namespaces. The three oracle predicates take
  `_iff_orc`.

## Brief for the auditor

1. **The statements.** Is each true as stated, at the right generality, and named and documented
   for public use?
   - `apply_of_lt` at `s' = s + 1` is `ExpBFS`'s `inWin_stepWith` for every action. Should
     `inWin_stepWith` be re-proved from it, as a later dedup item (12.2c)?
   - The two register-file equations are stated as `Function.update` chains. Is that the form a
     consumer needs, given that `RegExt` compares register files pointwise?
2. **The proofs.**
   - Are `apply_of_lt` and `reach_of_reflTransGen` correct?
   - Does the private chain lemma read `WalkLe` only through the two equations?
   - Do `setSt_toV` and `outerSt_toV` read `Machine`'s definitions only through its published
     lemmas?
3. **Rule 10** (`evidence/rule10/`): the four non-`Iff.rfl` proofs are copied into scratch
   modules that import their homes.
   - **The seals:** each copy is sealed over the other files' definitions it could reach, 13 in
     all, with the usual `simp` erasures; each home's own definition stays open. Every copy
     elaborates with 0 diagnostics.
   - **The controls:** 26, a delta and an equation goal per sealed definition. Unsealed, 24 close;
     the two that don't are the recursive definitions' delta goals (`WalkLe`, `Reach`). Sealed,
     none closes.

   Is any other-file definition unfolded or closed by reduction?
4. **Homes.** Each equation sits beside its definition. `reach_of_reflTransGen` sits beside
   `Reach`, `reach_of_chain` and `reflTransGen_of_reach`; its new import of `ISCountMath` adds
   `PathWalk` and `ISCountMath` to `Reach`'s closure. Is there a better home?
5. **Duplication** (`evidence/screen/`): the v3 screen over the eight files and nine neighbors, 17
   in all, at base (the campaign tip, 321 declarations, 64 pairs) and head (the PR, 323
   declarations, 64 pairs), with **no new pair** (`pairdiff.txt`). The `Iff.rfl` equations are
   too short to screen. An earlier 12-file run at the five-commit head also found none
   (`round1-12files/`). Does anything re-derive existing material? In particular:
   - `reach_of_reflTransGen` against `ISGen.mem_ball_iff_rcode` (a ball of the walk relation as
     the reachable codes) and against `mem_iff_reach`'s chain cut;
   - `apply_of_lt` against `inWin_stepWith`.
6. **Public-facing text and lint** (`evidence/lint/`): the docstrings and the module lists. Campaign
   lint: 0 FAIL in every directory touched. `Codec` loses one WARN and `SavitchARM` two, because
   five definitions gain a lemma beside them. The policy linter has the base's findings at shifted
   lines and none new.

## Repository-side attestations (verify or challenge)

- **Compilation** (`evidence/chain/`): the eight files and every module on the import paths
  between them and up to `Savitch`, 25 modules, compiled with `lean -o` in dependency order into a
  copy-on-write clone of `oleans-lcf3` (the campaign after #190). Every module exits 0. The only
  diagnostics are `RecordTable`'s four existing `sorry` warnings and `Savitch`'s one (`savitch`).
- **Axioms** (`evidence/axioms/`): the eleven lemmas on `[propext, Classical.choice, Quot.sound]`
  or fewer.
- **The route on this tree** (`evidence/route/`): the two probes above.
- **Replay:** `replay-@REPLAY@` (`evidence/merged-tree/`), the eight files' downstream closure,
  72 modules, chained from `oleans-lcf3`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/96-deepen-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `deepen-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
