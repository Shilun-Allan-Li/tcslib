# External audit pack: the deepening's API (PR #196, an API gate)

## Why this PR

The general `savitch` (`NSPACE S ⊆ SPACE (S · S)` for every `S ≥ logSpace`, [AB09, Theorem 4.14])
is proved by iterative deepening on the radius over Savitch's midpoint search. The design is
`campaign/items/ch34/savitch-general/SAVITCH-deepening-design.md`; its §9 and §10 are the pre-ship
on the merged tree. A later fill writes a register machine `D` that, at radii `s = 1, 2, …`,
embeds the search block `A E` twice: once asking whether an edge code is reachable (decider `2`
rerouted to the edge language), once asking for acceptance. Its correctness rests on two window
lemmas:
- **termination:** beyond the space bound no edge code is reachable;
- **window exactness:** with no reachable edge code, membership is midpoint reachability at radius
  `s`.

This PR lands both lemmas, in a new module `SpaceComplexity/SavitchARM/Window`, and the facts they
and the deepening machine need. Rule 10 forbids proofs to read other files' definitions except
through published equations. The pre-ship found eleven needed facts with no published form, and
this PR adds them beside their definitions:
- seven definitions' `Iff.rfl` equations;
- two register-file equations;
- a window step lemma;
- a path-shortening lemma.

The fill is then left the machine `D` and its contract. With this PR, the maintainer's probes close
the route's two hard joints on the PR's tree under rule-10 seals:
- **the window lemmas** are the new module itself. A sealed copy elaborates with 0 diagnostics
  (`evidence/rule10/WindowModuleSealed.lean.txt`, sealed over 24 definitions).
  `evidence/route/WindowRouteReal.lean.txt` is the earlier probe of the same proofs.
- **the block fit** (`evidence/route/BlockFitReal.lean.txt`, 0 diagnostics, sealed over 19
  definitions). The search block, embedded with `AHalt.embed_guardLe` and entered with the setup's
  registers, exits with exactly the deepening's question in the codec's terms: whether an edge
  code is reachable at radius `s`.

**Ruled by the user:**
- (2026-10-27) the general Savitch's generalization of `SavitchARM/*`, `Machines/*` and `Codec/*`,
  by PR and gate, FYI only;
- (2026-11-05, decision 4 of the design) `Iff.rfl` equations for `WalkLe` in `Logspace/PathWalk`
  and for `RCode` and `WinRun` in `ExpBFS/Radius`, FYI only.
  - The ruling named four equations. This PR adds three, because `Logspace/ISCountMath` already
    publishes `WalkLe`'s last-edge form (`ISCount.walkLe_succ_iff`), which
    `reach_of_reflTransGen` cites instead of a second successor equation.
- (2026-11-05, decision 5) the window module lands with this PR rather than with the fill.

**The PR:** #196 on `lean/deepen-window-api`, head `89f4ebbc6b0d007c981f907e3353d72fa84fa787`,
based on the campaign at `4ef99963b8839877c843adc8a8b09da64ef1d8b6` (`evidence/patches/`).
- It has nine commits, one per file; the ninth adds the window module and its facade line.
- It is additive: no statement changes, and nothing is removed (`evidence/freeze/`). The facade
  `SpaceComplexity.lean` gains one import and one module-list entry
  (`evidence/freeze/SpaceComplexity-facade.diff`).

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
| `SpaceComplexity/SavitchARM/Window` (new) · `NoEdge` | campaign (decision 5) | `¬ ∃ u < 2 ^ w, ⟨x, u, s⟩ ∈ initLang N ∧ ∃ v < 2 ^ w, ⟨x, v, s⟩ ∈ edgeLang N ∧ Reach (2 ^ w) (StepRel N x s) w u v`, the memberships spelled as in `mem_iff_reach` | a definition |
| `SavitchARM/Window` · `noEdge_of_lt` | campaign (decision 5) | `N.DecidesInSpace L sp → sp \|x\| < s → NoEdge N x s w` | `reflTransGen_of_reach`, `rcode_iff_reflTransGen`, `rcode_iff`, `coreSum_eq_of_code_eq`, `inWin_runWith_of_decides`, `NDTM.inWindow_of_coreSum_eq`, `Cfg.InWindow.core_bounds` |
| `SavitchARM/Window` · `mem_iff_reach_of_noEdge` (+ private `window_code_lt`, `window_reach_of_rcode`) | campaign (decision 5) | `N.DecidesInSpace L sp → codeK N * (s + logSpace \|x\| + 1) ≤ w → NoEdge N x s w → (x ∈ L ↔ ∃ u < 2 ^ w, init ∧ ∃ v < 2 ^ w, accept ∧ Reach (2 ^ w) (StepRel N x s) w u v)`: `mem_iff_reach`'s right side without `sp \|x\| ≤ s` and without the configuration-count bound | (⇒) induction on an accepting branch's prefixes, each a window run (`winRun_iff`, `WinRun.snoc`); an edge head would give a reachable edge code (`rcode_iff`, `reach_of_reflTransGen`), so heads stay strictly inside and one more step stays in the window (`apply_of_lt`, `stepWith_eq_apply`). (⇐) `reflTransGen_of_reach`, `mem_of_codePath` |

**Names** (`evidence/names/`): none of the new names is used on any ref (the campaign, `main`, every
PR head). The new names are the eleven lemmas, `chain_of_walkLe`, and the window module's
`NoEdge`, `noEdge_of_lt`, `mem_iff_reach_of_noEdge`, `window_code_lt` and `window_reach_of_rcode`.
Three choices avoided clashes:
- not `stepRel_iff`, because `Randomized/BPLInPCount` opens `Codec` and defines its own;
- not `walkLe_succ_iff`, because `ISCountMath` has one;
- not `rel_iff`, because Mathlib has several in opened namespaces. The three oracle predicates take
  `_iff_orc`.

## Brief for the auditor

1. **The statements.** Is each true as stated, at the right generality, and named and documented
   for public use?
   - `apply_of_lt` at `s' = s + 1` is `ExpBFS`'s `inWin_stepWith` for every action. Should
     `inWin_stepWith` be re-proved from it, as a later dedup item (12.2c)?
   - The two register-file equations are stated as `Function.update` chains. Is that the form a
     consumer needs, given that `RegExt` compares register files pointwise?
   - `NoEdge` is stated in the codec's terms, that is, the languages the deepening machine's
     deciders answer, rather than through `ExpBFS.RCode`. That makes the block fit's exit
     proposition `NoEdge`'s body verbatim. Is that the right public form?
   - `mem_iff_reach_of_noEdge` drops `mem_iff_reach`'s `sp |x| ≤ s` and its configuration-count
     bound `hcb`, and keeps the width hypothesis. Is anything lost or mis-stated?
   - The window module's docstrings attribute it as configuration-graph infrastructure for
     [AB09, §4.2.1, Theorem 4.14] without space constructibility, not as a result of the book.
     Is that right?
2. **The proofs.**
   - Are `apply_of_lt`, `reach_of_reflTransGen`, `noEdge_of_lt` and `mem_iff_reach_of_noEdge`
     correct?
   - Does the private chain lemma read `WalkLe` only through the two equations?
   - Do `setSt_toV` and `outerSt_toV` read `Machine`'s definitions only through its published
     lemmas?
3. **Rule 10** (`evidence/rule10/`). The four non-`Iff.rfl` proofs are copied into scratch
   modules that import their homes. The window module is copied whole, its own definition
   `NoEdge` left open.
   - **The four proofs' seals:** each copy is sealed over the other files' definitions it could
     reach, 13 in all, with the usual `simp` erasures; each home's own definition stays open.
     Every copy elaborates with 0 diagnostics.
   - **Those seals' controls:** 26, a delta goal and an equation goal per sealed definition.
     Unsealed, 24 close; the two that don't are the delta goals of the recursive definitions
     `WalkLe` and `Reach`. Sealed, none closes.
   - **The window module's seal** (`WindowModuleSealed.lean.txt`): 24 definitions, the window
     route's list (`evidence/route/window-seal/`), and 0 diagnostics.
   - **Its controls**, run on the route probe with the same list: 48. Unsealed, 46 close; the two
     that don't are the delta goals of `Reach` and `NDTM.runWith`, both recursive. Sealed, none
     closes.

   Is any other-file definition unfolded or closed by reduction?
4. **Homes.**
   - Each equation sits beside its definition.
   - `reach_of_reflTransGen` sits beside `Reach`, `reach_of_chain` and `reflTransGen_of_reach`.
     Its new import of `ISCountMath` adds `PathWalk` and `ISCountMath` to `Reach`'s closure.
   - `SavitchARM/Window` imports `SavitchARM/Reach` and `ExpBFS/Radius`, and nothing imports it
     yet; the fill's `Deepen` will.

   Is there a better home for any of them?
5. **Duplication** (`evidence/screen/`, its `README.md`). The v3 screen covers the PR's nine Lean
   files and nine neighbors, 18 in all: base is the campaign, 17 files (the window module did not
   exist), 321 declarations and 64 pairs; head is the PR, 327 declarations and 65 pairs. The
   `Iff.rfl` equations are too short to screen. Earlier runs at the eight-commit head
   (`superseded-6134e5dd/`) and the five-commit head (`round1-12files/`) found no new pair.
   - **One new pair:** `NoEdge` reproduces `Recursion`'s `Rel` (85%). The shared text is the
     codec's query layout `pairEncode x (pairEncode (Nat.bits u) … (Nat.bits s))`, which every
     decider question spells (23 files). **Maintainer's disposition: idiom.**
   - `ISGen.InitM` and `ISGen.AccM` (`Logspace/ISCountGenRadius`) abbreviate two of these
     memberships for the Immerman–Szelepcsényi consumer. `NoEdge` and `mem_iff_reach_of_noEdge`
     spell them out instead, as `mem_iff_reach` does. Should a codec-level home for the query
     memberships be a 12.2c item?

   Does anything re-derive existing material? In particular:
   - `reach_of_reflTransGen` against `ISGen.mem_ball_iff_rcode` (a ball of the walk relation as
     the reachable codes) and against `mem_iff_reach`'s chain cut;
   - `apply_of_lt` against `inWin_stepWith`;
   - `mem_iff_reach_of_noEdge` against `ExpBFS.mem_iff_of_card_eq` and `winRun_of_card_eq`. Those
     have the same shape (every accepting branch is a window run, by induction on prefixes), but
     close the window by equal counts at `s` and `s + 1` rather than by no reachable edge code.
     Likewise `noEdge_of_lt` against `ExpBFS.card_rset_succ_of_le`.
6. **Public-facing text and lint** (`evidence/lint/`): the docstrings and the module lists.
   - Campaign lint: 0 FAIL in every directory touched. `Codec` loses one WARN and `SavitchARM`
     two, because five definitions gain a lemma beside them. The window module adds none.
   - The policy linter has the base's findings at shifted lines and none new; the window module
     has 0 findings (`policy-head-window.txt`).

## Repository-side attestations (verify or challenge)

- **Compilation** (`evidence/chain/`): every module was compiled with `lean -o`, in dependency
  order, into a copy-on-write clone of `oleans-lcf3` (the campaign after #190). That covers the
  eight files, every module on the import paths between them and up to `Savitch` (25 modules), and
  then the window module (`log3.txt`). Every module exits 0. The only diagnostics are
  `RecordTable`'s four existing `sorry` warnings and `Savitch`'s one (`savitch`).
- **Axioms** (`evidence/axioms/`): the eleven lemmas, `noEdge_of_lt` and `mem_iff_reach_of_noEdge`
  are all on `[propext, Classical.choice, Quot.sound]` or fewer.
- **The route on this tree** (`evidence/route/`): the two probes above.
- **Replay:** `replay-ldwa` (`evidence/merged-tree/`), the downstream closure of the PR's ten
  files, 73 modules, chained from `oleans-lcf3`. It passed: 73 modules, 0 failed. The static
  check found 0 mismatches, and the only `sorry`s are the campaign's existing 30 (`RecordTable`
  4, `TQBF` 21, `Hierarchy` 4, `Savitch` 1, the general `savitch` that the deepening fill
  proves).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/96-deepen-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `deepen-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
