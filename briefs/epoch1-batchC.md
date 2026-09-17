# Fill campaign — Epoch 1, Batch C: the encoding list layer

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1. The statement
layer is complete and has passed four external audit gates (see `audits/`); what
remains is filling audited-true `sorry`s. This batch owns `Encoding.lean` and
fills its three tractable obligations: the pairing injectivity (a pure list
lemma), the diagonal-pairing machine (a three-phase concrete machine), and the
state-relabeling theorem (a configuration-bijection simulation). The big
`exists_effectiveMachineCode` stays sorry — it is a later epoch.

## Repository, branch, deliverable

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. Base: branch
  `complexity/arora-barak-ch1` — all work is relative to it, **not** `main`.
- Create a working branch `fill/epoch1-C` off `complexity/arora-barak-ch1`; when
  done, open a PR **into `complexity/arora-barak-ch1`**.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5 (fill-campaign ground
  rules), `audits/phase3-reaudit-findings.md` (Argument A's parse-grammar
  analysis — your injectivity proof formalizes its first step) and
  `audits/phase4-findings.md` finding 1 (the corrected `4n + 5` schedule for the
  diagonal-pairing machine).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Encoding.lean`

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned. Setup
  once from the repo root: `lake exe cache get` (several GB on first run).
- **Never run `lake build`** — banned on this branch (plan decision log). The
  repo's `.claude/CLAUDE.md` LeanInfoView-only rule presumes a local interactive
  session; for this cloud task the maintainer-designated verification path is
  the direct-`lean` check script:
  - Bootstrap once on a fresh clone:
    `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  - Iterate: `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Encoding`
    after each edit; re-check the later modules in the order list before the PR
    (Universal, the Uncomputability files, and the facades import you).
  - Final sweep: the full loop; **zero `error:` lines**; `sorry` warnings only
    at the out-of-scope declarations listed below.

## Ground rules (binding)

1. **File ownership.** Modify only `Encoding.lean`. Helpers are `private` unless
   there is a documented reason to export (a parser definition may deserve
   export if `exists_effectiveMachineCode`'s later fill will reuse it — if you
   export, say so in the PR); list every new declaration (public and private)
   in the PR — the next audit round blind-restates them. **The vendored files
   (`Configuration.lean`, `Deterministic.lean`) are frozen — never edit them.**
   If a helper belongs in another shared file, add a `private` copy in your file
   and record the request under "Requested shared lemmas" in the PR.
2. **Statement freeze.** Do not change the name, signature, statement,
   hypotheses, or `[AB09 …]` attribution of any existing declaration. You may
   append to a docstring's proof-sketch paragraph if the delivered proof
   deviates; flag such updates in the PR.
3. **Escalation.** If a target appears false or unprovable as stated, STOP on
   that item, do not alter the statement, record the obstruction under
   "Escalations" in the PR, and continue with your other targets.
4. Do not remove, weaken, or fill any sorry outside your target list — in your
   file that means `exists_effectiveMachineCode` stays.
5. Every remaining `sorry` keeps its docstring sketch; filled proofs keep their
   docstrings.
6. Precise imports; keep the `set_option` headers.

## Targets (recommended order)

### 1. `Turing.pairEncode_injective`

Pure list lemma, no machines. Recommended route (the docstring's aligned-pair
parser, which the phase-3 audit certified): define a `private` parser
`pairDecode : List Bool → Option (List Bool × List Bool)` by two-at-a-time
structural recursion — `false :: true :: rest ↦ some ([], rest)` (separator),
`b :: b' :: rest` with `b = b'` ↦ prepend `b` to the first component of
`pairDecode rest`, anything else ↦ `none` — then prove
`pairDecode (pairEncode x α) = some (x, α)` by induction on `x` (the doubled
blocks are `00`/`11`, never the aligned `01` separator), and derive injectivity
from the left inverse (`Function.LeftInverse.injective` or a two-line direct
argument on the `Prod`). Watch the `x = []` base case
(`pairEncode [] α = [false, true] ++ α`) and note `pairEncode`'s definition
uses `List.flatMap` — `simp [pairEncode, List.flatMap_cons]`-style unfolding.

### 2. `Turing.computesFunInTime_pairEncode_diag`

The diagonal pairing `α ↦ pairEncode α α` in linear time. The docstring sketch
carries the audited schedule (`audits/phase4-findings.md`, finding 1): pass one
costs **two steps per input bit** (emit the bit staying put, emit it again
moving right), then two stationary separator emissions, then the rewind (one
unconditional left step, left while reading `some _`, one right step — total
`n + 2`), then the verbatim pass (`n`), then one halting step: `4n + 5 ≤
6 * (n + 1)`. Machine outline: `k := 0`; states for
{pass1-emit-stay, pass1-emit-move, sep1, sep2, rewind, pass2} (a small inductive
or a sum of `Fin`s — either way `Fintype`/`DecidableEq` derivable or by
`inferInstance`). The proof pattern is `Composition.lean`'s `idTM` /
`idTM_run` / `computesFunInTime_id`: per-phase run invariants by induction on
steps, chained at phase boundaries, then `ComputesInTime.mono`. The rewind
invariant must track the input head moving *left* — `idTM_run` only walks
right, so you will prove the mirror-image position lemma with the
`Turing.moveInputPos` clamp at `0` (the head-position calculation
`j ↦ max (j−1) 0 ↦ 0 ↦ 1`, verified by the phase-4 auditor, covers every
starting position including the empty input).

### 3. `Turing.exists_codeTM`

Every one-work-tape binary machine is equivalent, input by input and step for
step, to a coded machine — a simulation by *bijection*, no new behavior. Plan:

- `M.State` carries `Fintype`/`DecidableEq` (bundled in `FinTM`) and is
  inhabited (`M.tm.q₀`), so `Fintype.card M.State = numStates + 1` for
  `numStates := Fintype.card M.State - 1` (positivity from
  `Fintype.card_pos_iff` + `Nonempty`; close the arithmetic with `omega`).
  `e := Fintype.equivFin M.State` composed with the card equality gives
  `e : M.State ≃ Fin (numStates + 1)` (`Equiv.cast` or `finCongr` on the card
  proof).
- **The sketch mentions `Turing.Action.mapState` — that helper does *not* exist
  in the vendored `Configuration.lean`, and the vendored files are frozen.**
  Define a `private` helper in `Encoding.lean` that maps an action's state
  field through `e` (record update: `{ a with state := a.state.map e }` — check
  `Action`'s exact field names in `Configuration.lean`), and build the coded
  transition `fun q inp ws => mapState e (M.tm.tr (e.symm q) inp ws')`.
- The tape-count cast: `hk : M.k = 1` means the work-tape read/write vectors
  must be transported between `Fin M.k` and `Fin 1`. Rather than `hk ▸`
  gymnastics, consider destructuring: reindex with `Fin.cast hk` explicitly in
  the transition definition and keep every cast in one helper so the
  commutation lemmas see a single normal form.
- Then a configuration bijection `Cfg … M.State ≃ Cfg … (Fin (numStates+1))`
  (mapping only the state component; tapes, heads, output unchanged) commuting
  with `step`, hence with `runFrom` by induction, hence the per-input
  `ComputesInTime` iff in both directions. The in-repo precedent for exactly
  this proof shape is the `Cfg.embedOracle_*` lemma suite in `Oracle.lean`
  (`embedOracle_apply`, `_init`, `_state_eq_none`, `_output`) — mirror its
  structure.

## Out-of-scope sorries you will see (leave every one untouched)

In your file: `exists_effectiveMachineCode`. Elsewhere: `universal`,
`universal_quadratic`, `timed_universal` (Universal.lean);
`computesFunInTime_const`, `computesFunInTime_ifEq`, `computesFunInTime_comp`,
`exists_comp_partial`, `exists_cond` (Composition.lean); `alphabet_reduction`,
`one_work_tape`, `nonnegative_heads`, `oblivious_of_mem_DTIME` (Robustness/);
`timeConstructible_id` (TimeConstructible.lean); `PAL_mem_DTIME_linear`
(Examples.lean); `Computes.exists_computesFunInTime` (Computable.lean);
`UC_not_computable` (Diagonalization.lean); `UC_computable_of_HALT_computable`
(Halting.lean).

## PR checklist (all of it in the PR description)

- [ ] Targets filled (3), one line each on how the proof went vs the sketch.
- [ ] New declarations (public and private) listed, for audit restatement —
      especially the parser and the state-mapping helper, with a note on
      whether the parser is exported for the future canonizer fill.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Verification evidence: final full-sweep log tail; zero `error:` lines.
- [ ] Diff touches only `Encoding.lean`.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `Function.update_noteq` at the pin).
- Core `Nat.pow_pos`, not mathlib `pow_pos` (missing order instances on ℕ).
- `dite_eq_right`/`dite_eq_left` do not exist: `split <;> simp <;> omega`.
- After `cases hs : cfg.state`, insert `dsimp only` to iota-reduce
  `match some q with …` before rewriting, or use nested `split`.
- Avoid bare `simp` when hypotheses use folded forms (`initCfg` is `@[simp]`);
  prefer targeted `simp only`.
- `omega` cannot see `(⟨e, h⟩ : Fin _).val` or un-beta-reduced lambdas:
  normalize with `show` / `simp only` first (see `idTM_run` in
  `Composition.lean`).
- SignType lemma names at the pin: `SignType.coe_one`, `SignType.neg_eq_neg_one`,
  `SignType.coe_neg_one`, `SignType.pos_eq_one`.
- Vendored API: `MultiTapeTM.runFrom_succ_eq_step'`, `MultiTapeTM.step`,
  `Action.apply`, `Cfg.inputSymbol` (double `dite`),
  `moveInputPos_pos_of_ne_right`, `inputSymbolInner`.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]` as
  `⟨s, hhalt, hout, -⟩` (pattern in `Finite.lean`'s `mono`/`output_unique`).
