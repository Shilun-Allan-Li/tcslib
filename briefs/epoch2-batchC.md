# Fill campaign — Epoch 2, Batch C: the remaining tape simulations

## Context

You are filling two Lean 4 proofs in **tcslib**'s formalization of
Arora–Barak, *Computational Complexity: A Modern Approach* (2009), Chapter 1:
`Turing.FinTM.nonnegative_heads` — [AB09, Claim 1.8] rendered as
"unidirectional (nonnegative) work-head use suffices" — and
`Turing.FinTM.alphabet_reduction` — [AB09, Claim 1.5], binary alphabet
suffices with constant-factor slowdown. Do **`nonnegative_heads` first**: it
is a near-lockstep folding simulation (one simulated step ↦ boundedly many
composite steps, no growing sweeps) and warms up the machinery;
`alphabet_reduction` is the first genuine macro-step (block-encoding)
simulation. Both sketches were corrected and certified by the phase-2
external audit — the corrected designs below are binding.

## Repository, base, deliverable (zip — there is no PR step)

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`, branch
  `complexity/arora-barak-ch1`. **Base commit: `24687122`** — verify with
  `git rev-parse HEAD` after checkout. Create a local branch `fill/epoch2-C`
  and commit your work there. GitHub write access is not available from this
  environment; **do not attempt to push or open a PR.**
- **Deliverable: a single zip archive** containing, at minimum:
  1. `REPORT.md` — the full report per the checklist below.
  2. The complete modified source files at their repository paths.
  3. `epoch2-C.patch` — `git format-patch 24687122 --stdout > epoch2-C.patch`.
  4. `epoch2-C.bundle` — `git bundle create epoch2-C.bundle 24687122..fill/epoch2-C`.
  5. `final-sweep.log` — the complete output of the final full sweep.
  6. `axioms.log` — `#print axioms` for both filled theorems (and, as a
     regression check, `Turing.FinTM.one_work_tape_binary`, which chains
     `alphabet_reduction`), via a scratch file *outside* the repository with
     the check script's `LEAN_PATH`. Expected for your two:
     `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**.
  7. `SHA256SUMS` — a hash manifest of every file in the zip.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5,
  `audits/phase2-findings.md` and `audits/phase2-reaudit-findings.md` (the
  corrected fold movement table and block-encoding design live there), and
  the docstring sketches on both targets.

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean`
  (`nonnegative_heads`; the `NonnegativeHeads` definition is **frozen**)
- `TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean`
  (`alphabet_reduction`)

All helpers are `private`, per file, defined *above* the theorem that uses
them (Lean has no forward references). Needed lemmas that belong in shared
files (`Finite.lean`, `Simulation.lean`, `StateRenaming.lean`; vendored files
**frozen**): add a `private` copy and record the request under "Requested
shared lemmas" in `REPORT.md`.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once from the repo root: `lake exe cache get` (several GB).
- **Never run `lake build`** (banned; plan decision log). The repo's
  `.claude/CLAUDE.md` LeanInfoView-only rule presumes a local interactive
  session; the maintainer-designated verification path is
  `scripts/lean_check_tree.sh` (strengthened: fails on nonzero `lean` exit,
  `error:` diagnostics, or a missing fresh `.olean`). Sweep recipe:
  `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )`
- Bootstrap once with that sweep; iterate on your modules (AlphabetReduction
  precedes SingleTape in the order; re-check everything after your earliest
  touched module); finish with the full sweep. Pass = sweep exits 0, zero
  `error:` lines, sorry warnings only at the out-of-scope list below.

## Ground rules (binding)

1. **File ownership** as above; every new declaration listed in `REPORT.md`
   (the next audit round restates them).
2. **Statement freeze.** No change to any existing declaration's name,
   signature, statement, hypotheses, or attribution — including
   `NonnegativeHeads` itself. Docstring sketch paragraphs may gain an
   appended implementation note; flag it.
3. **Escalation.** If a target appears false or unprovable as stated, STOP on
   that item, record the obstruction under "Escalations", and continue with
   the other target.
4. No other sorry is touched. 5. Sketches stay. 6. Precise imports; keep the
   `set_option` headers.

## Targets (in this order)

### 1. `Turing.FinTM.nonnegative_heads` (Bidirectional.lean)

Conclusion shape: `∃ Γ' … (e : Γ ↪ Γ') M' c, M'.NonnegativeHeads ∧
M'.k = M.k ∧ M'.ComputesFunInTimeVia e f (fun n => c * (T n + 1))`.

The audited construction (phase-2 findings; the corrections are binding):

- **Fold each work tape at the origin**: simulated cell `z` lives at folded
  coordinate `φ z = if 0 ≤ z then z else -z - 1`; each nonnegative folded
  cell carries **both** simulated cells `z` and `-z-1`.
- **Alphabet (audit-corrected)**: `Γ' = Bool × Option Γ × Option Γ` — an
  origin/track tag plus the two *independent* `Option Γ` payloads (marked
  blanks must be representable on each track separately). `Γ` embeds via `e`
  into the appropriate track with the other blank. The phase-2 round-2
  finding fixed this alphabet exactly; do not substitute a product without
  the `Option`s.
- **Movement table**: the simulated head's sign determines which track is
  active; crossing the fold (a move between `z = 0` and `z = -1`) becomes a
  **stationary** composite move that toggles the track tag at folded cell
  `0` — the phase-2 findings contain the full worked movement table
  (direction × track): mirror it case by case.
- **Detectable origin**: folded cell `0` is tagged so the simulator knows
  when it stands at the fold (the `Bool` component).
- **Safe halting off the embedding** (phase-2 audit, finding 10 / case A14):
  on input symbols outside `e`'s image — where `ComputesFunInTimeVia`
  promises nothing but `NonnegativeHeads` still quantifies — the simulator
  halts immediately on first contact, preserving nonnegativity. Check the
  `NonnegativeHeads` definition in the file and make sure your machine
  satisfies it on **every** input, not only embedded ones.
- Near-lockstep: constant composite steps per simulated step, hence the
  linear `c * (T n + 1)` bound.

In-repo precedent for the "coordinate-transported configuration" proof shape:
`MultiTapeTM.relabelState_step`/`_runFrom_init` in `StateRenaming.lean`
(state coordinate) and `Cfg.embedOracle_*` in `Oracle.lean` (tape extension)
— yours transports the *tape* coordinate through `φ` with a two-track
payload; write the configuration-shape function first
(simulated `Cfg` ↦ folded `Cfg`), prove one step-commutation lemma by the
movement table, then induct.

### 2. `Turing.FinTM.alphabet_reduction` (AlphabetReduction.lean)

Statement: given `e : Bool ↪ Γ` and `M : FinTM Γ` with
`M.ComputesFunInTimeVia e f T`, produce `M' : FinTM Bool` with
`M'.k = M.k` and `M'.ComputesFunInTime f (fun n => c * (T n + 1))`.

The audited construction (phase-2 findings):

- **Fixed-width blocks**: choose `L` with `2^L ≥ |Γ| + 1` (or any fixed-width
  scheme); each simulated `Option Γ` cell becomes an `L`-cell block of
  `Option Bool` on the corresponding work tape (`k` is preserved — block per
  tape, no merging).
- **All-blank block = logical blank** (audit-corrected): the encoding of the
  simulated blank is the block of `L` physical blanks, so untouched tape
  regions are automatically correctly encoded — do not use a nonblank code
  for blank.
- **Macro-step**: to simulate one step of `M`, sweep each work-tape block
  (`L` steps) to read the block into the state, compute `M`'s transition,
  sweep back writing the new block, and reposition to the neighboring block
  per the simulated move (`O(L)` steps in total per tape, `L` fixed) —
  constant factor, hence `c * (T n + 1)`.
- **Input tape**: `M` reads symbols of the form `some (e b)` (its inputs are
  `x.map e`); `M'` reads `some b` on the raw input `x` and translates through
  `e` inside its transition — no blocks on the read-only input tape.
  Boundary blanks pass through as blanks.
- **Output**: on the hypothesis inputs, `M`'s completed output is
  `(f x).map e`, and output is append-only, so every emitted symbol is in
  `e`'s image (`Turing.MultiTapeTM.output_prefix`); `M'` emits the
  `e`-preimage (decidable since `DecidableEq Γ` and `e` is injective). For
  totality of the machine define an arbitrary emission on non-image symbols;
  the correctness proof never meets that case — but say so explicitly in the
  invariant.
- `k = 0` degenerates to state-and-input-only translation — handle it first
  and separately if that is simpler.

## Out-of-scope sorries you will see (leave every one untouched)

`computesFunInTime_comp`, `exists_comp_partial` (Composition.lean);
`one_work_tape` (SingleTape.lean); `oblivious_of_mem_DTIME` (Oblivious.lean);
`exists_effectiveMachineCode` (Encoding.lean); `universal`, `timed_universal`
(Universal.lean). After your batch, exactly these 7 sorry warnings remain.

## REPORT.md checklist

- [ ] Targets filled (2), each with how the proof relates to its (corrected)
      sketch.
- [ ] New private declarations listed, for audit restatement.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Docstring appendices — or "none".
- [ ] Verification evidence: final sweep log attached, axiom log attached,
      zero `error:` lines, the exact 7 remaining sorry warnings.
- [ ] Diff touches only the two owned files.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `update_noteq`); core `Nat.pow_pos`;
  `dite_eq_right/left` don't exist — `split <;> simp <;> omega`; after
  `cases hs : cfg.state` insert `dsimp only`; avoid bare `simp` against
  folded hypotheses (`initCfg` is `@[simp]`) — targeted `simp only`; `ring`
  needs `import Mathlib.Tactic.Ring`; `omega` can't see `Fin.val ⟨e, h⟩` or
  un-beta-reduced lambdas — normalize first; SignType names:
  `SignType.coe_one`, `neg_eq_neg_one`, `coe_neg_one`, `pos_eq_one`,
  `zero_eq_zero`; `moveInputPos_zero`, `moveInputPos_pos_of_ne_right`,
  `moveInputPos_neg_of_ne_left`, `moveInputPos_neg_val` (Simulation.lean).
- Work tapes are ℤ-indexed `Option Γ'` functions updated via
  `Function.update`; blanks are `none`; `Cfg.ext` / `Cfg.ext_zero_tapes`
  prove configuration equality field by field.
- `(x.map e).length = x.length` (`List.length_map`) reconciles the `Via`
  bound's length with the raw input's.
- Proved in-repo exemplars: `StateRenaming.lean` (coordinate-transport
  commutation), `counterTM`'s `counterTape` shape function
  (TimeConstructible.lean), `condTM`'s phase machinery (Composition.lean),
  the `Simulation.lean` lockstep suites.
