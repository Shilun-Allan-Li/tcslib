# Fill campaign — Epoch 3, Batch A: the concrete effective scheme

## Context

You are filling one Lean 4 proof in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1:
`Turing.exists_effectiveMachineCode` — a concrete machine-representation
scheme exists, together with an in-model machine (the *canonizer*) computing
the fixed serialization of the decoded machine. Seventeen of the 21 audited
sorries are already proved; this is one of the last four. Its closure makes
every theorem that is currently "admission-free per supplied scheme" —
notably [AB09, Theorem 1.10] — instantiable at a concrete scheme.

The target has **two halves of very different character**:

1. **A Lean-level scheme** (pure functions and proofs, no machines):
   `encode := CodeTM.serialize`, a total parser `decode : List Bool → CodeTM`,
   and the padded round-trip law `decode_encode_pad`.
2. **The canonizer**: a `FinTM Bool` computing `fun α => (decode α).serialize`
   within some time bound `canonizerTime` — a genuine machine construction.

A decisive simplification for half 2, straight from the structure's fields:
`canonizerTime` is an **arbitrary** function — no monotonicity, positivity, or
polynomial growth is demanded (the phase-3 round-2 audit, finding 5, confirmed
this suffices for every downstream use). So you may build a machine that
computes `serialize ∘ decode` **totally with no time accounting at all**
(via the untimed guarded combinators), and then obtain the bound by
`Turing.FinTM.Computes.exists_computesFunInTime` (finiteness of inputs per
length). Chasing explicit step counts through the parser is legitimate but
entirely optional.

## Repository, base, deliverable (zip — there is no PR step)

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`, branch
  `complexity/arora-barak-ch1`. **Base commit: `71721842`** — verify with
  `git rev-parse HEAD` after checkout. Branch `fill/epoch3-A`; do not attempt
  to push or open a PR.
- **Deliverable: a single zip archive** containing, at minimum:
  1. `REPORT.md` — the full report per the checklist below.
  2. The complete modified source file(s) at their repository paths.
  3. `epoch3-A.patch` — `git format-patch 71721842 --stdout > epoch3-A.patch`.
  4. `epoch3-A.bundle` — `git bundle create epoch3-A.bundle 71721842..fill/epoch3-A`.
  5. `final-sweep.log` — complete output of the final full sweep.
  6. `axioms.log` — `#print axioms Turing.exists_effectiveMachineCode` (and,
     as regression checks, `Complexity.UC_not_computable` and
     `Turing.pairEncode_injective`), via a scratch file outside the
     repository with the check script's `LEAN_PATH`. Expected:
     `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**.
  7. `SHA256SUMS` — a hash manifest of every file in the zip.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5,
  `audits/phase3-reaudit-findings.md` **Argument A** (the parse grammar:
  unique parsing, prefix-freeness of complete serializations — your `decode`
  formalizes exactly this grammar) and its finding 8 (the **short-circuit**
  requirement), `audits/epoch2-resolutions.md` (design obligations), and the
  target's docstring sketch in `Encoding.lean` (it is detailed and binding).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Encoding.lean`

All helpers `private`, defined above the target. If the file approaches ~1000
lines (policy §1), record a split escalation in `REPORT.md` rather than
splitting shared structure yourself. Needed lemmas belonging in shared files:
`private` copy + "Requested shared lemmas" entry.

## Environment and verification

- `lake exe cache get` once; **never `lake build`**. The repo's
  `.claude/CLAUDE.md` LeanInfoView rule presumes a local session; the
  maintainer-designated path is `scripts/lean_check_tree.sh` (strengthened:
  fails on nonzero `lean` exit, `error:` diagnostics, or missing fresh
  `.olean`). Sweep:
  `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )`
  (25 modules). Pass = exit 0, zero `error:` lines, sorry warnings only at
  the out-of-scope list below.

## Ground rules (binding)

1. **File ownership**: only `Encoding.lean`; every new declaration listed in
   `REPORT.md` for audit restatement. 2. **Statement freeze**: no change to
   any existing declaration (docstring appendices allowed, flagged).
   3. **Escalation** over statement edits, always. 4. No other sorry touched.
   5. Sketches stay. 6. Precise imports; keep `set_option` headers.

## The target, and a suggested route

`theorem exists_effectiveMachineCode : Nonempty EffectiveMachineCode`

**Half 1 — the scheme.** Follow the docstring sketch and Argument A's grammar:

- `decode` parses `CodeTM.serialize`'s format: the `pairEncode` doubled-bit
  region for `Nat.bits numStates` (the file's private `pairDecode` is the
  aligned-pair parser — reuse or extend it), then the self-delimiting unary
  initial state, then exactly `9 * (numStates + 1)` fixed-format records
  (the `Serialize` section's field dictionaries: `signBits`, `optBoolBits`,
  `optOptBoolBits`, `unaryFin`, `optStateBits`, `actionBits`).
- **Totality**: any malformation yields a canonical trivial machine.
- **Short-circuit** (phase-3 round-2 finding 8, binding): the parser must
  reject a state count whose minimum table length exceeds the remaining
  input *without* enumerating the missing records — as a Lean function this
  means recursion structured on the input list (or a length check up front),
  never on the declared `numStates`; termination will force this anyway.
- **Padding law**: a complete serialization determines its own length
  (Argument A's prefix-freeness); the parser ignores a trailing all-`true`
  suffix. Prove `decode_encode_pad : ∀ M m, decode (serialize M ++
  List.replicate m true) = M` — expect this to be the bulk of half 1, by
  induction along the parse of each field (mirror how
  `pairDecode_pairEncode` is proved field by field).
- Watch the round-trip corner the audit flagged: `Nat.bits` is LSB-first with
  no redundant most-significant zeros, and `Nat.bits 0 = []` — the count
  region for a 1-state machine is empty (immediate separator).

**Half 2 — the canonizer.** The spec is
`canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime`.
Suggested assembly, using only proved API:

- On valid codes, `serialize ∘ decode` is *the identity up to removing the
  `true`-padding*; on invalid ones it is the constant trivial-machine
  serialization. You do **not** need a machine that literally re-serializes a
  parsed structure: a machine that (a) decides validity and locates the
  serialization's end (a single left-to-right scan tracking the parse state —
  the parse is finite-state except for the two unary fields and the record
  count, which live on work tapes as counters), (b) copies the valid prefix
  to the output, or (c) emits the fixed fallback string, is exactly
  `serialize ∘ decode`. Prove the machine's completed output equals
  `(decode α).serialize` by relating the same scan to the Lean parser.
- The proved combinators can carry the control flow:
  `Turing.FinTM.exists_cond` (branch on a decided predicate),
  `exists_comp_partial` / `computesFunInTime_comp` (Monotone bound needed for
  the timed one), `computesFunInTime_const` (the fallback), plus the
  `Simulation.lean` gadgets (emission chains, rewind, buffered layer) and the
  `Sweep.lean` zipper/transduction layer for scan invariants. Note
  `exists_cond`'s decider hypothesis is semantic (`D.Computes fun x => [p x]`)
  — your validity predicate can be exactly "the Lean parser succeeds".
- Once total correctness (`Computes`) is in hand, extract `canonizerTime` via
  `Computes.exists_computesFunInTime`. No properties of the bound are needed.
- **Do not appeal to `universal`** (it is sorry'd, and the epoch-2 audit
  recorded that no appeal is needed or appropriate).

## Out-of-scope sorries you will see (leave every one untouched)

`oblivious_of_mem_DTIME` (Oblivious.lean); `universal`, `timed_universal`
(Universal.lean). After your batch, exactly these 3 sorry warnings remain
(fewer if other epoch-3 batches merge first — your tree is judged at your
base).

## REPORT.md checklist

- [ ] Target filled; the parser grammar's relation to Argument A stated; the
      short-circuit mechanism described; which route half 2 took (explicit
      bound vs extracted bound).
- [ ] New private declarations listed, for audit restatement.
- [ ] Requested shared lemmas — or "none". Escalations — or "none".
      Docstring appendices — or "none".
- [ ] Verification evidence: final sweep log, axiom log, zero `error:` lines,
      the exact remaining sorry warnings.
- [ ] Diff touches only `Encoding.lean`.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne`; core `Nat.pow_pos`; no `dite_eq_right/left` —
  `split <;> simp <;> omega`; `dsimp only` after `cases hs : cfg.state`;
  targeted `simp only` against folded hypotheses (`initCfg` is `@[simp]`);
  `ring` needs `import Mathlib.Tactic.Ring`; normalize `Fin.val ⟨e,h⟩` and
  un-beta'd lambdas before `omega`; `Nat.find` under classical needs
  `classical` + explicit `(p := …)`; SignType names `SignType.coe_one`,
  `neg_eq_neg_one`, `coe_neg_one`, `pos_eq_one`, `zero_eq_zero`.
- `Nat.bits` interacts through `Nat.binaryRec'`, `Nat.bits_append_bit`,
  `Nat.bit0_bits`, `Nat.bit1_bits` (see `counterInc_bits` in
  `TimeConstructible.lean` for a worked pattern).
- Worked in-repo exemplars: `pairDecode`/`pairDecode_pairEncode` (your file —
  the parser-roundtrip pattern at small scale), `counterTM` (work-tape
  counter invariants), `condTM` and the buffered layer (control flow),
  `sweepFold`/`sweep_run` (scan-with-state invariants).
