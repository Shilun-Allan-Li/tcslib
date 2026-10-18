# Ch2 fill campaign — Epoch 3, Batch B: the SAT track

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e3-B`). The
  required base is `b55180a8bb38b94427e75e63630aa6eab5fd6e95`; record it in
  `REPORT.md` and never rebase onto anything else.
- **Delivery is by zip, not PR or push**: `fill-ch2-e3-B.zip`, **flat**
  (`SHA256SUMS` at the root), with `REPORT.md`, the full modified source,
  the `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

Epochs 1 and 2 are complete and audited (38/59 proved; gate records in
`audits/ch2-epoch2-resolutions.md`). Your batch is the **SAT machine
track** [AB09, Theorem 2.10 membership + Lemma 2.14]: two `(1,1)` NP
memberships and the clause-splitting reduction. The formula layer is fully
proved (E1 batch 1D): `Std.Sat.CNF.parse`/`serialize`/`decode`,
`decode_serialize`, `numVars_decode_le`, `eval_congr_of_lt_numVars` are
citable theorems. The audited machine-construction library
(`Build/{Convention,Wrappers,Loop,Primitives}`, two closed gates) is the
expected construction vocabulary: split recovery (`splitSolve` at the
`(C, c)` the statement forces), capture/isolation (`capture_run`), loops
(`exists_loopCfgTM`/`exists_loopFindTM`), and the primitive catalog. The
epoch-2 fills (`NP.lean`, `TMSAT.lean`) are proved in-repo precedents for
odd-split recovery, marker/strip parsing, and buffered verdicts.

## Owned file and targets (in order)

- `TCSlib/Complexity/ClassNP/SAT.lean` — targets:
  1. `SAT_mem_NP` (9 pts): certificate parameters `(1, 1)`, length exactly
     `n + 1`; verifier obligations per the binding docstring sketch —
     unique odd split (**rejecting explicitly on even `m`**), the LL(1)
     parsing machine for `Std.Sat.CNF.parse` (on parse failure continue
     with the fallback, i.e. accept — the empty formula evaluates `true`),
     the streaming evaluation machine with unary-index assignment walks,
     the buffered verdict.
  2. `SAT3_mem_NP` (3 pts): the same verifier with one more pass — the
     width-≤-3 scan after parsing, before evaluating; the fallback has no
     clauses and passes the width check (non-well-formed strings stay on
     the member side, as `SAT3` requires).
  3. `SAT_reducible_SAT3` (12 pts): the formula-level transform `t`
     (clause chains with fresh variables from `numVars` upward),
     equisatisfiability by induction exactly as the docstring's two
     directions, then the string-level
     `f = serialize ∘ t ∘ decode` with `PolyTimeComputable f` by the named
     machine obligations (shared parsing machine, streaming transform,
     serializer), and correctness **for every string** (the fallback `[]`
     is fixed by `t`; both sides true).

## Environment and verification

- Pinned toolchain (Lean 4.25.0, `cdd38ac5115b`; mathlib `029db123ddaa`).
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap the **57-module** order
  (`scripts/ab_ch1_module_order.txt` via `scripts/lean_check_tree.sh`);
  iterate the owned module plus later modules; final full fresh sweep,
  zero `error:` lines.
- **Axiom prints**: all three targets at most
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` — **zero
  sanctioned admitted dependencies**. Kernel-traversal template:
  `audits/programs/ch2-e2-ClosureAxioms.lean`.

## Ground rules (binding)

1. **File ownership.** Only `SAT.lean`; only the three targets plus
   `private` helpers; list every new declaration.
2. **Statement freeze** absolute; escalation over alteration, always.
3. In-file and in-repo proved material is citable, never modifiable.
4. Docstrings stay (append-only, flagged). Precise imports; keep
   `set_option` headers.
5. **Continuation budget anticipated** (24 points; the campaign partition
   plans for it): if exhausted, deliver a partial flat zip; `REPORT.md`
   states proved/admitted/frontier exactly (admissions allowed **only** in
   a partial delivery, each listed); the maintainer issues a continuation
   brief. Prefer completing targets 1–2 cleanly over starting 3.

## Inherited audit contract (verbatim; binding on the fill)

From `audits/ch2-phase3-findings.md` (via the phase-3 resolutions):

> For an input `x` of length `n`, `numVars(decode x) ≤ n`. A certificate of
> length `n+1` therefore contains every relevant assignment bit.
> Restricting a satisfying total assignment supplies such a certificate;
> conversely `u.getD · false` supplies a total assignment from one. The
> verifier's total length is `2n+1`, so it rejects even lengths and
> recovers the unique split on odd lengths, including length one. **A
> complete syntax pass must precede rejection on a failed clause or
> excessive width**: `[1,0,0,1]` shows why rejecting an unsatisfiable
> parsed prefix before discovering trailing garbage would be wrong. The
> stated parsing-then-evaluation order supports this requirement. Unary
> walks, width checks, and final buffered verdicts have polynomial cost.
> Both `(1,1)` NP witnesses are valid.

And the parser grammar conventions (same record):

> | `parseClause fuel x` | A leading zero returns the empty clause and suffix, even at fuel zero. Otherwise a leading one requires positive fuel, one literal parse, and recursive parsing at fuel minus one. |
> | `parseClauses fuel x` | A leading zero returns the empty formula and suffix, even at fuel zero. A leading one requires positive fuel; parse the clause body and remaining formula, each with fuel minus one, threading the returned suffix. |

Your machine's parser must realize exactly this grammar; the
parsing-then-evaluation order is binding on all three targets (target 2's
width scan also runs only after a complete parse).

## Out-of-scope sorries you will see (leave untouched)

The padding cluster and `EXP_subset_NEXP` (3A, concurrent, in
`Nondeterminism.lean`/`EXP.lean`); `CookLevin/Snapshot.lean` (3C);
`Tautology.lean` (3D and 4B); `CookLevin/Hardness.lean` (E4). On
completion `SAT.lean` is admission-free.

## REPORT.md checklist

- [ ] Targets filled in order (or the frontier exact); the verifier
      obligations and the equisatisfiability induction mapped to
      discharging lemmas; the complete-syntax-pass-first discipline and
      even-rejection called out explicitly.
- [ ] Base hash; new privates listed; final file size.
- [ ] Axiom prints (standard triple at most, roots empty); final sweep log
      tail; diff touches only `SAT.lean`; archive flat.
- [ ] Requested shared lemmas / escalations — or "none".

## Known pitfalls at this pin (hard-won)

- The E2 lists carry over (`briefs/ch2-epoch2-batch{C,D}.md`): odd-split
  recovery and marker conventions are proved precedents in `NP.lean`
  (`mem_NP_iff_exists_length_le`) and `TMSAT.lean` (the `(1,1)` odd split
  — the round-2 audit's own prediction); study them before building.
- `Function.update_of_ne`; `dsimp only` after `cases hs : cfg.state`;
  `omega` needs beta-reduced non-`Fin` goals; `moveInputPos` clamps;
  buffered output is the standing isolation obligation — the real output
  stays empty until the single final verdict.
- The fallback convention differs per language: `SAT`'s fallback (empty
  formula) is satisfiable — parse failure **accepts**; keep every
  equivalence quantified over all strings, not just well-formed ones.
- Fresh-variable arithmetic: freshness is by construction from `numVars`
  upward; `eval_congr_of_lt_numVars` is the citable bound — don't
  re-derive mentioned-variable reasoning.
