# §12 fill campaign — Epoch F2, Batch A: the catalog space annotations (`Build/Catalog.lean`, Part 2)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/s12-f2-A`),
  record the base commit hash you branched from in `REPORT.md`, and never
  rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-s12-f2-A.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

You are filling the **final 19 statements of the §12 routine layer** —
the Part-2 space annotations of the catalog. The statement gate closed in
three audited rounds and epoch F1 closed in one
(`audits/routine-infra-resolutions.md`, `audits/routine-f1-resolutions.md`
— read both, plus the three round reports they cite). Your file already
contains epoch F1's completed Part-1 fills, whose `private` helpers are
**yours to use**: `catalogCfg`/`catalogTrace` (full-configuration routine
traces), the per-routine invariants, and the seven `catalog_redirect*`
copies (do **not** instead add the queued public projection to
`Wrappers.lean` — that file is not yours). Each target re-opens an
**existing proved witness** from `Build/Primitives.lean`,
`Build/Wrappers.lean`, or `Build/Loop.lean` and adds its space clause —
except one, which commissions a new machine (the summit, last below).

## Owned file (modify this and nothing else)

`TCSlib/Complexity/TuringMachine/Build/Catalog.lean` — the 19 remaining
sorried theorems, in this risk order:

**(i) Same-witness, constant space (7):** `computesFunInTime_id_spaceUsed`,
`_const_`, `_prepend_`, `_pairEncodeFixed_`, `_pairValid_`, `_pairDup_`,
`_incFixed_` — the original witnesses have zero work tapes (or finite
control only); space is exactly `0`/constant at all times.

**(ii) Same-witness, linear space (3):** `_pairFst_`, `_pairSnd_`,
`_pairConcat_` — the shared `pairExtractTM` prefix buffer is linear;
malformed inputs leave at most a partial linear buffer.

**(iii) Case-split rows (2):** `_polyUnary_` (linear banks for `e ≥ 1`;
the fixed emission chain at `e = 0`), `_polyBits_` — **the `C = 0` and
`e = 0` cases take the constant-output witness family; the buffered unary
route is valid only for `C > 0, e > 0`, where `n + 1 ≤ C(n+1)^e`**
(statement-round finding R5, binding — the old generator's unary banks
defeat a constant bound at `C = 0`).

**(iv) Constructions over received parts (4):** `_lengthBits_` (the
**direct variable-width counter**: return the head after each carry,
`Σ carries ≤ n`, width `O(Nat.size n + 1)` — the imported sharp witness
of `timeConstructible_id` is explicitly **not** relied on),
`_pairLenCheck_` (linear parser banks + captured unary output
`≤ C(n+1)^e`), `_stripLast_` (guard and raw banks each linear; the
quadratic time clause is slack — no replay story), `_splitSolve_` (round
returns confine reused spans; fuel and accepted buffer inside degree
`e + 1`).

**(v) The wrapper and loop rows (2):** `computesFunInTime_cond_spaceUsed`
(W3: decider bank + selected branch bank + idle origins, disjoint;
`sD n + max(s₁ n)(s₂ n) + c`) and `exists_loopTM_spaceUsed` (L: the
six-step ledger quoted below is binding).

**(vi) The summit (1):** `computesFunInTime_pairMapSnd_spaceUsed` — **the
only new machine of the §12 fill**: the commissioned forwarding
controller. The received `pairMapTM` witness is **refuted** for this
bound (its capture tape visits `|g b| + 1` cells — statement-round
finding R4); your sketch's controller instead validates/buffers the pair,
emits the encoded first component, then simulates the payload on the
buffered second component **forwarding its output** (emissions to
physical output, never to a work bank), leaving payload work-head
trajectories unchanged — coefficient `1` on `Sg` plus linear
administration. Continuation brief anticipated if the budget exhausts
here.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (65 modules; it predates six facade-wired modules — if the facade check
  below complains, check `Build/Embed`, `Build/Seam`, `NDCodes`,
  `Formulas/QBF`, `Formulas/QBFEncoding` individually first), then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Catalog`.
- Iterate on your file per edit. Final: your file with **zero `error:`
  lines and ZERO `sorry` warnings** — this delivery completes the file —
  then `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine`.
- **Axiom prints**: `#print axioms Turing.<name>` (and
  `Turing.FinTM.<name>` where applicable) for all 19 filled theorems on
  the final fresh tree; each footprint **at most**
  `[propext, Classical.choice, Quot.sound]` — proper subsets fine — and
  no `sorryAx`: no sanctioned admitted dependency.

## Ground rules (binding)

1. **File ownership.** Only `Build/Catalog.lean`, and only the 19 targets'
   proofs plus `private` helpers. The file is large (1851 lines) by
   recorded justification — do **not** split it. Shared wishes (including
   anything about the queued `Wrappers.lean` projection) go under
   "Requested shared lemmas" in `REPORT.md` with a `private` local copy.
   List every new declaration — the epoch audit blind-restates them.
2. **Statement freeze.** No renames, re-signatures, restatements, or
   attribution edits anywhere — including epoch F1's completed proofs.
   Docstring sketch appendices allowed, flagged.
3. **Escalation** on anything unprovable as stated: stop, record the
   obstruction, deliver what exists.
4. No touching anything outside your 19 targets and your new helpers.
5. Docstrings stay. 6. Precise imports; keep `set_option` headers.
7. **Continuation budget**: 19 targets, one summit. On exhaustion,
   deliver a partial zip whose `REPORT.md` states what is proved, which
   `private` helpers remain `sorry` (allowed **only** in a partial
   delivery, each listed), and the frontier — the maintainer issues a
   continuation brief. Fill in the risk order above so a partial delivery
   retires maximal risk.

## Inherited audit contract (verbatim; binding on the fill)

From `audits/routine-infra-r2-findings.md`, the R4 ledger for the summit
(the target's hypotheses name `Sg`, `hgs`, `hSg`):

> The payload work bank starts blank with heads at zero; administrative
> stages leave those heads stationary. During simulation its head
> positions are exactly source positions, possibly repeated during
> controller microsteps. After payload halt, the host freezes those heads.
> Hence the payload bank's contribution is at most `Sg |b|`, with
> coefficient **one**, at every horizon. For fixed implementation
> constants `A,B`:
> `space_host ≤ Sg(|b|) + A(n+1) ≤ Sg(n) + A(n+1)`,
> `time_host ≤ B(n+1+Tg(|b|)) ≤ B(n+1+Tg(n))`.
> Choose the theorem's single `c ≥ max(A,B)`. Invalid encodings halt
> after validation with empty output and the same administrative bounds.
> Forwarded output never occupies a work tape [...]. No inherited time
> clause or hypothesis was weakened to obtain this repair.
> [...] The virtual-input controller needs a fixed number of microsteps
> per source step to preserve both input boundary clamps, including empty
> `b`.

From `audits/routine-infra-findings.md`, answer 5, the loop-row ledger
(binding for `exists_loopTM_spaceUsed`; `ℓ = |(Nat.bits (R n))|`):

> 1. `hstart` and `hround` give the actual startup/return/halt times at
>    most `T n`. Every prefix used by the host lies inside one of those
>    windows, so `hstartSpace` and `hroundSpace` apply. [...]
> 2. Each body phase starts with all work heads at 0. A unit-step integer
>    walk that visits at most `S n` cells stays within `[-S n, S n]`;
>    therefore the union over **arbitrarily many rounds** on each fixed
>    body tape is still contained in that interval. [...] no factor `R n`.
> 3. `hFspace` bounds the fuel machine's own bank by `S n` throughout its
>    execution. [...]
> 4. `hF` starts from empty output and permits at most one emitted bit
>    per step. Hence `ℓ ≤ T n`. The fuel capture tape and copied
>    countdown tape each need only the interval from the left overshoot
>    to position `ℓ`, plus fixed controller allowances. Debit changes
>    bits inside the same fixed width [...].
> 5. Startup and rejecting body rounds end with empty output, so
>    append-only output forces them to emit nothing throughout. An
>    accepting round ends with exactly `[true]` [...]. No per-round
>    output log accumulates.
> 6. The stationary one-cell flag and finitely many boundary allowances
>    add a machine constant. Thus one can choose a constant `c` [...]
>    with `host space ≤ c(S n + ℓ + 1) ≤ c(S n + T n + 1)`.

Also binding, from the same loop: the W3 `cond` row keeps the decider
bank, the selected branch bank, and idle branch-origin cells disjoint —
"only one output bit is captured from the decider. Input rewind is
uncharged input-head motion, and no monotonicity is needed because both
branches see the same input." For every same-witness row, the round-1
report's Part-2 assessment table (one row per target, "Supported, same
witness family" with the decisive sentence) is the per-target route —
quote the relevant row in your `REPORT.md` against each fill.

## Out-of-scope sorries you will see (leave untouched)

None in your file — your delivery makes `Catalog.lean` zero-sorry.
Elsewhere: the chapter-3/4 statement surfaces (`Diagonalization/*`,
`ClassOracle/*`, `SpaceComplexity/*`, `ClassPSPACE/*`, `Formulas/QBF*`,
`TuringMachine/NDCodes.lean`, `TuringMachine/Oracle*.lean`,
`TuringMachine/NondeterministicSpace.lean`) — never touch them.

## REPORT.md checklist

- [ ] 19/19 filled (or the partial frontier per ground rule 7, in risk
      order); `Catalog.lean` zero-sorry (or the exact remaining list).
- [ ] Base commit hash; every new `private` declaration listed; the
      summit controller's stage structure (validate/buffer → emit prefix
      → forward payload) identified by lemma.
- [ ] Per-target: the matching audit-row quoted (round-1 Part-2 table /
      R4 / R5 / answer 5) with your proved bound beside it.
- [ ] Requested shared lemmas — or "none". Escalations — or "none".
- [ ] Final sweep log tail (zero `error:`, zero `sorry`) + facade check +
      19 axiom prints (at most the standard triple; no `sorryAx`).
- [ ] Diff touches only `Build/Catalog.lean`.

## Known pitfalls at this pin (hard-won)

- The F1 helpers are in-file and `private` — use them (`catalogTrace`'s
  full-configuration traces; `catalog_redirect_run` for redirected
  payloads), but do not generalize their statements in place; add new
  privates instead.
- The existential targets quantify the witness: you may pick a
  **different machine** than the original time-row's witness where the
  sketch says so (R5's constant family; the summit's new controller) —
  the time clause must still be proved for your witness, verbatim.
- `pairExtractTM`'s buffer holds at most the first component — its
  linear bound needs the pair grammar's doubled-prefix length arithmetic
  (`Encoding.lean`'s `pairEncode` length lemmas).
- Space is all-time (`spaceUsed` at every `t ≤` the horizon, origins
  included): stationary suffixes freeze visited sets — prove trajectory
  containment, then take cardinalities (`Int.card_Icc`); never argue
  from bounds without the trajectory (the statement-round R6 lesson).
- `Function.update_of_ne` (not `update_noteq`); after
  `cases hs : cfg.state`, `dsimp only`; avoid bare `simp` with folded
  forms; `omega` wants beta-reduced, non-`Fin`-projection goals.
- The loop host's tapes are fixed banks — reuse intervals, never fresh
  offsets per round (answer 5, step 2, is your invariant's shape).
