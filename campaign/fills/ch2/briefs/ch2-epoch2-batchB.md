# Ch2 fill campaign — Epoch 2, Batch B: the Theorem-2.6 compilations

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2-B`), record
  the base commit hash in `REPORT.md`.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch2-e2-B.zip` with `REPORT.md`, the full modified source file, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

You are filling the two directions of [AB09, Theorem 2.6] — the equivalence
of the verifier-certificate and nondeterministic-machine definitions of
`NP` — plus their one-line assembly. Statement layer audited (four closed
gates); epoch 1 closed in one round and proved the NDTM run calculus your
proofs will consume (`runWith` algebra, `AcceptsWithin.mono`,
`HaltsWithin.mono`, `toNDTM_runWith`, all in the tree, proved). The two
directions are mirror-image machine constructions: ⊆ simulates a **fixed**
NDTM deterministically with the choice word read from the certificate
suffix; ⊇ guesses the certificate bitwise and runs the verifier machine
relocated-and-captured. Both docstring sketches name every obligation; the
phase-2 audit's invariant tables below are binding.

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/ClassNP/Nondeterminism.lean` — targets, in order:
  1. `ntime_poly_subset_NP` (line 101, 10 pts)
  2. `NP_subset_iUnion_NTIME` (line 132, 8 pts)
  3. `NP_eq_iUnion_NTIME` (line 142, 1 pt — antisymmetry of 1 and 2)

  The padding cluster in the same file (`ntime_expPow_subset_NEXP`,
  `NEXP_subset_iUnion_NTIME`, `NEXP_eq_iUnion_NTIME`,
  `EXP_eq_NEXP_of_P_eq_NP`, `P_ne_NP_of_EXP_ne_NEXP`) is **epoch 3 — not
  yours**.

## Environment and verification

As the epoch-1 briefs: pinned toolchain, `lake exe cache get` once,
**never `lake build`**; bootstrap the 53-module order list once; iterate
`bash scripts/lean_check_tree.sh TCSlib/Complexity/ClassNP/Nondeterminism`
plus the later modules; final full sweep with zero `error:` lines.
**Axiom prints** for the three targets: **at most**
`[propext, Classical.choice, Quot.sound]` (subsets fine — disposition D1);
`sorryAx` must not appear — this batch has **no sanctioned admitted
dependency** (everything cited by the sketches is proved: `mem_P_iff`,
`mem_P_of_dtime_le`, `succ_pow_le`, the epoch-1 run calculus).

## Ground rules (binding)

Identical to epoch 1 (`workflow.md` §4, full force): exclusive ownership of
the one file; helpers `private`, all new declarations listed; statement
freeze with escalation over alteration; no out-of-scope sorries touched;
docstrings stay; precise imports. **Continuation budget**: 19 points
combined; if exhausted, partial delivery per the B2 precedent with the
frontier stated precisely (any `sorry` in a partial delivery listed, allowed
only there).

## Binding rule inherited from the phase-2 audit

**No untimed composition and no bare computability substitutions**
(`audits/ch2-phase2-findings.md`, note 3): every machine step of both
compilations carries its explicit time bound through the timed interfaces;
nothing may route through `exists_comp_partial` or an untimed
`Computes`-level argument.

## Inherited invariant tables (verbatim; binding on the fill)

From `audits/ch2-phase2-findings.md`, for the ⊆-direction simulation
(`ntime_poly_subset_NP`, obligation (iii)–(v)):

> | Component | Required behavior and adversarial check |
> |---|---|
> | Source input | With shifted source head position `p`, read blank at `p=0,n+1`, and otherwise read `x[p−1]`. Update `p` by the source `moveInputPos`, clamping to `0,…,n+1`. A move to the right boundary must not expose the first certificate bit. Repeated outward moves must remain clamped, so a later inward move returns correctly. Initial position is 1 even when `x=[]`. |
> | Choice tape | Before source step number `j`, use exactly the certificate bit at position `j`. Administrative simulator transitions do not consume source choices. A halted source remains unchanged; either finishing the clock with absorbed steps or stopping early preserves the verdict. |
> | Source state and tapes | Store the fixed machine's finite state in finite control and keep its work tapes separate from counters, choice storage, and buffers. Simulation bookkeeping must not alter the represented source configuration. |
> | Output | Suppress physical output during simulation. Capture every source emission, including an emission on the halting transition, before testing the final buffer. Emit exactly one verifier decision bit. A halted output `[true,false]`, `[]`, or `[false]` rejects; a live output `[true]` also rejects. |

And for the ⊇-direction (`NP_subset_iUnion_NTIME`), the audit's
**adversarial reconstruction: certificates to choice words** — its five
steps are the binding branch-correspondence contract:

> 1. Compute the input length and the explicit `Q(n)`; initialize the guess
>    countdown. At each guess-writing transition, the current choice bit is
>    written as the next certificate bit. All intervening transitions ignore
>    their choice bit. The countdown and phase control are separate from
>    guessed data, so the times of the guess-writing transitions depend on
>    the input length, not their values.
> 2. For every `u` of length exactly `Q(n)`, assign its successive bits to
>    those guess-writing positions of a branch word and set unused choices
>    arbitrarily. This realizes `u`. Conversely, every sufficiently long
>    branch word yields exactly one such `u`, because precisely `Q(n)`
>    writes occur. Thus the construction has both witness coverage and
>    witness extraction; it does not incorrectly equate the first `Q(n)`
>    physical choices with the certificate. If `C=0`, there are no
>    guess-writing positions and the sole certificate is `[]`.
> 3. Assemble `x++u` and start the verifier from its proper initial
>    configuration with blank simulated work tapes, empty captured output,
>    and virtual input head 1. Its virtual read-only input is the assembly
>    tape, with the corresponding length's boundary guard and clamping. The
>    two NDTM tables coincide throughout this simulation. Capture output and
>    emit a single final verdict. The deterministic verifier's totality
>    holds for every assembled string, so every branch terminates, whether
>    or not `x∈L`.
> 4. A branch accepts exactly when its extracted certificate satisfies
>    `x++u∈V`; existential branch acceptance is therefore equivalent to
>    membership in `L`. Extend a terminated branch to the declared common
>    budget by absorption. Conversely, every branch at that budget has
>    completed the construction and yields a legitimate certificate. The
>    later verifier phase may have certificate-dependent running time; the
>    needed assertion is a **common upper bound**, not equal actual halting
>    times.
> 5. For fixed positive constants `K,r` absorbing arithmetic, assembly, and
>    simulation costs, a bound of the form `H(n) ≤ K(n+Q(n)+1)^r` suffices.
>    It can incorporate any fixed-degree bookkeeping cost. Put
>    `e = r·max(1,c)`. Then, at every `n`,
>    `n+Q(n)+1 ≤ (C+1)(n+1)^{max(1,c)}` and
>    `H(n) ≤ K(C+1)^r (n+1)^e ≤ K(C+1)^r 2^e (n^e+1)`.

Your `REPORT.md` must map the table rows and the five steps to the lemmas
discharging them.

## Out-of-scope sorries you will see (leave untouched)

The padding cluster in your own file (epoch 3, listed above);
`NP_subset_EXP` (2A, concurrent); `mem_NP_iff_exists_length_le` and the
HALT pair (2C); the `TMSAT.lean` four (2D); everything in E3/E4.

## REPORT.md checklist

- [ ] Three targets filled in order; the invariant-table and five-step
      mappings.
- [ ] Base hash recorded; all new declarations listed.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail + axiom prints (at most the triple; no
      `sorryAx`).
- [ ] Diff touches only `Nondeterminism.lean`.

## Known pitfalls at this pin

The epoch-1 list carries over verbatim (see
`briefs/ch2-epoch1-batchB.md` §pitfalls, same pin), plus:
- The two NDTM transition tables coincide outside the guessing phase —
  make that a definitional fact of your construction, not a lemma fought
  after the fact.
- `Turing.FinNDTM.AcceptsWithin.mono` (proved, epoch 1) does the final
  budget-padding; don't re-derive absorption.
- Phase boundaries must be input-length-functions only; any
  value-dependence of timing breaks witness extraction (step 2).
