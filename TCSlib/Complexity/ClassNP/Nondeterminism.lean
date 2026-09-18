/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassNP.EXP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic characterizations: Theorem 2.6, NEXP, and padding

[AB09, Theorem 2.6]: `NP = ⋃ c, NTIME (n^c)` — the certificate view and the
nondeterministic-machine view of `NP` coincide, with the accepting choice word as the
certificate and vice versa. This module states both directions as machine
compilations, the analogous `NTIME` characterization of the certificate-form
`Complexity.NEXP` ([AB09, §2.6.2] *defines* `NEXP` as `⋃ c, NTIME (2^(n^c))`; our
definition is [AB09, Exercise 2.27]'s verifier form, so the equality here is the
reconciliation of the two), and Theorem 2.22 (`EXP ≠ NEXP → P ≠ NP`, by padding).

## Design and deviations from [AB09]

* **The `NTIME` unions carry the same `+ 1` padding as `P`**: we write
  `⋃ c, NTIME (n^c + 1)` where [AB09] writes `⋃_{c ≥ 1} NTIME(n^c)`, for the reason
  recorded at `Complexity.P` — `n^c` vanishes at `n = 0` for `c ≥ 1` and no machine
  halts in zero steps, so the literal union is degenerate on the empty input; for
  `n ≥ 1` the two readings sandwich each other inside the constant slack. The
  exponential union `⋃ c, NTIME (2^(n^c))` needs no padding (`2^(n^c) ≥ 1`) and is
  [AB09]'s expression verbatim, matching `Complexity.EXP`.
* **Theorem 2.22 is proved through the certificate form** of `Complexity.NEXP` — the
  route of [AB09, Exercise 2.27], which needs no nondeterministic machines — rather
  than by padding an `NTIME` machine as in [AB09]'s proof of the theorem. With
  `Complexity.NEXP_eq_iUnion_NTIME` on the books the two renderings of the statement
  agree; the certificate route reuses the audited Exercise-2.1 interface instead of
  re-deriving NDTM compilations inside the padding argument.
* The choice-word/certificate correspondence is stated over the repaired explicit
  length formulas of `Complexity.NP`/`Complexity.NEXP` (phase-1 audit): each direction
  must land certificates of length **exactly** `C·(n+1)^c` (resp. `C·2^((n+1)^c)`),
  which the sketches arrange by padding choice words — harmless because halting is
  absorbing under every choice (`Turing.NDTM.runWith_of_halt`).

## Main results

* `Complexity.ntime_poly_subset_NP`, `Complexity.NP_subset_iUnion_NTIME`,
  `Complexity.NP_eq_iUnion_NTIME` — [AB09, Theorem 2.6], both directions and the
  equality.
* `Complexity.ntime_expPow_subset_NEXP`, `Complexity.NEXP_subset_iUnion_NTIME`,
  `Complexity.NEXP_eq_iUnion_NTIME` — the `NTIME` form of `NEXP` [AB09, §2.6.2,
  reconciled with Exercise 2.27].
* `Complexity.EXP_eq_NEXP_of_P_eq_NP`, `Complexity.P_ne_NP_of_EXP_ne_NEXP` —
  [AB09, Theorem 2.22], padding.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Theorem 2.6, pp. 41-42; §2.6.2, pp. 56-57;
  Theorem 2.22, p. 57; Exercises 2.1, 2.27.)
-/

namespace Complexity

open Turing

/-- **The choice word is a certificate** [AB09, Theorem 2.6, ⊆-direction of the
union]: every fixed-degree nondeterministic time class is contained in `NP`.

**Proof sketch.** Let `N` decide `L` within `T n = a·(n^c + 1)` (the `NTIME`
constant `a`). Certificate parameters: coefficient `2a`, degree `c`, so
`Q n = 2a·(n+1)^c ≥ T n` (as `n^c ≤ (n+1)^c` and `1 ≤ (n+1)^c`). The verifier
language is
`V = {x ++ u : |u| = Q |x| ∧ the run of N on x under choice word u is halted with output [true]}`
— a well-defined set, the split being unique since `n ↦ n + Q n` is strictly
increasing. Membership equivalence: forward, an accepting branch of length `T n` pads
with `false`-bits to length exactly `Q n`, still halted-with-`[true]` by
`Turing.NDTM.runWith_append` and `Turing.NDTM.runWith_of_halt`; backward, the length-
`T n` prefix of an accepting `u` is halted by the decider's `HaltsWithin`, absorption
gives it the same state and output, and `Turing.FinNDTM.AcceptsWithin` at `T n`
returns `x ∈ L`. `V ∈ P` by a deciding machine whose obligations are named for the
fill: (i) recover the unique split — search `n ≤ m` for `n + Q n = m`, **rejecting
explicitly when no solution exists** (the round-3 pattern of
`Complexity.mem_NP_iff_exists_length_le`), with a polynomial-evaluation machine for
the explicit formula `Q`; (ii) copy the choice suffix `u` to a dedicated work tape;
(iii) a clocked product simulation of the **fixed** machine `N`: `N`'s work tapes as
disjoint tape blocks (the `Simulation` lockstep gadgets are the precedent), `N`'s
state in finite control, and `N`'s input head as a binary position counter with the
**input-window guard** — `N` reads `x` only, so when the tracked position leaves the
window the simulator feeds the boundary blank instead of the symbol of `x ++ u` under
its own head, emulating the clamping of `Turing.moveInputPos` against the recovered
`n`; (iv) per simulated step, consume the next bit of the copied choice tape to select
between `N`'s two transition tables; (v) **output capture**: buffer `N`'s emissions on
a work tape and never write to the real output during simulation (the append-only
isolation obligation of the `Complexity.NP_subset_EXP` sketch;
`Turing.universalCaptureTM` is the in-repo precedent); (vi) the verdict — output
`[true]` iff the simulated run is halted with buffer exactly `[true]`, else `[false]`.
Budget: `Q n ≤ m` simulated steps at polynomial bookkeeping each, so polynomial in
`m`; conclude `V ∈ P` via `Complexity.mem_P_of_dtime_le` and `L ∈ NP` with
`(2a, c, V)`. -/
theorem ntime_poly_subset_NP (c : ℕ) : NTIME (fun n => n ^ c + 1) ⊆ NP := by
  sorry

/-- **Guess the certificate** [AB09, Theorem 2.6, ⊇-direction of the union]: `NP` is
contained in the union of the fixed-degree nondeterministic time classes.

**Proof sketch.** Let `L ∈ NP` with parameters `(C, c, V)` and, via
`Complexity.mem_P_iff`, a machine `M_V` deciding `V` within `A·(m+1)^d`. The NDTM, on
input `x` of length `n`: (i) evaluate `Q n = C·(n+1)^c` in binary (the shared
polynomial-evaluation obligation) and initialize a countdown; (ii) **guessing phase**
— write exactly `Q n` guessed bits onto a guess tape, `δ₀` writing `false` and `δ₁`
writing `true` on each nondeterministic write step ([AB09]'s concrete recipe, p. 42),
interleaved with deterministic countdown bookkeeping (the phase boundaries are
identical across branches: only the guessed content diverges, never the timing); (iii) assemble `x ++ u` on an assembly tape (copy the
input, append the guess tape); (iv) run `M_V` **with its input relocated to the
assembly tape** — the input-relocation obligation: the fixed machine `M_V`'s
input-tape reads are served from a work tape through a binary head-position counter
with the window guard, symmetric to the simulation obligation of
`Complexity.ntime_poly_subset_NP`; (v) capture `M_V`'s output in a buffer (isolation,
as always) and emit the verdict: `[true]` if the buffer is exactly `[true]`, else
`[false]`, then halt. Outside the guessing phase the two transition functions
coincide, so every choice word drives the same phases and every branch halts within
the deterministic budget — `HaltsWithin` holds on all inputs. Acceptance: branches of
the guessing phase realize exactly the strings `u` with `|u| = Q n`, and the verdict
is `[true]` precisely when `x ++ u ∈ V` (`M_V` decides `V`), so some branch accepts
iff `x ∈ L`; non-members' branches all emit `[false] ≠ [true]`. Padding accepting
branches to the exact budget is `Turing.FinNDTM.AcceptsWithin.mono`. Total time is
polynomial in `n` — guessing `Q n` steps with `O(log Q n)`-bit countdowns, assembly
`O(n + Q n)`, and the relocated `M_V` run `A·(n + Q n + 1)^d` with polynomial
per-step bookkeeping — hence at most `a'·(n^e + 1)` for a fixed degree `e` (normalize
with `Complexity.succ_pow_le`), landing `L` in the degree-`e` component. -/
theorem NP_subset_iUnion_NTIME : NP ⊆ ⋃ c : ℕ, NTIME fun n => n ^ c + 1 := by
  sorry

/-- **Theorem 2.6** [AB09]: `NP = ⋃ c, NTIME (n^c + 1)` — the verifier-certificate
definition and the nondeterministic-machine definition of `NP` coincide (with the
`+ 1` padding of the union recorded in the deviations list).

**Proof sketch.** Antisymmetry: `Complexity.NP_subset_iUnion_NTIME` one way;
`Set.iUnion_subset` with `Complexity.ntime_poly_subset_NP` at every degree the
other. -/
theorem NP_eq_iUnion_NTIME : NP = ⋃ c : ℕ, NTIME fun n => n ^ c + 1 := by
  sorry

/-- **Exponential choice words are exponential certificates**: every fixed-exponent
`NTIME (2^(n^c))` class is contained in the certificate-form `Complexity.NEXP`.

**Proof sketch.** The exponential analogue of `Complexity.ntime_poly_subset_NP`, same
verifier machine, different arithmetic. Let `N` decide `L` within `T n = a·2^(n^c)`
(if `a = 0` the budget is `0` and no decider exists — `Turing.NDTM.HaltsWithin` fails
on the empty choice word — so the case is vacuous). Certificate parameters: `C = a`,
degree `c`, length `Q n = a·2^((n+1)^c) ≥ T n`. The verifier language is the same
accepting-run language over the split `y = x ++ u`; `n ↦ n + Q n` is strictly
increasing (in `n` alone already), the split search over `n ≤ m` writes each candidate
`Q n` in binary — `(n+1)^c + O(log a)` bits, polynomial in `m` (the check recorded in
the `Complexity.EXP_subset_NEXP` sketch) — and **rejects explicitly when no solution
exists**. The simulation runs `|u| = Q n ≤ m` steps of the fixed machine `N` at
polynomial bookkeeping per step — polynomial in `m`, which is the whole point of
exponential padding: `V ∈ P`. Forward/backward certificate correspondence is verbatim
the polynomial case (pad with `false`-bits; truncate to the length-`T n` prefix and
absorb). -/
theorem ntime_expPow_subset_NEXP (c : ℕ) : NTIME (fun n => 2 ^ n ^ c) ⊆ NEXP := by
  sorry

/-- **Guess the exponential certificate**: the certificate-form `Complexity.NEXP` is
contained in the union of the fixed-exponent `NTIME (2^(n^c))` classes.

**Proof sketch.** The exponential analogue of `Complexity.NP_subset_iUnion_NTIME`.
Given `(C, c, V)` for `L` with `E n = C·2^((n+1)^c)` and `M_V` deciding `V` within
`A·(m+1)^d`: evaluate `E n` in binary (`(n+1)^c + O(log C)` bits; writing `2^((n+1)^c)`
is a `1` followed by `(n+1)^c` zeros, produced by a counter in time polynomial in
`(n+1)^c`); guess exactly `E n` bits (`δ₀`/`δ₁` write `false`/`true` on each
nondeterministic write step, deterministic countdown bookkeeping interleaved, phase
boundaries identical across branches); assemble
`x ++ u`; run the relocated, captured `M_V`; emit the verdict. Every branch is total
and the phases cost `O(E n)` guessing steps at `O((n+1)^c)`-bit countdown decrements,
plus `A·(n + E n + 1)^d` relocated verifier steps with polynomial bookkeeping — in all
at most `2^(n^e)` for a fixed `e` (say `e = c + d + 2`) once `n` exceeds a fixed
threshold, with the finitely many inputs of smaller lengths absorbed into `NTIME`'s
constant (their maximal halting time is a number; the truncation argument of
`Complexity.NTIME.mono` keeps the acceptance equivalence at the padded budget). Land
`L` in the exponent-`e` component. -/
theorem NEXP_subset_iUnion_NTIME : NEXP ⊆ ⋃ c : ℕ, NTIME fun n => 2 ^ n ^ c := by
  sorry

/-- **The `NTIME` form of `NEXP`** [AB09, §2.6.2 reconciled with Exercise 2.27]:
`NEXP = ⋃ c, NTIME (2^(n^c))`. [AB09] *defines* `NEXP` by the right-hand side;
`Complexity.NEXP` is Exercise 2.27's certificate form, and this equality discharges
the reconciliation obligation recorded at its definition.

**Proof sketch.** Antisymmetry: `Complexity.NEXP_subset_iUnion_NTIME` one way;
`Set.iUnion_subset` with `Complexity.ntime_expPow_subset_NEXP` at every exponent the
other. -/
theorem NEXP_eq_iUnion_NTIME : NEXP = ⋃ c : ℕ, NTIME fun n => 2 ^ n ^ c := by
  sorry

/-- **Padding scales collapses up** [AB09, Theorem 2.22, contrapositive form]: if
`P = NP` then `EXP = NEXP`.

**Proof sketch.** `EXP ⊆ NEXP` is `Complexity.EXP_subset_NEXP`. Conversely let
`L ∈ NEXP` with `(C, c, V)` and `E n = C·2^((n+1)^c)`; the padded language is
`L_pad = {Turing.pairEncode x (List.replicate (E |x|) true) : x ∈ L}`
([AB09]'s `⟨x, 1^(2^(|x|^c))⟩`, rendered with the audited self-delimiting pairing;
`|Turing.pairEncode x pad| = 2|x| + 2 + E |x|`). **`L_pad ∈ NP`**, through the (⇐)
direction of the bounded paired interface `Complexity.mem_NP_iff_exists_length_le` —
this is the route of [AB09, Exercise 2.27], no nondeterministic machines: parameters
`C' = 1`, `c' = 1` (the `NEXP` certificate `u` of `x` has `|u| = E |x| ≤ |x'|` for the
padded input `x'`), and verifier
`V' = {Turing.pairEncode x' u : x' = Turing.pairEncode x (List.replicate (E |x|) true)
for some x, |u| = E |x|, and x ++ u ∈ V}`. Deciding `V'` in time polynomial in
`|x'| + |u|`: parse the outer pair (`Turing.pairDecode` — self-delimiting, outermost
first; a parsing-machine obligation), parse `x'` into `(x, pad)`, evaluate `E |x|` in
binary — **before any validity assumption** its bit length is at most
`(|x|+1)^c + bits(C) + 1`, polynomial in the actual input length since the parsed
`x` is a substring of the input (`E n = 0` when `C = 0`); the logarithmic-in-`|x'|`
estimate holds only *after* the padding-length check and must not be used to budget
the evaluation itself (round-1 audit, finding 1) — check `pad` is all-`true` of
exactly that length and `|u|` equals it exactly (rejecting otherwise — malformed
`x'` lies in neither `L_pad` nor any `V'`-pair, keeping the equivalence for all
inputs; both exact checks are needed, the bounded outer witness condition replaces
neither), assemble `x ++ u` (length
`≤ |x'|`), and run `V`'s polynomial decider relocated-and-captured (the shared
obligations). By `P = NP`, `L_pad ∈ P`; let `M_pad` decide it within `A·(m+1)^d`.
**`L ∈ EXP`**: on `x`, evaluate `E |x|` and write the pad (`E |x|` symbols —
exponential time, which `EXP` affords), assemble `y = Turing.pairEncode x pad` by an
emission machine, run the relocated, captured `M_pad` on `y`, and forward the verdict.
Total time is polynomial in `|y| = 2|x| + 2 + E |x|`, hence at most `2^(n^e)` for a
fixed `e` beyond a fixed threshold, small lengths absorbed into `DTIME`'s constant:
`L ∈ EXP`. -/
theorem EXP_eq_NEXP_of_P_eq_NP (h : P = NP) : EXP = NEXP := by
  sorry

/-- **Theorem 2.22** [AB09]: if `EXP ≠ NEXP` then `P ≠ NP`.

**Proof sketch.** Contraposition of `Complexity.EXP_eq_NEXP_of_P_eq_NP`. -/
theorem P_ne_NP_of_EXP_ne_NEXP (h : EXP ≠ NEXP) : P ≠ NP := by
  sorry

end Complexity
