/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Build.PairSplit
import TCSlib.Complexity.Randomized.Build.UnaryMul
import TCSlib.Complexity.Randomized.PolyExpr

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two new machine primitives: coin splitting and unary multiplication

The closure calculus of non-uniform PPTs ([PS10, §2.1], implicit in every reduction of
chapters 2–4; inventory item Claim-26.3) needs two string machines that the library's
catalog `TCSlib.Complexity.TuringMachine.Build.Primitives` does not provide:

* `Turing.FinTM.computesFunInTime_pairSplitAt` — `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩`: cut a
  coin string at a unary length (fresh coin segments as independent uniform strings);
* `Turing.FinTM.computesFunInTime_unaryMul` — `⟨1^a, 1^b⟩ ↦ 1^{ab}`: unary multiplication,
  which makes every syntactic polynomial computable in unary
  (`Complexity.polyTimeComputable_unaryPoly`) without the repetition lemma (D9).

Both are built in the `Build/` style (foundation decision D11): explicit finite machines with
a proved timed contract (`TCSlib.Complexity.Randomized.Build.PairSplit`,
`TCSlib.Complexity.Randomized.Build.UnaryMul`). This file states the two contracts with their
construction sketches (DESIGN.md §2.4) and derives the FP-level consequences the closure
catalogue consumes:
`polyTimeComputable_unaryPoly` (by induction on the expression, the `mul` case being the
only use of `unaryMul`) and the typed cuts `polyTimeComputable_pairTakePoly` /
`polyTimeComputable_pairDropPoly` (`pairSplitAt` applied to `⟨1^{p(|fst z|)}, snd z⟩`).

The unary evaluator is hosted here rather than in `TCSlib.Complexity.Randomized.PolyExpr`
because its `mul` case needs `unaryMul`, while the cuts below need both the evaluator and
`PolyExpr`; this keeps the import graph acyclic.

## Main results

* `Turing.FinTM.computesFunInTime_pairSplitAt` — coin splitting at a unary length, linear
  time (proved; the machine is `Turing.FinTM.exists_pairSplitTM` in
  `TCSlib.Complexity.Randomized.Build.PairSplit`).
* `Turing.FinTM.computesFunInTime_unaryMul` — unary multiplication, quadratic time
  (proved; the machine is `Turing.FinTM.exists_unaryMulTM` in
  `TCSlib.Complexity.Randomized.Build.UnaryMul`).
* `Complexity.polyTimeComputable_unaryPoly` — `x ↦ 1^{p(|x|)}` is polynomial-time
  computable for every syntactic polynomial `p` (proved by induction; the `mul` and `pow`
  cases rest on `unaryMul`).
* `Complexity.polyTimeComputable_pairTakePoly`, `Complexity.polyTimeComputable_pairDropPoly`
  — on `⟨u, b⟩`, the first / the remaining `p(|u|)` bits of `b` (proved from `pairSplitAt`).

## Main definitions

None (the primitives are existence statements over `Turing.FinTM Bool`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1, the closure properties of p.p.t. machines used implicitly throughout.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, multi-tape machines and linear-time string
  manipulation.)
-/

namespace Turing.FinTM

/-- **Coin splitting at a unary length** (new primitive): on a pair `⟨u, b⟩` the machine
outputs the pair `⟨b.take |u|, b.drop |u|⟩`; on a malformed word it outputs `[]`. Linear
time. This is how a reduction uses disjoint segments of its coin string as independent
uniform strings [PS10, §2.1, implicit; inventory Claim-26.3(c)].

**Proof sketch (construction, DESIGN.md §2.4; built in
`TCSlib.Complexity.Randomized.Build.PairSplit`).** One work tape. Phase 1 is the buffered
aligned parser of `Turing.FinTM.computesFunInTime_pairFst`: it reads the doubled prefix of
`u` onto the work tape without emitting anything, and stops at the separator `01` (a
malformed prefix halts with empty output). Phase 2 rewinds the work head. Phase 3 is a copy
scan of `b`: while the work head walks across the stored `u`, each bit `c` of `b` read on
the input tape is emitted doubled as `cc` (the doubled first component of the output pair);
when the stored `u` is exhausted the machine emits the separator `01` and then copies the
remainder of `b` verbatim (if `b` is shorter than `u`, the separator is emitted when the
input ends and the second component is empty). The step ledger gives at most `5 (n + 1)`
steps; the output is `pairEncode (b.take |u|) (b.drop |u|)` by `Turing.pairEncode_eq_dbl`
(`Turing.FinTM.exists_pairSplitTM`, with `c = 5`). -/
theorem computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
          | none => [])
        fun n => c * (n + 1) := by
  obtain ⟨M, hM⟩ := exists_pairSplitTM
  exact ⟨M, 5, hM⟩

/-- **Unary multiplication** (new primitive): on a pair `⟨u, v⟩` the machine outputs
`1^{|u| · |v|}`; on a malformed word it outputs `[]`. Quadratic time. With it every syntactic
polynomial is computable in unary (`Complexity.polyTimeComputable_unaryPoly`), so the lengths
`1^{p(n)}` that reductions need never go through the repetition lemma (D9).

**Proof sketch (construction, DESIGN.md §2.4; built in
`TCSlib.Complexity.Randomized.Build.UnaryMul`).** One work tape. Phase 1 is the buffered
aligned parser of `Turing.FinTM.computesFunInTime_pairFst`: it undoubles the prefix `u` onto
the work tape without emitting anything (one cell per token of `u`, so the content of `u` is
irrelevant) and validates the separator `01`; a malformed input halts with empty output.
Phase 2 rewinds the work head and then, for each symbol of the second component `v` (read
left to right, its content irrelevant), walks across the stored word emitting one `true`
per cell (`emitAction`-style) and rewinds the work tape; at the end of the input it halts.
**Deviation from the DESIGN.md sketch** (which stores `v` and replays it once per token of
`u`): storing `u` and replaying it once per symbol of `v` needs no input rewind, and the
product `|u| · |v|` is the same. The run takes `|u| + 1 + |v| (2 |u| + 3) + 1` steps after
the parser, at most `(n + 1) ^ 2 + 3 n + 5 ≤ 5 (n + 1) ^ 2` in all (step ledger `mul_run`),
and the output is `List.replicate (|u| * |v|) true` by induction on the symbols of `v`
(`List.replicate_add`, `Nat.mul_succ`) — `Turing.FinTM.exists_unaryMulTM`, with `c = 5`. -/
theorem computesFunInTime_unaryMul :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (u, v) => List.replicate (u.length * v.length) true
          | none => [])
        fun n => c * (n + 1) ^ 2 := by
  obtain ⟨M, hM⟩ := exists_unaryMulTM
  exact ⟨M, 5, hM⟩

end Turing.FinTM

namespace Complexity

open Turing

/-- FP-level unary multiplication: if `x ↦ 1^{f x}` and `x ↦ 1^{g x}` are polynomial-time
computable, so is `x ↦ 1^{f x · g x}` (pair the two unary strings with
`PolyTimeComputable.pairEncode` and apply the unary-multiplication machine). -/
private theorem polyTimeComputable_unaryMulFun {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (f x * g x) true := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_unaryMul
  have hmul : PolyTimeComputable (fun z => match pairDecode z with
      | some (u, v) => List.replicate (u.length * v.length) true
      | none => []) := ⟨M, c, 2, hM⟩
  convert hmul.comp (hf.pairEncode hg) using 1
  funext x
  simp [pairDecode_pairEncode]

/-- **The unary evaluator of a syntactic polynomial is polynomial-time:** for every
`p : PolyExpr`, the map `x ↦ 1^{p(|x|)}` is polynomial-time computable. This is the device by
which a reduction produces every length `1^{p(n)}` it needs (coin cuts, parameter changes,
padding), foundation decision D9; it is never routed through the repetition lemma.

**Proof sketch.** Induction on `p`. `const c`: the constant string `1^c`
(`Complexity.polyTimeComputable_const`). `var`: `x ↦ 1^{|x|}`
(`Complexity.polyTimeComputable_unary`). `add p q`: concatenate the two unary strings
(`Complexity.PolyTimeComputable.append`, `List.replicate_add`). `mul p q`: pair the two unary
strings and apply the unary-multiplication machine `Turing.FinTM.computesFunInTime_unaryMul`
(the only case that uses the new primitive). `pow p c`: inner induction on `c`, the step
being the `mul` case against `1^{p(|x|)}` (`pow_succ`). -/
theorem polyTimeComputable_unaryPoly (p : PolyExpr) :
    PolyTimeComputable fun x => List.replicate (p.eval x.length) true := by
  induction p with
  | const c => exact polyTimeComputable_const (List.replicate c true)
  | var => exact polyTimeComputable_unary
  | add p q hp hq =>
    simpa only [PolyExpr.eval_add, List.replicate_add] using hp.append hq
  | mul p q hp hq => exact polyTimeComputable_unaryMulFun hp hq
  | pow p c hp =>
    induction c with
    | zero => simpa using polyTimeComputable_const (List.replicate 1 true)
    | succ c ih =>
      simpa only [PolyExpr.eval_pow, pow_succ] using polyTimeComputable_unaryMulFun ih hp

/-- The FP form of the coin-splitting machine: `z ↦ ⟨(snd z).take |fst z|, (snd z).drop |fst z|⟩`
on pairs, `[]` on malformed words. -/
private theorem polyTimeComputable_pairSplitAt :
    PolyTimeComputable fun z => match pairDecode z with
      | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
      | none => [] := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_pairSplitAt
  exact polyTimeComputable_of_linear ⟨M, c, hM⟩

/-- The re-pairing `z ↦ ⟨1^{p(|fst z|)}, snd z⟩` is polynomial-time (the unary evaluator on
the first component, paired with the second component). -/
private theorem polyTimeComputable_pairUnaryFst (p : PolyExpr) :
    PolyTimeComputable fun z =>
      pairEncode (List.replicate (p.eval (pairFstD z).length) true) (pairSndD z) :=
  ((polyTimeComputable_unaryPoly p).comp polyTimeComputable_pairFstD).pairEncode
    polyTimeComputable_pairSndD

/-- **Typed coin cut, head:** on `z = ⟨u, b⟩`, the first `p(|u|)` bits of `b` are
polynomial-time computable (`z ↦ (snd z).take (p(|fst z|))`, with the total projections
`Complexity.pairFstD`/`pairSndD`). A reduction run on `⟨1^n, r⟩` thereby reads the first
`p(n)` coins as data [PS10, §2.1, implicit; inventory Claim-26.3(c)].

**Proof sketch.** `pairFstD ∘ pairSplitAt ∘ (z ↦ ⟨1^{p(|fst z|)}, snd z⟩)`: the re-pairing is
`polyTimeComputable_unaryPoly p` on `pairFstD` paired with `pairSndD`
(`PolyTimeComputable.pairEncode`), the split is `Turing.FinTM.computesFunInTime_pairSplitAt`
via `polyTimeComputable_of_linear`, and the composite equals the claimed function by
`Turing.pairDecode_pairEncode`, `Complexity.pairFstD_pairEncode` and `List.length_replicate`
(`PolyTimeComputable.comp`, `funext`). -/
theorem polyTimeComputable_pairTakePoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).take (p.eval (pairFstD z).length) := by
  convert polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSplitAt.comp (polyTimeComputable_pairUnaryFst p)) using 1
  funext z
  simp [pairDecode_pairEncode]

/-- **Typed coin cut, tail:** on `z = ⟨u, b⟩`, the bits of `b` after the first `p(|u|)` are
polynomial-time computable (`z ↦ (snd z).drop (p(|fst z|))`): the remaining coins of a
reduction after the first `p(n)` were consumed.

**Proof sketch.** As `polyTimeComputable_pairTakePoly` with `pairSndD` in place of `pairFstD`
after the split (`Complexity.pairSndD_pairEncode`). -/
theorem polyTimeComputable_pairDropPoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).drop (p.eval (pairFstD z).length) := by
  convert polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSplitAt.comp (polyTimeComputable_pairUnaryFst p)) using 1
  funext z
  simp [pairDecode_pairEncode]

end Complexity
