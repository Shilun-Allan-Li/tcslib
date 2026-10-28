/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Build.IterateFind
import TCSlib.Complexity.Randomized.Build.StateLoop
import TCSlib.Complexity.Randomized.Build.StringLoops
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The repetition lemma: polynomially many rounds of a polynomial-time step

Every theorem of [PS10, ch. 2–4] that *repeats* an adversary — hardness amplification
[PS10, Theorem 35.1, Algorithm 38.5: `2nm²p(n)` fresh-coin calls returning the first
success], Goldreich–Levin [PS10, Theorem 87.3: `n(2^k − 1)` calls and a majority], the
next-bit predictor, the GGM distinguisher hosting `q(n)` oracle queries, the truncated
simulators of the zero-knowledge chapter (inventory item Inf-4.3: "restart loops with a
bounded number of attempts as strict PPT", Claims 123.d and 128.a), rejection samplers
(D10) — reduces to one machine lemma, `Complexity.polyTimeComputable_iterateFind`: iterate a
polynomial-time step `g` at most `R(|x|)` times on a polynomially bounded orbit and return
the payload `out` of the first orbit point accepted by `acc` (`[]` on exhaustion). The
iteration `polyTimeComputable_iterate`, the concatenating variant
`polyTimeComputable_iterateEmit`, the block map and the string tests `majority`, `pairXor`,
`pairEq` are instances or small machines.

**Admissions policy (D11).** `polyTimeComputable_iterateFind` is the single machine lemma
that may remain admitted at the end of the fill campaign (run 4); every theorem that repeats
an adversary depends on it and on nothing else admitted, and the headline axiom prints
(`audits/pass-shelat/Checks.lean`) list it by name if it is still open. The derived lemmas of
this file are to be closed from it (or by small direct machines), so that the admission stays
a single named one. **Status (run 3b):** `polyTimeComputable_iterateFind` is closed — its
machine is built in `TCSlib.Complexity.Randomized.Build.IterateFindHost` (clean modules and
the finite host) and `TCSlib.Complexity.Randomized.Build.IterateFind` (assembly through
`Turing.FinTM.exists_loopFindTM`), and its axiom print is `[propext, Classical.choice, Quot.sound]`.
The six derived lemmas are closed too, as instances of one private **state-loop** form
`polyTimeComputable_stateFind` of the repetition lemma (a state word `⟨x, s⟩` retaining the
input, a step on the state, a test firing first at round `N x ≤ R|x|`, an output read off the
final state), whose loop data, orbit closed forms and bounds live in
`TCSlib.Complexity.Randomized.Build.StateLoop` (the form itself and the two iteration loops)
and `TCSlib.Complexity.Randomized.Build.StringLoops` (the four string loops).

**Construction plan of `iterateFind` (DESIGN.md §2.6, with the three panel repairs built in;
the proof sketch of the theorem repeats it).**

1. *State word carries the input.* `s0 x := ⟨x, x⟩` (second component: the current orbit
   point). Loop data for `Turing.FinTM.exists_loopFindTM`: `stepF x w := guardedStep g P x w`
   (**length-guarded**: `⟨x, g (snd w)⟩` if `|g (snd w)| ≤ P|x|`, else `w`),
   `acceptF x w := acc (snd w)`, `out x w := out (snd w)`,
   `Inv x w := fst w = x ∧ |snd w| ≤ P|x|` (`LoopInv`). `hInv0` is `pairDecode_pairEncode`
   plus `horbit x 0`; `hInvStep` holds for every `w` because the guarded step leaves `w`
   unchanged when the new point would be too long (`loopInv_guardedStep`). On the orbit
   `i ≤ R|x|`, `horbit` shows the guard is never taken, so
   `(stepF x)^[i] (s0 x) = ⟨x, g^[i] x⟩` (`iterate_guardedStep_eq`) and the `find?` of the
   conclusion is the statement's.
2. *Modules.* From `hg`, `hacc`, `hout` build three clean-call modules over the state word:
   `C₁ := exists_installCallTM` for `w ↦ ⟨[acc (snd w)], w⟩` (the verdict as the first cell of
   the installed word, `pairEncode [b] w = [b, b, false, true] ++ w`, no scan needed);
   `C₂ := exists_installCallTM` for the guarded step on the pair (FP by
   `polyTimeComputable_ite` with `polyTimeComputable_lenLe` on `⟨1^{P|fst w|}, g (snd w)⟩`,
   `polyTimeComputable_unaryPoly P`); `C₃ := exists_emitCallTM` for `w ↦ out (snd (snd w))`.
   Each module promises first-visit-to-exit from the clean seam over an arbitrary native
   input and `0 < C.k`.
3. *Gluing without overriding `exit`.* Body state `Unit ⊕ (C₁.State ⊕ C₂.State ⊕ C₃.State) ⊕ Fin 3`;
   tape counts equalised with idle tapes (`leftAction`/`leftCfg_run`, Simulation.lean). The
   anchor is the fresh state `inl ()`, whose transition is stationary into `C₁.entry` (no
   module-internal state is the anchor). The module tables are copied with every transition
   *targeting* `Cᵢ.exit` redirected to a fresh branch state `inr (inr k)`, so the module's own
   table at `exit` is never consulted and `entry = exit` is harmless: the first positive visit
   of `exit` promised by the contract is exactly the first entry into the branch state, with
   the clean seam on the tapes. Branch states: after `C₁`, read tape-0 cell 0 — `true` →
   `C₃.entry`, `false` → `C₂.entry`; after `C₂` → anchor (one stationary step); after `C₃` → halt.
4. *`hstart`.* From `initCfg x`, install `s0 x = ⟨x, x⟩` on tape 0: one more
   `exists_installCallTM` module for `pairDup` (`computesFunInTime_pairDup`) applied to the
   argument word `x`, which is first copied onto tape 0 by a one-state copy scan of the native
   input plus `timed_rewind` (precedent: the startup phases of `computesFunInTime_splitSolveWith`).
   No anchor visit before the seam.
5. *`hround`.* From `Cfg.ofWords anchor (stateWord K w)` with `Inv x w`: one step into
   `C₁.entry`; `C₁` to its first exit (`t₁ ≤ c₁ (T_acc(|w|) + 2|w| + 5)`), branch; accepting
   clause: `C₃` to its first exit emitting `out (snd w)` and halt; advancing clause: `C₂` to
   its first exit installing `stepF x w`, one step to the anchor. Anchor exclusion inside the
   round is syntactic (the anchor is `inl ()`, entered only from the post-`C₂` branch state).
   Budget `T n := c (T_g(Q n) + T_acc(Q n) + T_out(Q n) + Q n + 8)` with
   `Q n := 2n + 2 + P.eval n + 4` (the length of the state word), a normal-form majorant by
   `PolyExpr.eval_le`.
6. *Fuel.* `hF` from `computesFunInTime_polyBits` for a normal-form majorant of `R`, or
   `polyTimeComputable_unaryPoly R` + `computesFunInTime_lengthBits` for exact `R` (the `find?`
   range must be exactly `R|x| + 1`: use the exact form).
7. *Conclusion.* `exists_loopFindTM` gives `E` within `c (T n + 1)(R n + 2)`; package as
   `PolyTimeComputable`. `iterate` threads a unary counter in the state
   (`acc := lenEq cnt 1^{R|x|}` against `unaryPoly R` of the retained input); `iterateEmit`
   threads an accumulator; the derived string functions are instances.

Estimated size 1 200–1 800 lines; private precedent for the module gluing: `satClean_install`,
`satStopTM`, `sat_run_agree` in `TCSlib.Complexity.ClassNP.SAT` (private copies, not edits).

## Main definitions

* `Complexity.guardedStep` — the length-guarded step on the state word `⟨x, s⟩`.
* `Complexity.LoopInv` — the loop invariant `fst w = x ∧ |snd w| ≤ P|x|`.

## Main results

* `Complexity.polyTimeComputable_iterateFind` — the load-bearing lemma (proved: the machine
  is built in `TCSlib.Complexity.Randomized.Build.IterateFind`, and the pure facts below
  identify its guarded orbit with `g^[i] x`).
* `Complexity.polyTimeComputable_iterate`, `Complexity.polyTimeComputable_iterateEmit` —
  `R(|x|)`-fold iteration and concatenated emissions (proved; state loops with a unary round
  counter).
* `Complexity.polyTimeComputable_majority`, `polyTimeComputable_pairXor`,
  `polyTimeComputable_pairEq`, `polyTimeComputable_blockMap` — string tests and the block
  map used by the reductions (proved; state loops consuming the input).
* `Complexity.loopInv_init`, `Complexity.loopInv_guardedStep`,
  `Complexity.iterate_guardedStep_eq`, `Complexity.acc_guardedStep_eq` — the pure facts about
  the guarded step (proved; step 1 of the plan).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1; Theorem 87.3; Algorithms 123.4 and 128.7.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded machines.)
-/

namespace Complexity

open Turing StateLoop

/-! ### The guarded step and its pure theory (step 1 of the plan) -/

/-- The length-guarded step on the state word `w = ⟨x, s⟩`: advance to `⟨x, g s⟩` if the new
orbit point fits the bound `P|x|`, else stay (DESIGN.md §2.6, step 1). The guard makes the
loop invariant `LoopInv` closed under the step for every state word; on the orbit it is
never taken. -/
def guardedStep (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool) : List Bool :=
  if (g (pairSndD w)).length ≤ P.eval x.length then pairEncode x (g (pairSndD w)) else w

/-- The loop invariant: the state word carries the input `x` in its first component and an
orbit point of length at most `P|x|` in its second. -/
def LoopInv (P : PolyExpr) (x w : List Bool) : Prop :=
  pairFstD w = x ∧ (pairSndD w).length ≤ P.eval x.length

/-- The initial state word `⟨x, x⟩` satisfies the invariant when `|x| ≤ P|x|` (the case `i = 0`
of the orbit bound). -/
theorem loopInv_init (P : PolyExpr) (x : List Bool) (h0 : x.length ≤ P.eval x.length) :
    LoopInv P x (pairEncode x x) := by
  simp [LoopInv, h0]

/-- The invariant is closed under the guarded step, for every state word: if the new orbit
point fits, the new word is `⟨x, g s⟩`; otherwise the word is unchanged. -/
theorem loopInv_guardedStep (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool)
    (h : LoopInv P x w) : LoopInv P x (guardedStep g P x w) := by
  unfold guardedStep
  split_ifs with hg
  · simp [LoopInv, hg]
  · exact h

/-- On the orbit the guard is never taken: for `i ≤ R|x|`, the `i`-fold guarded step from
`⟨x, x⟩` is `⟨x, g^[i] x⟩` (induction on `i`, using the orbit bound at `i`). -/
theorem iterate_guardedStep_eq (g : List Bool → List Bool) (R P : PolyExpr) (x : List Bool)
    (horbit : ∀ i, i ≤ R.eval x.length → (g^[i] x).length ≤ P.eval x.length)
    (i : ℕ) (hi : i ≤ R.eval x.length) :
    (guardedStep g P x)^[i] (pairEncode x x) = pairEncode x (g^[i] x) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (Nat.le_of_succ_le hi)]
    unfold guardedStep
    have hlen : (g (g^[i] x)).length ≤ P.eval x.length := by
      rw [← Function.iterate_succ_apply' g i x]
      exact horbit (i + 1) hi
    simp [hlen, Function.iterate_succ_apply']

/-- The acceptance tests of the loop agree with those of the statement on the whole range
`0, …, R|x|`: `acc (snd ((stepF x)^[i] ⟨x, x⟩)) = acc (g^[i] x)`. -/
theorem acc_guardedStep_eq (g : List Bool → List Bool) (acc : List Bool → Bool) (R P : PolyExpr)
    (x : List Bool)
    (horbit : ∀ i, i ≤ R.eval x.length → (g^[i] x).length ≤ P.eval x.length)
    (i : ℕ) (hi : i ≤ R.eval x.length) :
    acc (pairSndD ((guardedStep g P x)^[i] (pairEncode x x))) = acc (g^[i] x) := by
  rw [iterate_guardedStep_eq g R P x horbit i hi, pairSndD_pairEncode]

/-! ### The repetition lemma and its instances -/

/-- **The repetition lemma (load-bearing; D11).** Let `g` be a polynomial-time step, `acc` a
polynomial-time acceptance test, `out` a polynomial-time payload map, `R` and `P` syntactic
polynomials such that the orbit `g^[i] x` stays of length `≤ P|x|` for `i ≤ R|x|`. Then the
function "iterate `g` from `x` at most `R|x|` times and return `out` of the first accepted
orbit point, `[]` if none is accepted" is polynomial-time computable. It is the machine
behind every repeated-adversary argument of [PS10]: Algorithm 38.5's `2nm²p(n)` attempts
with first success [PS10, Theorem 35.1], the `n(2^k−1)` calls of Goldreich–Levin
[PS10, Theorem 87.3], rejection sampling (D10), the truncated simulators
[PS10, Algorithms 123.4 and 128.7] (inventory Inf-4.3).

**Proof sketch.** Instance of `Turing.FinTM.exists_loopFindTM` (Loop.lean) with the data of the
construction plan in the module docstring: (1) state word `⟨x, s⟩`, guarded step
`guardedStep g P`, invariant `LoopInv P` (`loopInv_init`, `loopInv_guardedStep`), and on the
orbit `(stepF x)^[i] ⟨x, x⟩ = ⟨x, g^[i] x⟩` (`iterate_guardedStep_eq`), so the loop's `find?`
over `List.range (R|x| + 1)` is the statement's (`acc_guardedStep_eq`); (2) the three
clean-call modules `C₁` (verdict installed as the first cell), `C₂` (guarded step on the
pair, FP by `polyTimeComputable_ite`, `polyTimeComputable_lenLe`,
`polyTimeComputable_unaryPoly P`) and `C₃` (`out` of the orbit point, emitted) from
`exists_installCallTM`/`exists_emitCallTM`; (3) the glued body with the fresh anchor
`inl ()` and transitions into each `exit` redirected to fresh branch states; (4) `hstart` by a
`pairDup` install module after a copy scan and `timed_rewind`; (5) `hround` with budget
`T n := c (T_g(Q n) + T_acc(Q n) + T_out(Q n) + Q n + 8)`, `Q n := 2n + 2 + P n + 4`, in normal
form by `PolyExpr.eval_le`; (6) fuel `Nat.bits (R|x|)` by `polyTimeComputable_unaryPoly R`
and `computesFunInTime_lengthBits`; (7) `exists_loopFindTM` returns a machine within
`c (T n + 1)(R n + 2)`, packaged as `PolyTimeComputable`. Sub-obligations: the four modules,
the gluing lemma (precedent: `satClean_install`/`sat_run_agree` in `ClassNP/SAT.lean`), the
startup phase, the round budget arithmetic. -/
theorem polyTimeComputable_iterateFind {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x)) with
      | some i => out (g^[i] x)
      | none => [] := by
  have h := IterateFind.polyTimeComputable_find hg hacc hout R P horbit
  convert h using 1
  funext x
  have hstep : IterateFind.step g P x = guardedStep g P x := rfl
  have hfind : (List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x)) =
      (List.range (R.eval x.length + 1)).find?
        (fun i => acc (pairSndD ((IterateFind.step g P x)^[i] (pairEncode x x)))) := by
    apply IterateFind.find?_congr_of_mem
    intro i hi
    rw [List.mem_range] at hi
    rw [hstep, acc_guardedStep_eq g acc R P x (horbit x) i (by omega)]
  rw [hfind]
  cases hf : (List.range (R.eval x.length + 1)).find?
      (fun i => acc (pairSndD ((IterateFind.step g P x)^[i] (pairEncode x x)))) with
  | none => rfl
  | some i =>
    have hi := List.mem_of_find?_eq_some hf
    rw [List.mem_range] at hi
    simp only [hstep, iterate_guardedStep_eq g R P x (horbit x) i (by omega), pairSndD_pairEncode]

/-! ### State loops: the common form of the derived lemmas -/

/-- **State loops** (the common form of the six derived lemmas; DESIGN.md §2.6, step 7). A
state word `⟨x, s⟩` retains the input `x` and evolves its state from `start x` by
`s ↦ step ⟨x, s⟩` (`Complexity.StateLoop.orbit`); a test `acc` on the state word is `false`
before round `N x` and `true` at round `N x ≤ R|x|`, the states up to that round have length at
most `B|x|`, and `out` reads the answer off the final state word. Then
`x ↦ out ⟨x, orbit x (N x)⟩` is polynomial-time computable.

**Proof sketch.** Instance of `polyTimeComputable_iterateFind` on the length-guarded step
`Complexity.StateLoop.gstep step B` (which refuses to move when the new state would exceed
`B|fst w|`), with `R` as the round polynomial and `StateLoop.gstepBound B = 3n + 2 + B(n)` as
the orbit bound — valid for *every* word by `StateLoop.length_gstep_iterate_le`, which is what
`horbit` demands — pre-composed with `x ↦ ⟨x, start x⟩` (`PolyTimeComputable.pairEncode`). On
the genuine orbit the guard never fires (`StateLoop.gstep_iterate_eq`, from the bound on the
first `N x` states), so the loop's `find?` over `List.range (R|⟨x, start x⟩| + 1)` — a range
containing `N x`, as `R` is monotone (`PolyExpr.eval_mono`) — returns `some (N x)`
(`StateLoop.find?_range_eq_some`), and the payload is `out ⟨x, orbit x (N x)⟩`. -/
private theorem polyTimeComputable_stateFind {start step : List Bool → List Bool}
    {acc : List Bool → Bool} {out : List Bool → List Bool}
    (hstart : PolyTimeComputable start) (hstep : PolyTimeComputable step)
    (hacc : PolyTimeComputable fun w => [acc w]) (hout : PolyTimeComputable out)
    (R B : PolyExpr) (N : List Bool → ℕ) (hN : ∀ x, N x ≤ R.eval x.length)
    (hbound : ∀ x i, i ≤ N x → (orbit start step x i).length ≤ B.eval x.length)
    (hfirst : ∀ x i, i < N x → acc (pairEncode x (orbit start step x i)) = false)
    (hlast : ∀ x, acc (pairEncode x (orbit start step x (N x))) = true) :
    PolyTimeComputable fun x => out (pairEncode x (orbit start step x (N x))) := by
  have hF := polyTimeComputable_iterateFind (gstep_poly hstep B) hacc hout R (gstepBound B)
    (fun w i _ => length_gstep_iterate_le step B w i)
  have hpre : PolyTimeComputable fun x => pairEncode x (start x) :=
    polyTimeComputable_id.pairEncode hstart
  convert hF.comp hpre using 1
  funext x
  simp only [Function.comp_apply]
  have horb := gstep_iterate_eq start step B x (N x) (hbound x)
  have hle : N x ≤ R.eval (pairEncode x (start x)).length :=
    (hN x).trans (R.eval_mono (by rw [length_pairEncode]; omega))
  have hfind : (List.range (R.eval (pairEncode x (start x)).length + 1)).find?
      (fun i => acc ((gstep step B)^[i] (pairEncode x (start x)))) = some (N x) := by
    apply find?_range_eq_some hle
    · intro i hi
      rw [horb i hi.le]
      exact hfirst x i hi
    · rw [horb (N x) le_rfl]
      exact hlast x
  rw [hfind]
  exact (congrArg out (horb (N x) le_rfl)).symm

/-- **Polynomially many iterations:** under the orbit bound, `x ↦ g^[R|x|] x` is
polynomial-time computable (the honest `m(n)`-fold evaluations of [PS10, Theorem 35.1]
and the `ℓ(n)`-fold generator expansion of [PS10, Lemma 80.5] are instances).

**Proof sketch.** State loop (`polyTimeComputable_stateFind`, data in
`Complexity.StateLoop.IterLoop`) on the state `⟨1^i, g^[i] x⟩` from `⟨[], x⟩`: the step
appends a token to the unary counter and advances the orbit point (`IterLoop.orbit_eq`);
`acc` is the length test `R|x| ≤ |cnt|` against `1^{R|x|}` of the retained input
(`polyTimeComputable_unaryPoly R`, `polyTimeComputable_lenLe`), `false` below round `R|x|`
and `true` there; `out` projects the orbit point. The states of the first `R|x|` rounds have
length `2i + 2 + |g^[i] x| ≤ 2R|x| + 2 + P|x|` by `horbit`. -/
theorem polyTimeComputable_iterate {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x => g^[R.eval x.length] x := by
  have hbound : ∀ x i, i ≤ R.eval x.length →
      (orbit IterLoop.start (IterLoop.step g) x i).length ≤
        (PolyExpr.add (.mul (.const 2) R) (.add (.const 2) P)).eval x.length := by
    intro x i hi
    rw [IterLoop.orbit_eq, length_pairEncode, List.length_replicate]
    have := horbit x i hi
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  have hfirst : ∀ x i, i < R.eval x.length →
      IterLoop.acc R (pairEncode x (orbit IterLoop.start (IterLoop.step g) x i)) = false := by
    intro x i hi
    rw [IterLoop.orbit_eq]
    simp [IterLoop.acc, hi]
  have hlast : ∀ x, IterLoop.acc R
      (pairEncode x (orbit IterLoop.start (IterLoop.step g) x (R.eval x.length))) = true := by
    intro x
    rw [IterLoop.orbit_eq]
    simp [IterLoop.acc]
  have h := polyTimeComputable_stateFind IterLoop.start_poly (IterLoop.step_poly hg)
    (IterLoop.acc_poly R) IterLoop.out_poly R _ (fun x => R.eval x.length) (fun _ => le_rfl)
    hbound hfirst hlast
  convert h using 1
  funext x
  rw [IterLoop.orbit_eq]
  simp [IterLoop.out]

/-- **Polynomially many iterations with concatenated emissions:** under the orbit bound,
`x ↦ emit x ++ emit (g x) ++ ⋯ ++ emit (g^[R|x|] x)` is polynomial-time computable (the
`m − 1` evaluations of `f` whose outputs form the tuple of Algorithm 38.5, the block
evaluations of `prodFun`, the lazily sampled GGM table).

**Proof sketch.** As `polyTimeComputable_iterate` (state loop, data in
`Complexity.StateLoop.EmitLoop`), with the state `⟨1^i, ⟨g^[i] x, acc_i⟩⟩` where
`acc_i = (List.range i).flatMap (emit ∘ g^[·] x)`: the step appends `emit` of the current
orbit point to the accumulator (`PolyTimeComputable.append`) before advancing
(`EmitLoop.orbit_eq`); the counter test `IterLoop.acc R` fires first at round `R|x|`, where
`out` returns `acc_i ++ emit (g^[i] x)` (`List.range_succ`, `List.flatMap_append`). The
accumulator is bounded by `R|x| · C (P|x| + 1)^c` with `C, c` from `hemit.output_length_le`
(`StateLoop.length_flatMap_range_le`), the `PolyExpr` `R · (normal C c)[P/n]`
(`PolyExpr.eval_subst`). -/
theorem polyTimeComputable_iterateEmit {g emit : List Bool → List Bool}
    (hg : PolyTimeComputable g) (hemit : PolyTimeComputable emit) (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      (List.range (R.eval x.length + 1)).flatMap fun i => emit (g^[i] x) := by
  obtain ⟨Ce, ce, hCe⟩ := hemit.output_length_le
  have hbound : ∀ x i, i ≤ R.eval x.length →
      (orbit EmitLoop.start (EmitLoop.step g emit) x i).length ≤
        (PolyExpr.add (.mul (.const 2) R) (.add (.const 4) (.add (.mul (.const 2) P)
          (.mul R ((PolyExpr.normal Ce ce).subst P))))).eval x.length := by
    intro x i hi
    rw [EmitLoop.orbit_eq, length_pairEncode, length_pairEncode, List.length_replicate]
    have h1 := horbit x i hi
    have hchunk : ∀ j < i, (emit (g^[j] x)).length ≤ Ce * (P.eval x.length + 1) ^ ce := by
      intro j hj
      refine (hCe _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
      have := horbit x j (by omega)
      omega
    have h2 := (length_flatMap_range_le _ _ i hchunk).trans (Nat.mul_le_mul_right _ hi)
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_subst,
      PolyExpr.eval_normal]
    generalize R.eval x.length * (Ce * (P.eval x.length + 1) ^ ce) = Q at h2
    omega
  have hfirst : ∀ x i, i < R.eval x.length →
      IterLoop.acc R (pairEncode x (orbit EmitLoop.start (EmitLoop.step g emit) x i)) = false := by
    intro x i hi
    rw [EmitLoop.orbit_eq]
    simp [IterLoop.acc, hi]
  have hlast : ∀ x, IterLoop.acc R (pairEncode x
      (orbit EmitLoop.start (EmitLoop.step g emit) x (R.eval x.length))) = true := by
    intro x
    rw [EmitLoop.orbit_eq]
    simp [IterLoop.acc]
  have h := polyTimeComputable_stateFind EmitLoop.start_poly (EmitLoop.step_poly hg hemit)
    (IterLoop.acc_poly R) (EmitLoop.out_poly hemit) R _ (fun x => R.eval x.length)
    (fun _ => le_rfl) hbound hfirst hlast
  convert h using 1
  funext x
  rw [EmitLoop.orbit_eq]
  simp [EmitLoop.out, List.range_succ]

/-- **Majority vote** on a bit string: `w ↦ [decide (|w| < 2 · #true w)]` (strict majority of
`true`) is polynomial-time computable (the vote of the Goldreich–Levin inverter
[PS10, Algorithm 89.6] and of the next-bit predictor).

**Proof sketch.** State loop (`polyTimeComputable_stateFind`, data in
`Complexity.StateLoop.MajLoop`) with `R := var` on the state `⟨rest, ⟨1^{#true}, 1^{#false}⟩⟩`
from `⟨w, ⟨[], []⟩⟩`: each step drops the first bit of `rest` (`StateLoop.tail_poly`) and
appends a token to the counter of its value (`StateLoop.headBit_poly`,
`polyTimeComputable_ite`), so after `i ≤ |w|` rounds the state is
`⟨w.drop i, ⟨1^{#true (w.take i)}, 1^{#false (w.take i)}⟩⟩` (`MajLoop.orbit_eq`); `acc` is the
emptiness test on `rest`, first `true` at round `|w|`; `out` is the length test
`|1 :: 1^{#false}| ≤ |1^{#true}|` (`polyTimeComputable_lenLe`), which is the verdict since
`|w| < 2 #true ↔ #false + 1 ≤ #true` (`List.count_true_add_count_false`). States have length
at most `5|w| + 4`. -/
theorem polyTimeComputable_majority :
    PolyTimeComputable fun w => [decide (w.length < 2 * w.count true)] := by
  have h := polyTimeComputable_stateFind MajLoop.start_poly MajLoop.step_poly MajLoop.acc_poly
    MajLoop.out_poly .var (.add (.mul (.const 5) .var) (.const 4)) List.length (fun _ => le_rfl)
    (fun w i hi => by simpa using MajLoop.orbit_length_le w i hi) MajLoop.acc_orbit_false
    MajLoop.acc_orbit_true
  convert h using 1
  funext w
  exact (MajLoop.out_orbit w).symm

/-- **Bitwise exclusive-or of the two components of a pair** (`List.zipWith xor`) is
polynomial-time computable (the one-time pad of [PS10, Algorithm 92.1 and 99.1] and the
hard-core-bit mask of [PS10, Algorithm 104.3]).

**Proof sketch.** State loop (`polyTimeComputable_stateFind`, data in
`Complexity.StateLoop.XorLoop`) with `R := var` on the state `⟨a', ⟨b', c⟩⟩` from
`⟨fst z, ⟨snd z, []⟩⟩`: each step drops the heads of `a'`, `b'` and appends their xor to `c`
(`StateLoop.tail_poly`, `StateLoop.headBit_poly`, `StateLoop.xor_poly`), so after
`i ≤ min |a| |b|` rounds the state is `⟨a.drop i, ⟨b.drop i, (zipWith xor a b).take i⟩⟩`
(`XorLoop.orbit_eq`, by `List.take_succ` and `List.getElem?_zipWith`); `acc` is "one of `a'`,
`b'` is empty" (`StateLoop.isNil_poly`, `StateLoop.or_poly`), first `true` at round
`min |a| |b| = |zipWith xor a b|` (`List.length_zipWith`), where `out` returns `c`. States have
length at most `5|z| + 4` (`StateLoop.length_pairFstD_add_pairSndD_le`). -/
theorem polyTimeComputable_pairXor :
    PolyTimeComputable fun z => List.zipWith xor (pairFstD z) (pairSndD z) := by
  have hN : ∀ z, XorLoop.rounds z ≤ PolyExpr.var.eval z.length := by
    intro z
    have := length_pairFstD_add_pairSndD_le z
    unfold XorLoop.rounds
    simp only [PolyExpr.eval_var]
    omega
  have h := polyTimeComputable_stateFind XorLoop.start_poly XorLoop.step_poly XorLoop.acc_poly
    XorLoop.out_poly .var (.add (.mul (.const 5) .var) (.const 4)) XorLoop.rounds hN
    (fun z i hi => by simpa using XorLoop.orbit_length_le z i hi) XorLoop.acc_orbit_false
    XorLoop.acc_orbit_true
  convert h using 1
  funext z
  exact (XorLoop.out_orbit z).symm

/-- **Equality test of the two components of a pair** (`[decide (fst z = snd z)]`) is
polynomial-time computable (the test `f(z_i) = y` of [PS10, Algorithm 38.5] and every
verification step of the reductions).

**Proof sketch.** State loop (`polyTimeComputable_stateFind`, data in
`Complexity.StateLoop.EqLoop`) with `R := var` on the state `⟨a', ⟨b', flag⟩⟩` from
`⟨fst z, ⟨snd z, []⟩⟩`: each step drops the heads of `a'`, `b'` and sets `flag := [true]` if
they differ (`polyTimeComputable_ite` on `StateLoop.xor_poly`), so after `i ≤ min |a| |b|`
rounds the state is `⟨a.drop i, ⟨b.drop i, flag⟩⟩` with `flag = []` iff `a.take i = b.take i`
(`EqLoop.orbit_eq`, `EqLoop.flag_succ`); `acc` is `XorLoop.acc` ("one of `a'`, `b'` is
empty"), first `true` at round `min |a| |b|`, where `out` is the conjunction of the three
emptiness tests `a' = [] ∧ b' = [] ∧ flag = []` (`polyTimeComputable_and`), i.e. `a = b`
(`EqLoop.verdict_eq`: equal lengths and equal prefixes). States have length at most
`5|z| + 5`. -/
theorem polyTimeComputable_pairEq :
    PolyTimeComputable fun z => [decide (pairFstD z = pairSndD z)] := by
  have hN : ∀ z, XorLoop.rounds z ≤ PolyExpr.var.eval z.length := by
    intro z
    have := length_pairFstD_add_pairSndD_le z
    unfold XorLoop.rounds
    simp only [PolyExpr.eval_var]
    omega
  have h := polyTimeComputable_stateFind XorLoop.start_poly EqLoop.step_poly XorLoop.acc_poly
    EqLoop.out_poly .var (.add (.mul (.const 5) .var) (.const 5)) XorLoop.rounds hN
    (fun z i hi => by simpa using EqLoop.orbit_length_le z i hi) EqLoop.acc_orbit_false
    EqLoop.acc_orbit_true
  convert h using 1
  funext z
  exact (EqLoop.out_orbit z).symm

/-- **Block map:** apply `g` to the consecutive blocks of length `b(|fst z|)` of `snd z` and
concatenate (the first component carries `1^n`; the `⌊|snd z| / b(n)⌋` full blocks are
mapped, a partial last block is dropped). This evaluates `prodFun f q` blockwise
[PS10, Theorem 35.1, Algorithm 38.5] and decodes tuples of `n`-bit strings.

**Proof sketch.** State loop (`polyTimeComputable_stateFind`, data in
`Complexity.StateLoop.BlockLoop`) with `R := var` (at most `|z|` blocks) on the state
`⟨rest, c⟩` from `⟨snd z, []⟩`, with `k := b(|fst z|)` read off the retained input: each step
drops `k` bits of `rest` and appends `g (rest.take k)` to `c` (`polyTimeComputable_pairDropPoly b`,
`polyTimeComputable_pairTakePoly b` on `⟨fst z, rest⟩`), so after `i` rounds the state is
`⟨(snd z).drop (i k), g (block 0) ++ ⋯ ++ g (block (i − 1))⟩` (`BlockLoop.orbit_eq`,
`List.drop_drop`); `acc` is "`|rest| < k` or `k = 0`" (two length tests against `1^k`), `false`
below round `|snd z| / k` and `true` there (`Nat.le_div_iff_mul_le`, `Nat.lt_mul_div_succ`),
where `out` returns `c`, the statement's `flatMap`. States have length at most
`2|z| + 2 + |z| · C (b(|z|) + 1)^c` with `C, c` from `hg.output_length_le`. -/
theorem polyTimeComputable_blockMap (b : PolyExpr) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun z =>
      (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
        g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length)) := by
  obtain ⟨C, c, hC⟩ := hg.output_length_le
  have hN : ∀ z, BlockLoop.rounds b z ≤ PolyExpr.var.eval z.length := by
    intro z
    have := length_pairFstD_add_pairSndD_le z
    exact (Nat.div_le_self _ _).trans (by simp only [PolyExpr.eval_var]; omega)
  have h := polyTimeComputable_stateFind BlockLoop.start_poly (BlockLoop.step_poly b hg)
    (BlockLoop.acc_poly b) BlockLoop.out_poly .var _ (BlockLoop.rounds b) hN
    (BlockLoop.orbit_length_le b g C c hC) (BlockLoop.acc_orbit_false b g)
    (BlockLoop.acc_orbit_true b g)
  convert h using 1
  funext z
  exact (BlockLoop.out_orbit b g z).symm

end Complexity
