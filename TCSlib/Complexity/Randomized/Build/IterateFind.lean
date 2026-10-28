/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.Randomized.Build.IterateFindHost
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The machine behind the repetition lemma

The finite machine behind `Complexity.polyTimeComputable_iterateFind`
(`TCSlib.Complexity.Randomized.Repetition`, the load-bearing lemma of the Pass–shelat campaign,
foundation decision D11 of `PassShelatChapter2-4Plan.md`): iterate a polynomial-time step `g`
at most `R(|x|)` times on a polynomially bounded orbit and return the payload `out` of the first
orbit point accepted by `acc` (`[]` on exhaustion). Every theorem of [PS10, ch. 2–4] that
repeats an adversary — Algorithm 38.5's `2nm²p(n)` attempts with first success
[PS10, Theorem 35.1], the `n(2^k − 1)` calls of Goldreich–Levin [PS10, Theorem 87.3], the
truncated simulators [PS10, Algorithms 123.4 and 128.7] — reduces to this machine.

## Construction (DESIGN.md §2.6, the three panel repairs built in)

The machine is an instance of the result-bearing loop combinator
`Turing.FinTM.exists_loopFindTM` (`TCSlib.Complexity.TuringMachine.Build.Loop`).

1. *State word.* The loop state is the pair `⟨x, s⟩` (`Turing.pairEncode x s`) of the input
   and the current orbit point; the loop invariant `Inv` says the word *is* such a pair with
   `|s| ≤ P|x|`; the step is the length-guarded `Complexity.IterateFind.step`
   (`⟨x, g s⟩` if `|g s| ≤ P|x|`, else unchanged), under which the invariant is closed for
   every admissible word; on the orbit the guard never fires (the pure lemmas of
   `TCSlib.Complexity.Randomized.Repetition`).
2. *Modules.* Three clean-call modules over the state word, from
   `Turing.FinTM.exists_installCallTM`/`exists_emitCallTM` applied to FP functions: the
   **verdict** install `w ↦ ⟨[acc (snd w)], w⟩` (the verdict as the first cell of the installed
   word), the **step** install `w' ↦ step` on the pair carried by `w'`, and the **payload** emit
   `w' ↦ out (snd (snd w'))`; plus the startup module `x ↦ ⟨x, x⟩`
   (`Turing.FinTM.computesFunInTime_pairDup`) and a two-state copier that puts the native
   input on tape 0 first.
3. *Gluing.* Each module is converted into a first-halting source (a release flag stops it one
   silent step after its first positive exit), padded to the common tape count, and embedded
   into one finite host through the forwarding transformer `Turing.emitAction`; the host's own
   control has three fresh states — the loop **anchor** (never a module-internal state), a
   **branch** state reading the verdict cell of tape 0, and a **halt** state. Modules return
   to fixed host states: copier → startup install → anchor; verdict → branch; branch → payload
   emit (verdict `true`) or step install (verdict `false`); payload emit → halt; step → anchor.
4. *Budgets.* All requests are state words of length at most `Q n + 4` with
   `Q n = 2n + 2 + P n`; every module's polynomial budget on its argument is majorised by one
   common `A · (Q n + 5)^D`, which also pays for the fuel machine `x ↦ Nat.bits (R|x|)`
   (`Complexity.polyTimeComputable_unaryPoly R` composed with
   `Turing.FinTM.computesFunInTime_lengthBits`, so that the `find?` range is exactly
   `R|x| + 1`). The loop combinator returns a machine within `c (T n + 1)(R n + 2)`, which
   `PolyExpr.eval_le` puts in the normal form of `Complexity.PolyTimeComputable`.

The clean-module layer and the finite host (steps 2–3: release-flag stop, padding,
forwarding host, first-halt cutting, the copier) live in
`TCSlib.Complexity.Randomized.Build.IterateFindHost`; this file supplies the pure step, the
FP functions of the modules, the budget arithmetic, and the assembly through
`Turing.FinTM.exists_loopFindTM`.

## Main definitions

* `Complexity.IterateFind.step` — the length-guarded step on the state word (definitionally
  `Complexity.guardedStep`).

## Main results

* `Complexity.IterateFind.polyTimeComputable_find` — the loop-level form of the repetition
  lemma: the first accepted orbit point's payload along the guarded orbit of `⟨x, x⟩` is
  polynomial-time computable.
* `Complexity.IterateFind.find?_congr_of_mem` — `List.find?` depends only on the predicate's
  values on the list (used to identify the guarded orbit with `g^[i] x`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1; Theorem 87.3; Algorithms 123.4 and 128.7.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded machines.)
-/

namespace Complexity.IterateFind

open Turing

/-! ### The guarded step on the state word and its FP pieces -/

/-- The length-guarded step on the state word `w = ⟨x, s⟩`: advance to `⟨x, g s⟩` if the new
orbit point fits the bound `P|x|`, else stay (DESIGN.md §2.6, step 1). This is definitionally
`Complexity.guardedStep g P x w`; it is restated here because this file is imported by the
file defining `guardedStep`. -/
def step (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool) : List Bool :=
  if (g (pairSndD w)).length ≤ P.eval x.length then pairEncode x (g (pairSndD w)) else w

/-- The loop invariant used by the machine: the state word *is* a pair `⟨x, s⟩` with
`|s| ≤ P|x|` (stronger than the pure `Complexity.LoopInv`, which also admits malformed
words; the machine needs the well-formedness to bound the word's length). -/
private def Inv (P : PolyExpr) (x w : List Bool) : Prop :=
  ∃ s, w = pairEncode x s ∧ s.length ≤ P.eval x.length

/-- The initial word `⟨x, x⟩` is admissible when `|x| ≤ P|x|`. -/
private theorem inv_init (P : PolyExpr) (x : List Bool) (h0 : x.length ≤ P.eval x.length) :
    Inv P x (pairEncode x x) :=
  ⟨x, rfl, h0⟩

/-- The invariant is closed under the guarded step (the guard keeps the word unchanged when
the new point would be too long). -/
private theorem inv_step (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool)
    (h : Inv P x w) : Inv P x (step g P x w) := by
  obtain ⟨s, rfl, hs⟩ := h
  unfold step
  rw [pairSndD_pairEncode]
  split_ifs with hg
  · exact ⟨g s, rfl, hg⟩
  · exact ⟨s, rfl, hs⟩

/-- The length of an admissible state word is at most `2|x| + 2 + P|x|`. -/
private theorem inv_length (P : PolyExpr) (x w : List Bool) (h : Inv P x w) :
    w.length ≤ 2 * x.length + 2 + P.eval x.length := by
  obtain ⟨s, rfl, hs⟩ := h
  rw [length_pairEncode]
  omega

/-- The verdict word: `w ↦ ⟨[acc (snd w)], w⟩` (the verdict as the first cell, since
`pairEncode [b] w = [b, b, false, true] ++ w`). -/
private def verdictWord (acc : List Bool → Bool) (w : List Bool) : List Bool :=
  pairEncode [acc (pairSndD w)] w

/-- The step on a verdict word: strip the verdict, then take the guarded step on the pair
`⟨x, s⟩` carried by the word, with `x` recovered from the word itself. -/
private def stepWord (g : List Bool → List Bool) (P : PolyExpr) (w' : List Bool) : List Bool :=
  if (g (pairSndD (pairSndD w'))).length ≤ P.eval (pairFstD (pairSndD w')).length then
    pairEncode (pairFstD (pairSndD w')) (g (pairSndD (pairSndD w')))
  else pairSndD w'

/-- The payload of a verdict word: `out` of the orbit point `snd (snd w')`. -/
private def outWord (out : List Bool → List Bool) (w' : List Bool) : List Bool :=
  out (pairSndD (pairSndD w'))

/-- The first cell of a verdict word is the verdict. -/
private theorem verdictWord_head (acc : List Bool → Bool) (w : List Bool) :
    (verdictWord acc w)[0]? = some (acc (pairSndD w)) := by
  simp [verdictWord, pairEncode]

/-- The length of a verdict word. -/
private theorem verdictWord_length (acc : List Bool → Bool) (w : List Bool) :
    (verdictWord acc w).length = w.length + 4 := by
  simp [verdictWord, length_pairEncode]
  omega

/-- On the verdict word of an admissible pair, `stepWord` is the guarded step. -/
private theorem stepWord_verdictWord (g : List Bool → List Bool) (P : PolyExpr)
    (acc : List Bool → Bool) (x s : List Bool) :
    stepWord g P (verdictWord acc (pairEncode x s)) = step g P x (pairEncode x s) := by
  simp [stepWord, verdictWord, step]

/-- On the verdict word of a pair, `outWord` is `out` of the orbit point. -/
private theorem outWord_verdictWord (out : List Bool → List Bool) (acc : List Bool → Bool)
    (x s : List Bool) : outWord out (verdictWord acc (pairEncode x s)) = out s := by
  simp [outWord, verdictWord]

/-- The verdict word is polynomial-time computable (`PolyTimeComputable.pairEncode` of the
test composed with the projection and the identity). -/
private theorem verdictWord_poly {acc : List Bool → Bool}
    (hacc : PolyTimeComputable fun s => [acc s]) : PolyTimeComputable (verdictWord acc) := by
  have h := (hacc.comp polyTimeComputable_pairSndD).pairEncode polyTimeComputable_id
  exact h

/-- The step on verdict words is polynomial-time computable.

**Proof sketch.** `Complexity.polyTimeComputable_ite`: the test
`|g (snd (snd w'))| ≤ P|fst (snd w')|` is `Complexity.polyTimeComputable_lenLe` on the pair
`⟨1^{P|fst (snd w')|}, g (snd (snd w'))⟩`, built with the unary evaluator
`Complexity.polyTimeComputable_unaryPoly P` and `PolyTimeComputable.pairEncode`; the `then`
branch is the pairing of the two projections (with `g`), the `else` branch the projection
`snd`; the Boolean test is identified with the propositional `if` by `decide_eq_true_eq`. -/
private theorem stepWord_poly {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    (P : PolyExpr) : PolyTimeComputable (stepWord g P) := by
  have hs2 : PolyTimeComputable fun w' => pairSndD (pairSndD w') :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hf1 : PolyTimeComputable fun w' => pairFstD (pairSndD w') :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hgg : PolyTimeComputable fun w' => g (pairSndD (pairSndD w')) := hg.comp hs2
  have hun : PolyTimeComputable fun w' =>
      List.replicate (P.eval (pairFstD (pairSndD w')).length) true :=
    (polyTimeComputable_unaryPoly P).comp hf1
  have htest : PolyTimeComputable fun w' =>
      [decide ((g (pairSndD (pairSndD w'))).length ≤ P.eval (pairFstD (pairSndD w')).length)] := by
    have h := polyTimeComputable_lenLe.comp (hun.pairEncode hgg)
    convert h using 1
    funext w'
    simp
  have hthen : PolyTimeComputable fun w' =>
      pairEncode (pairFstD (pairSndD w')) (g (pairSndD (pairSndD w'))) := hf1.pairEncode hgg
  have h := polyTimeComputable_ite htest hthen polyTimeComputable_pairSndD
  convert h using 1
  funext w'
  simp [stepWord]

/-- The payload map on verdict words is polynomial-time computable. -/
private theorem outWord_poly {out : List Bool → List Bool} (hout : PolyTimeComputable out) :
    PolyTimeComputable (outWord out) :=
  hout.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The duplication `x ↦ ⟨x, x⟩` is polynomial-time computable. -/
private theorem dupWord_poly : PolyTimeComputable fun x => pairEncode x x :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairDup

/-! ### Assembly -/

/-- Every polynomial on a bounded request fits the common power. -/
private lemma request_budget (A d D n m : ℕ) (hd : d ≤ D) (hm : m + 1 ≤ n) :
    A * (m + 1) ^ d ≤ A * n ^ D := by
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left hm d).trans (Nat.pow_le_pow_right (by omega) hd)

/-- `List.find?` depends only on the values of the predicate on the list's elements. -/
theorem find?_congr_of_mem {α : Type*} {p q : α → Bool} :
    ∀ l : List α, (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    have ha : p a = q a := h a (List.mem_cons_self ..)
    by_cases hq : q a = true
    · rw [List.find?_cons_of_pos (by rw [ha]; exact hq), List.find?_cons_of_pos hq]
    · rw [List.find?_cons_of_neg (by rw [ha]; exact hq), List.find?_cons_of_neg hq]
      exact find?_congr_of_mem l (fun b hb => h b (List.mem_cons_of_mem a hb))

/-- The final budget arithmetic: the loop combinator's bound `c (T n + 1)(R n + 2)` with
`T n = A (2n + 2 + P n + 5)^D` is in the normal form `C (n + 1)^e` once `P` and `R` are
majorised by `CP (n+1)^cP` and `CR (n+1)^cR`.

**Proof sketch.** `2n + 7 + P n ≤ (CP + 7)(n+1)^{cP+1}` (both `7(n+1)` and `CP (n+1)^{cP}`
are at most the corresponding multiples of `(n+1)^{cP+1}`); raise to the `D`-th power
(`Nat.pow_le_pow_left`, `Nat.mul_pow`, `Nat.pow_mul`), absorb the `+ 1` with
`1 ≤ (n+1)^{(cP+1)D}`, bound `R n + 2 ≤ (CR + 2)(n+1)^{cR}` likewise, and multiply
(`Nat.mul_le_mul`, `Nat.pow_add`). -/
private lemma final_bound (c A D CP cP CR cR n Pn Rn : ℕ)
    (hP : Pn ≤ CP * (n + 1) ^ cP) (hR : Rn ≤ CR * (n + 1) ^ cR) :
    c * (A * (2 * n + 2 + Pn + 5) ^ D + 1) * (Rn + 2) ≤
      c * (A * (CP + 7) ^ D + 1) * (CR + 2) * (n + 1) ^ ((cP + 1) * D + cR) := by
  have hpos : 0 < n + 1 := Nat.succ_pos n
  have h1 : 2 * n + 2 + Pn + 5 ≤ (CP + 7) * (n + 1) ^ (cP + 1) := by
    have ha : n + 1 ≤ (n + 1) ^ (cP + 1) := by
      simpa using Nat.pow_le_pow_right hpos (show 1 ≤ cP + 1 by omega)
    have hb : (n + 1) ^ cP ≤ (n + 1) ^ (cP + 1) := Nat.pow_le_pow_right hpos (by omega)
    have hc := Nat.mul_le_mul_left CP hb
    calc 2 * n + 2 + Pn + 5 ≤ 7 * (n + 1) + CP * (n + 1) ^ cP := by omega
      _ ≤ 7 * (n + 1) ^ (cP + 1) + CP * (n + 1) ^ (cP + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left 7 ha) hc
      _ = (CP + 7) * (n + 1) ^ (cP + 1) := by ring
  have h2 : (2 * n + 2 + Pn + 5) ^ D ≤ (CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D) := by
    calc (2 * n + 2 + Pn + 5) ^ D ≤ ((CP + 7) * (n + 1) ^ (cP + 1)) ^ D :=
          Nat.pow_le_pow_left h1 D
      _ = (CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D) := by rw [Nat.mul_pow, ← Nat.pow_mul]
  have hone : 1 ≤ (n + 1) ^ ((cP + 1) * D) := Nat.one_le_pow _ _ hpos
  have h3 : A * (2 * n + 2 + Pn + 5) ^ D + 1 ≤
      (A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D) := by
    calc A * (2 * n + 2 + Pn + 5) ^ D + 1
        ≤ A * ((CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D)) + (n + 1) ^ ((cP + 1) * D) :=
          Nat.add_le_add (Nat.mul_le_mul_left A h2) hone
      _ = (A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D) := by ring
  have h4 : Rn + 2 ≤ (CR + 2) * (n + 1) ^ cR := by
    have hone' : 1 ≤ (n + 1) ^ cR := Nat.one_le_pow _ _ hpos
    calc Rn + 2 ≤ CR * (n + 1) ^ cR + 2 * (n + 1) ^ cR := by omega
      _ = (CR + 2) * (n + 1) ^ cR := by ring
  calc c * (A * (2 * n + 2 + Pn + 5) ^ D + 1) * (Rn + 2)
      ≤ c * ((A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D)) * ((CR + 2) * (n + 1) ^ cR) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left c h3) h4
    _ = c * (A * (CP + 7) ^ D + 1) * (CR + 2) * (n + 1) ^ ((cP + 1) * D + cR) := by
        rw [Nat.pow_add]; ring

/-- **The loop-level repetition lemma.** Let `g` be a polynomial-time step, `acc` a
polynomial-time test, `out` a polynomial-time payload map, and `R, P` syntactic polynomials
with `|g^[i] x| ≤ P|x|` for `i ≤ R|x|`. Then the function returning `out` of the orbit point
of the first index `i ≤ R|x|` at which `acc` accepts the second component of the `i`-fold
guarded step `Complexity.IterateFind.step g P x` from `⟨x, x⟩` (`[]` if none) is
polynomial-time computable. This is the machine behind
`Complexity.polyTimeComputable_iterateFind` [PS10, Algorithm 38.5, Theorem 35.1]; the pure
identification of the guarded orbit with `g^[i] x` is done there.

**Proof sketch.** Instance of `Turing.FinTM.exists_loopFindTM` for the host `hostTM` over
the five clean modules (the copier, and `clean_install`/`clean_emit` of `x ↦ ⟨x, x⟩`,
`verdictWord acc`, `stepWord g P`, `outWord out`), with anchor `inl 0`, invariant `Inv P`,
step `step g P`, acceptance `acc ∘ snd`, payload `out ∘ snd`, start word `⟨x, x⟩`. The fuel
machine computes `Nat.bits (R|x|)` (`polyTimeComputable_unaryPoly R` composed with
`computesFunInTime_lengthBits`). `hstart`: the copier (`copy_clean`, `host_call`) then the
startup install (`host_clean`) reach the anchor seam with `⟨x, x⟩` in `2|x| + 2 + t_S` steps
with no earlier anchor visit. `hround`: from the anchor seam with an admissible word `⟨x, s⟩`,
the dispatch step, the verdict call, the branch step (`host_branch`), then either the payload
call and the halt step (`host_halt`) — state `none`, output `out s` — or the step call
returning to the anchor seam with `step g P x ⟨x, s⟩` (`stepWord_verdictWord`); the anchor
guard is `guard_add` over the segments. All requests have length at most `2|x| + 2 + P|x| + 4`,
so every call fits the common budget `T n = A (2n + 2 + P n + 5)^D` (`request_budget`), and
`final_bound` puts the combinator's bound `c (T n + 1)(R n + 2)` in normal form. -/
theorem polyTimeComputable_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find?
          (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x x)))) with
      | some i => out (pairSndD ((step g P x)^[i] (pairEncode x x)))
      | none => [] := by
  obtain ⟨S, aS, dS, hS⟩ := clean_install dupWord_poly
  obtain ⟨V, aV, dV, hV⟩ := clean_install (verdictWord_poly hacc)
  obtain ⟨I, aI, dI, hI⟩ := clean_install (stepWord_poly hg P)
  obtain ⟨E, aE, dE, hE⟩ := clean_emit (outWord_poly hout)
  obtain ⟨F, aF, dF, hF⟩ : PolyTimeComputable fun x => Nat.bits (R.eval x.length) := by
    have h := (polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits).comp
      (polyTimeComputable_unaryPoly R)
    convert h using 1
    funext x
    simp
  let M : Fin 5 → FinTM Bool := fun i => match i.val with
    | 0 => copyTM | 1 => S | 2 => V | 3 => I | _ => E
  let K := S.k + V.k + I.k + E.k
  have hk : ∀ i, (M i).k ≤ K + 1 := by
    intro i; fin_cases i <;> simp [M, K, copyTM] <;> omega
  let H := hostTM M K hk
  let anchor : H.State := .inl 0
  let D := dS + dV + dI + dE + dF + 1
  let A := aS + aV + aI + aE + aF + 5
  let pow (n : ℕ) := (2 * n + 2 + P.eval n + 5) ^ D
  let T (n : ℕ) := A * pow n
  have hpow (n : ℕ) : n + 1 ≤ pow n := by
    have h := Nat.pow_le_pow_right (show 0 < 2 * n + 2 + P.eval n + 5 by omega)
      (show 1 ≤ D by dsimp [D]; omega)
    simp only [Nat.pow_one] at h
    exact (by omega : n + 1 ≤ 2 * n + 2 + P.eval n + 5).trans h
  have hret0 : hostRet M 0 = hostEntry M 1 := rfl
  have hret1 : hostRet M 1 = anchor := rfl
  have hret2 : hostRet M 2 = .inl 1 := rfl
  have hret3 : hostRet M 3 = anchor := rfl
  have hret4 : hostRet M 4 = .inl 2 := rfl
  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ v < t, (H.tm.runFrom (H.tm.initCfg x) v).state ≠ some anchor) ∧
      H.tm.runFrom (H.tm.initCfg x) t = Cfg.ofWords anchor (stateWord H.k (pairEncode x x)) := by
    intro x
    obtain ⟨hcg, hce⟩ := copy_clean x
    obtain ⟨hcGuard, hcEnd⟩ := host_call M K hk 0 (by simp [M, copyTM]) x [] x [] [] (0 : Fin 2)
      (2 * x.length + 2) hcg (by simpa using hce)
    have hi : H.tm.initCfg x = Cfg.ofWords (hostEntry M 0) (stateWord (K + 1) []) := by
      refine Cfg.ext rfl rfl ?_ rfl rfl
      funext i z
      simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord]
    change H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 0) (stateWord (K + 1) []))
      (2 * x.length + 2) = Cfg.ofWords (hostRet M 0) (stateWord (K + 1) x) at hcEnd
    rw [hret0] at hcEnd
    obtain ⟨ts, hspos, hst, hsGuard, hsEnd⟩ := host_clean M K hk 1
      (fun x => pairEncode x x) (fun _ => []) (fun n => aS * (n + 1) ^ dS)
      (by simpa [M] using hS) x x []
    change H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 1) (stateWord (K + 1) x)) ts =
      Cfg.ofWords (hostRet M 1) (stateWord (K + 1) (pairEncode x x)) at hsEnd
    rw [hret1] at hsEnd
    have hsB := request_budget aS dS D (2 * x.length + 2 + P.eval x.length + 5) x.length
      (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    refine ⟨2 * x.length + 2 + ts, ?_, ?_, ?_⟩
    · dsimp only [T, A, pow]
      simp only [Nat.add_mul]
      dsimp only [pow] at hp
      omega
    · rw [hi]
      exact guard_add H.tm anchor _ _ _ ts hcGuard hcEnd hsGuard
    · rw [hi, MultiTapeTM.runFrom_add, hcEnd, hsEnd]
      rfl
  have hround : ∀ x w : List Bool, Inv P x w → ∃ t, 0 < t ∧ t ≤ T x.length ∧
      (∀ t', 0 < t' → t' < t →
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t').state
          ≠ some anchor) ∧
      if acc (pairSndD w) then
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).state = none ∧
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).output =
          out (pairSndD w)
      else
        H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t =
          Cfg.ofWords anchor (stateWord H.k (step g P x w)) := by
    intro x w hw
    obtain ⟨s, rfl, hs⟩ := hw
    have hwlen : (pairEncode x s).length ≤ 2 * x.length + 2 + P.eval x.length := by
      rw [length_pairEncode]; omega
    have hw'len : (verdictWord acc (pairEncode x s)).length =
        (pairEncode x s).length + 4 := verdictWord_length acc _
    have hpow' := hpow x.length
    -- the dispatch, the verdict call, the branch
    have hdisp := host_dispatch M K hk x (pairEncode x s)
    obtain ⟨tv, hvpos, hvt, hvGuard, hvEnd⟩ := host_clean M K hk 2 (verdictWord acc)
      (fun _ => []) (fun n => aV * (n + 1) ^ dV) (by simpa [M] using hV) x (pairEncode x s) []
    change H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 2) (stateWord (K + 1)
      (pairEncode x s))) tv = Cfg.ofWords (hostRet M 2) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s))) at hvEnd
    rw [hret2] at hvEnd
    have hbr := host_branch M K hk x (acc s) (verdictWord acc (pairEncode x s))
      (by rw [verdictWord_head, pairSndD_pairEncode])
    have hvB := request_budget aV dV D (2 * x.length + 2 + P.eval x.length + 5)
      (pairEncode x s).length (by dsimp [D]; omega) (by omega)
    have hseg : H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 2)
        (stateWord (K + 1) (pairEncode x s))) (tv + 1) =
        Cfg.ofWords (hostEntry M (if acc s then 4 else 3))
          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) := by
      rw [MultiTapeTM.runFrom_succ_eq_step', hvEnd, hbr]
    have hsegGuard : ∀ v < tv + 1, (H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 2)
        (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
      refine guard_add H.tm anchor _ _ tv 1 hvGuard hvEnd ?_
      intro v hv
      have hv0 : v = 0 := by omega
      subst hv0
      simp [Cfg.ofWords, anchor]
    by_cases hb : acc s = true
    · -- accepting round: the payload call, then the halt
      rw [if_pos hb] at hseg
      obtain ⟨te, hepos, het, heGuard, heEnd⟩ := host_clean M K hk 4 id (outWord out)
        (fun n => aE * (n + 1) ^ dE) (by simpa [M] using hE) x
        (verdictWord acc (pairEncode x s)) []
      change H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 4) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s)))) te = {Cfg.ofWords (hostRet M 4) (stateWord (K + 1)
          (verdictWord acc (pairEncode x s))) with
            output := [] ++ outWord out (verdictWord acc (pairEncode x s))} at heEnd
      rw [hret4, List.nil_append, outWord_verdictWord] at heEnd
      have hhalt := host_halt M K hk x (verdictWord acc (pairEncode x s)) (out s)
      have heB := request_budget aE dE D (2 * x.length + 2 + P.eval x.length + 5)
        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 2)
          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + te + 1) =
          {Cfg.ofWords (input := x) (.inl 2 : HostState M) (stateWord (K + 1)
            (verdictWord acc (pairEncode x s))) with state := none, output := out s} := by
        rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hseg, heEnd, hhalt]
      have hallGuard : ∀ v < tv + 1 + te + 1, (H.tm.runFrom (Cfg.ofWords (input := x)
          (hostEntry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
        refine guard_add H.tm anchor _ {Cfg.ofWords (input := x) (.inl 2 : HostState M)
          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) with output := out s}
          (tv + 1 + te) 1 ?_ ?_ ?_
        · exact guard_add H.tm anchor _ _ (tv + 1) te hsegGuard hseg heGuard
        · rw [MultiTapeTM.runFrom_add, hseg, heEnd]
        · intro v hv
          have hv0 : v = 0 := by omega
          subst hv0
          simp [Cfg.ofWords, anchor]
      refine ⟨tv + 1 + te + 1 + 1, by omega, ?_, ?_, ?_⟩
      · dsimp only [T, A, pow]
        simp only [Nat.add_mul]
        dsimp only [pow] at hpow'
        omega
      · intro v hv hvt
        have hvform : v = (v - 1) + 1 := by omega
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
          (pairEncode x s))) v).state ≠ some anchor
        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
        exact hallGuard (v - 1) (by omega)
      · rw [pairSndD_pairEncode, if_pos hb]
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + te + 1 + 1)).state = none ∧
          (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + te + 1 + 1)).output = out s
        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
        exact ⟨rfl, rfl⟩
    · -- advancing round: the step call returns to the anchor
      rw [if_neg hb] at hseg
      obtain ⟨ti, hipos, hit, hiGuard, hiEnd⟩ := host_clean M K hk 3 (stepWord g P)
        (fun _ => []) (fun n => aI * (n + 1) ^ dI) (by simpa [M] using hI) x
        (verdictWord acc (pairEncode x s)) []
      change H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 3) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s)))) ti = Cfg.ofWords (hostRet M 3) (stateWord (K + 1)
          (stepWord g P (verdictWord acc (pairEncode x s)))) at hiEnd
      rw [hret3, stepWord_verdictWord] at hiEnd
      have hiB := request_budget aI dI D (2 * x.length + 2 + P.eval x.length + 5)
        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 2)
          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + ti) =
          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s))) := by
        rw [MultiTapeTM.runFrom_add, hseg, hiEnd]
      have hallGuard : ∀ v < tv + 1 + ti, (H.tm.runFrom (Cfg.ofWords (input := x)
          (hostEntry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor :=
        guard_add H.tm anchor _ _ (tv + 1) ti hsegGuard hseg hiGuard
      refine ⟨tv + 1 + ti + 1, by omega, ?_, ?_, ?_⟩
      · dsimp only [T, A, pow]
        simp only [Nat.add_mul]
        dsimp only [pow] at hpow'
        omega
      · intro v hv hvt
        have hvform : v = (v - 1) + 1 := by omega
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
          (pairEncode x s))) v).state ≠ some anchor
        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
        exact hallGuard (v - 1) (by omega)
      · rw [pairSndD_pairEncode, if_neg hb]
        change H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + ti + 1) =
          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s)))
        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
  have hFuel : F.ComputesFunInTime (fun x => Nat.bits (R.eval x.length)) T := by
    intro x
    apply (hF x).mono
    have h := request_budget aF dF D (2 * x.length + 2 + P.eval x.length + 5) x.length
      (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    dsimp only [T, A, pow]
    simp only [Nat.add_mul]
    dsimp only [pow] at hp
    omega
  obtain ⟨L, c, hL⟩ := FinTM.exists_loopFindTM H F anchor (Inv P) (step g P)
    (fun _ w => acc (pairSndD w)) (fun _ w => out (pairSndD w)) (fun x => pairEncode x x)
    (fun n => R.eval n) T hFuel
    (fun x => inv_init P x (by simpa using horbit x 0 (Nat.zero_le _)))
    (fun x w h => inv_step g P x w h) hstart hround
  obtain ⟨CP, cP, hCP⟩ := P.eval_le
  obtain ⟨CR, cR, hCR⟩ := R.eval_le
  refine ⟨L, c * (A * (CP + 7) ^ D + 1) * (CR + 2), (cP + 1) * D + cR, fun x => (hL x).mono ?_⟩
  exact final_bound c A D CP cP CR cR x.length (P.eval x.length) (R.eval x.length)
    (hCP _) (hCR _)

end Complexity.IterateFind
