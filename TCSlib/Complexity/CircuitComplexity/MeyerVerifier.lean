/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.MeyerVerifierGlue

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: the `Σ₂ᵖ` verifier

The `∀`-block of the `Σ₂ᵖ` formula in the proof of [AB09, Thm 6.20]: given the input `x`
and a guessed circuit description `D` (supposed to decide the tableau language
`Complexity.Meyer.Tab M` at the query length of `x`), a *counterexample* is a
verifier instance — a time word `t`, an offset word `a`, a unary input offset `j` with a
padding word — at which some local check fails. The checks query `D` through the
circuit evaluator `CVAL` ([AB09]'s "`T(x, C(i), C(i₁), …)` is a polynomial-time TM
checking these conditions").

## The checks

Writing `⟦sel, t, a⟧` for the guessed answer at selector `sel`, time `t`, offset `a`
(little-endian words of the width `W = Cw (|x|+1)^cw`), the checks are (`goodF`):

* *initial row*: state `(q₀, empty)` at time `0`, blank work cells, input cells `x̂`;
* *`-0 = +0`*: both codes of offset `0` agree;
* *step*: if the claimed state and reads at time `t` are `(σ, ρ)`, then the state, every
  work-tape edge `(e, e + 1)` and every input edge at time `t + 1` follow the local rule
  (`ruleS`, `ruleW`, `ruleI` of `MeyerTableau.lean`), including the input boundary;
* *final row*: at time `2^W - 1` the state is halted with output `[true]`.

Each check is a Boolean function (`goodF`) of finitely many *atoms* (`Atom`): `CVAL`
queries, length tests and one-pass tests; so the counterexample language is in `P`
(`badLang_mem_P`) by `mem_P_of_atoms`.

## Main definitions

* `Complexity.Meyer.Atom`, `Complexity.Meyer.evalAtom` — the atoms of a verifier input.
* `Complexity.Meyer.Check`, `Complexity.Meyer.goodF` — the checks.
* `Complexity.Meyer.badLang`, `Complexity.Meyer.innerLang`.

## Main results

* `Complexity.Meyer.evalAtom_mem_P`, `Complexity.Meyer.badLang_mem_P`,
  `Complexity.Meyer.innerLang_mem_coNP`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing Complexity.PolyHierarchy BoolCircuit BoolCircuit.CktSatReduction
  Complexity.KarpLipton Complexity.TimeHierarchy

variable (Cw cw : ℕ)

/-! ### Atoms -/

/-- **The atoms** of a verifier input: guessed answers `⟦sel, T, A⟧`, the range
conditions on the instance words, and the input bit `x[j]` (through `CVAL`). -/
inductive Atom (S : Type) (k : ℕ) where
  | ans : TabSel S k → TW → AW → Atom S k
  | lenAll | tNotOnes | aNotOnes | aZero | jZero | jLtN | jLeN | jEqN1 | xbit
  deriving DecidableEq, Fintype

variable (M : FinTM Bool)

/-- Membership in a complement language. -/
@[simp] theorem lang_mem_compl (L : Language Bool) (z : List Bool) : z ∈ Lᶜ ↔ z ∉ L := Iff.rfl

/-- Membership in a language given by a predicate. -/
@[simp] theorem lang_mem_setOf (p : List Bool → Prop) (z : List Bool) :
    z ∈ ({z | p z} : Language Bool) ↔ p z := Iff.rfl

open Classical in
/-- The guessed answer of the description `D` for a query. -/
noncomputable def ansD (D : List Bool) (sel : Sel M) (T A x : List Bool) : Bool :=
  decide (pairEncode D (query (encodeSel sel) T A x) ∈ CVAL)

open Classical in
/-- **The value of an atom** on a verifier input. -/
noncomputable def evalAtom : Atom M.State M.k → List Bool → Bool
  | .ans sel T A, z => ansD M (vD z) sel (twd Cw cw T z) (awd Cw cw A z) (vx z)
  | .lenAll, z => decide ((vt z).length = wd Cw cw (vx z).length ∧
      (va z).length = wd Cw cw (vx z).length ∧ (vj z).length ≤ (vx z).length + 1 ∧
      (bjw z).length = wd Cw cw (vx z).length)
  | .tNotOnes, z => decide ((incFixed (vt z)).getD [] ≠ [])
  | .aNotOnes, z => decide ((incFixed (va z)).getD [] ≠ [])
  | .aZero, z => decide (va z = List.replicate (va z).length false)
  | .jZero, z => decide ((vj z).length = 0)
  | .jLtN, z => decide ((vj z).length < (vx z).length)
  | .jLeN, z => decide ((vj z).length ≤ (vx z).length)
  | .jEqN1, z => decide ((vj z).length = (vx z).length + 1)
  | .xbit, z => decide (pairEncode (idxDesc (vx z).length (vj z).length) (vx z) ∈ CVAL)

/-- The `true`-bits of a word, as a transducer. -/
def trues (u : List Bool) : List Bool :=
  transduce (fun _ _ => ()) (fun _ b => if b then some true else none) () u

/-- A word has no `true` bits iff it is all `false`. -/
theorem trues_eq_nil (u : List Bool) : trues u = [] ↔ u = List.replicate u.length false := by
  induction u with
  | nil => simp [trues, transduce]
  | cons b u ih =>
    cases b <;> simp [trues, transduce, List.replicate_succ] at ih ⊢
    exact ih

/-- A length equality of polynomial-time strings, as a test. -/
theorem lenEq_test {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) :
    ({z | decide ((f z).length = (g z).length) = true} : Language Bool) ∈ P := by
  simpa using lenEq_preimage_mem_P hf hg

/-- A length inequality of polynomial-time strings, as a test. -/
theorem lenLe_test {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) :
    ({z | decide ((g z).length ≤ (f z).length) = true} : Language Bool) ∈ P := by
  simpa using lenLe_preimage_mem_P hf hg

/-- **Every atom is decidable in polynomial time.**

**Proof sketch.** Each atom is a `CVAL` query on a polynomial-time constructible string
(`pt_query`, `pt_twd`, `pt_awd`, the index description), a length comparison of
polynomial-time strings (`lenEq_test`, `lenLe_test`), or the emptiness of a transducer's
output, all in `P`. -/
theorem evalAtom_mem_P (a : Atom M.State M.k) :
    ({z | evalAtom Cw cw M a z = true} : Language Bool) ∈ P := by
  have hW := unaryPT_poly Cw cw pt_vx
  have hW' : PolyTimeComputable (fun z => List.replicate (wd Cw cw (vx z).length) true) := by
    simpa [wd] using hW
  cases a with
  | ans sel T A =>
    have h := preimage_mem_P CVAL_mem_P
      (pt_vD.pairEncode (pt_query (encodeSel sel) (pt_twd Cw cw T) (pt_awd Cw cw A) pt_vx))
    convert h using 1
    ext z; simp [evalAtom, ansD]
  | lenAll =>
    have h1 := lenEq_test pt_vt hW'
    have h2 := lenEq_test pt_va hW'
    have h3 := lenLe_test ((polyTimeComputable_prepend [true]).comp pt_vx) pt_vj
    have h4 := lenEq_test pt_bjw hW'
    have := inter_mem_P h1 (inter_mem_P h2 (inter_mem_P h3 h4))
    convert this using 1
    ext z; simp [evalAtom]
  | tNotOnes =>
    have h := compl_mem_P (lenLe_test (polyTimeComputable_const []) (pt_inc.comp pt_vt))
    convert h using 1
    ext z
    change _ ↔ ¬ (_ = true)
    simp [evalAtom]
  | aNotOnes =>
    have h := compl_mem_P (lenLe_test (polyTimeComputable_const []) (pt_inc.comp pt_va))
    convert h using 1
    ext z
    change _ ↔ ¬ (_ = true)
    simp [evalAtom]
  | aZero =>
    have ht : PolyTimeComputable trues := polyTimeComputable_transduce _ _ _
    have h := lenLe_test (polyTimeComputable_const []) (ht.comp pt_va)
    convert h using 1
    ext z
    simp only [evalAtom, decide_eq_true_eq, Set.mem_setOf_eq, List.length_nil,
      Nat.le_zero, List.length_eq_zero_iff]
    exact (trues_eq_nil (va z)).symm
  | jZero =>
    have h := lenLe_test (polyTimeComputable_const []) pt_vj
    convert h using 1
    ext z; simp [evalAtom]
  | jLtN =>
    have h := compl_mem_P (lenLe_test pt_vj pt_vx)
    convert h using 1
    ext z
    change _ ↔ ¬ (_ = true)
    simp [evalAtom]
  | jLeN =>
    have h := lenLe_test pt_vx pt_vj
    convert h using 1
  | jEqN1 =>
    have h := lenEq_test pt_vj ((polyTimeComputable_prepend [true]).comp pt_vx)
    convert h using 1
  | xbit =>
    have hd : PolyTimeComputable (fun z => idxDesc (vx z).length (vj z).length) := by
      have := PolyTimeComputable.append (polyTimeComputable_unary.comp pt_vx)
        ((polyTimeComputable_prepend [false, false]).comp
          (PolyTimeComputable.append (polyTimeComputable_unary.comp pt_vj)
            (polyTimeComputable_const [false])))
      convert this using 1
    have h := preimage_mem_P CVAL_mem_P (hd.pairEncode pt_vx)
    convert h using 1
    ext z; simp [evalAtom]

/-! ### The checks -/

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The local checks** of the verifier, with their finite parameters: a claimed state
`σ`, claimed reads `ρ`, a work tape `h`, an edge sign `s`, a selector bit `b`. -/
inductive Check (S : Type) (k : ℕ) where
  | initSt : Option S → OutReg → Check S k
  | initW : Fin k → Bool → Bool → Check S k
  | initI : Bool → Bool → Check S k
  | negZero : Option (Fin k) → Bool → Check S k
  | stepSt : Option S × OutReg → Option Bool × (Fin k → Option Bool) → Option S × OutReg →
      Check S k
  | stepW : Option S × OutReg → Option Bool × (Fin k → Option Bool) → Fin k → Bool → Check S k
  | stepI : Option S × OutReg → Option Bool × (Fin k → Option Bool) → Bool → Check S k
  | bdryI : Option S × OutReg → Option Bool × (Fin k → Option Bool) → Check S k
  | final : Check S k
  deriving DecidableEq, Fintype

section checks

variable (v : Atom M.State M.k → Bool)

/-- The guessed symbol at tape `τ`, sign `s`, time `T`, offset `A`. -/
def symvA (τ : Option (Fin M.k)) (s : Bool) (T : TW) (A : AW) : Option Bool :=
  if v (.ans (.sym τ s true) T A) then none else some (v (.ans (.sym τ s false) T A))

/-- The guessed state claim at time `T`. -/
def stA (σ : Option M.State × OutReg) (T : TW) : Bool := v (.ans (.st σ.1 σ.2) T .a0)

/-- The guesses at time `T` claim the state `σ` and the reads `ρ`. -/
def claims (T : TW) (σ : Option M.State × OutReg) (ρ : Rd M) : Bool :=
  stA M v σ T && decide (symvA M v none false T .a0 = ρ.1) &&
    decide (∀ h, symvA M v (some h) false T .a0 = ρ.2 h)

/-- The guessed initial input cell at sign `s` and unary offset `j`: blank on the
negative side, `x[j]` (blank beyond `x`) on the nonnegative side. -/
def xinV (s : Bool) : Option Bool :=
  if s && !(v .jZero) then none else if v .jLtN then some (v .xbit) else none

/-- The work-tape step check on the edge of sign `s`. -/
def workOK (σ : Option M.State × OutReg) (ρ : Rd M) (h : Fin M.k) (s : Bool) : Bool :=
  let c₁ : AW := if s then .an else .ac
  let c₂ : AW := if s then .ac else .an
  let E0 := !s && v .aZero
  let E1 := s && v .aZero
  match σ.1 with
  | none => decide (symvA M v (some h) s .tn c₁ = symvA M v (some h) s .tc c₁)
  | some q =>
    let ws : Option Bool := wsym ((M.tm.tr q ρ.1 ρ.2).workTapes h).1 (ρ.2 h)
    match ((M.tm.tr q ρ.1 ρ.2).workTapes h).2 with
    | .pos => decide (symvA M v (some h) s .tn c₁ =
        if E1 then ws else symvA M v (some h) s .tc c₂)
    | .neg => decide (symvA M v (some h) s .tn c₂ =
        if E0 then ws else symvA M v (some h) s .tc c₁)
    | .zero => decide (symvA M v (some h) s .tn c₁ =
        if E0 then ws else symvA M v (some h) s .tc c₁)

/-- The guessed clamping condition of an input move `m`. -/
def clampedA (ρ : Rd M) (m : SignType) : Bool :=
  decide (ρ.1 = none) && decide (symvA M v none (decide (m = .neg)) .tc .a1 = none)

/-- The input step check on the edge of sign `s`. -/
def inOK (σ : Option M.State × OutReg) (ρ : Rd M) (s : Bool) : Bool :=
  let c₁ : AW := if s then .aj1 else .aj
  let c₂ : AW := if s then .aj else .aj1
  let same := decide (symvA M v none s .tn c₁ = symvA M v none s .tc c₁) &&
    decide (symvA M v none s .tn c₂ = symvA M v none s .tc c₂)
  match σ.1 with
  | none => same
  | some q =>
    let m := (M.tm.tr q ρ.1 ρ.2).inputTape
    match m with
    | .zero => same
    | .pos => if clampedA M v ρ m then same
        else decide (symvA M v none s .tn c₁ = symvA M v none s .tc c₂)
    | .neg => if clampedA M v ρ m then same
        else decide (symvA M v none s .tn c₂ = symvA M v none s .tc c₁)

/-- The input boundary check: an unclamped outward move blanks the outermost cell. -/
def bdOK (σ : Option M.State × OutReg) (ρ : Rd M) : Bool :=
  match σ.1 with
  | none => true
  | some q =>
    let m := (M.tm.tr q ρ.1 ρ.2).inputTape
    match m with
    | .zero => true
    | .pos => clampedA M v ρ m || decide (symvA M v none false .tn .aj = none)
    | .neg => clampedA M v ρ m || decide (symvA M v none true .tn .aj = none)

/-- **The checks** as Boolean functions of the atoms. -/
def goodF : Check M.State M.k → Bool
  | .initSt σ r => v (.ans (.st σ r) .t0 .a0) == decide ((σ, r) = (some M.tm.q₀, OutReg.empty))
  | .initW h s b => v (.ans (.sym (some h) s b) .t0 .ac) == symBit b none
  | .initI s b => v (.ans (.sym none s b) .t0 .aj) == symBit b (xinV M v s)
  | .negZero τ b => v (.ans (.sym τ true b) .tc .a0) == v (.ans (.sym τ false b) .tc .a0)
  | .stepSt σ ρ σ' => !(v .tNotOnes && claims M v .tc σ ρ) ||
      (v (.ans (.st σ'.1 σ'.2) .tn .a0) == decide (σ' = ruleS M σ ρ))
  | .stepW σ ρ h s => !(v .tNotOnes && v .aNotOnes && claims M v .tc σ ρ) ||
      workOK M v σ ρ h s
  | .stepI σ ρ s => !(v .tNotOnes && v .jLeN && claims M v .tc σ ρ) ||
      inOK M v σ ρ s
  | .bdryI σ ρ => !(v .tNotOnes && v .jEqN1 && claims M v .tc σ ρ) || bdOK M v σ ρ
  | .final => v (.ans (.st none (.one true)) .t1 .a0)

/-- **A counterexample**: the instance words are in range and some check fails. -/
def badF : Bool := v .lenAll && !(decide (∀ π : Check M.State M.k, goodF M v π = true))

end checks

/-- **The counterexample language**: verifier inputs `⟨⟨x, U⟩, ⟨⟨t, a⟩, ⟨j, p⟩⟩⟩` that
are counterexamples to the checks for the description padded in `U`. -/
noncomputable def badLang : Language Bool := {z | badF M (fun a => evalAtom Cw cw M a z) = true}

/-- **The counterexample language is in `P`.**

**Proof sketch.** It is a Boolean function of finitely many atoms, each in `P`
(`evalAtom_mem_P`); apply `mem_P_of_atoms`. -/
theorem badLang_mem_P : badLang Cw cw M ∈ P :=
  mem_P_of_atoms (fun a z => evalAtom Cw cw M a z) (evalAtom_mem_P Cw cw M) (badF M)

/-! ### The inner `coNP` language -/

/-- Atoms depend only on the coordinates. -/
theorem evalAtom_congr {z z' : List Bool} (hx : vx z = vx z') (hD : vD z = vD z')
    (ht : vt z = vt z') (ha : va z = va z') (hj : vj z = vj z') (hp : vp z = vp z')
    (a : Atom M.State M.k) : evalAtom Cw cw M a z = evalAtom Cw cw M a z' := by
  have hb : bjw z = bjw z' := by simp [bjw, hj, hp]
  cases a with
  | ans sel T A =>
    have hT : twd Cw cw T z = twd Cw cw T z' := by cases T <;> simp [twd, ht, hx]
    have hA : awd Cw cw A z = awd Cw cw A z' := by cases A <;> simp [awd, ha, hx, hb]
    simp [evalAtom, hT, hA, hD, hx]
  | _ => simp [evalAtom, hx, ht, ha, hj, hb]

/-- **The inner language of the `Σ₂ᵖ` formula**: the pairs `⟨x, U⟩` admitting no
counterexample. -/
noncomputable def innerLang : Language Bool := {w | ∀ v, pairEncode w v ∉ badLang Cw cw M}

/-- **The inner language is in `coNP`.**

**Proof sketch.** Its complement is `{w | ∃ v, ⟨w, v⟩ ∈ badLang}` with `badLang ∈ P`; a
counterexample can be re-encoded from its four coordinates, which the range condition
bounds by the width `W ≤ Cw (|w|+1)^cw` and `|x| + 1`, so certificates of length
`(7 Cw + 12)(|w| + 1)^{cw+1}` suffice (`mem_NP_iff_exists_length_le`). -/
theorem innerLang_mem_coNP : innerLang Cw cw M ∈ coNP := by
  show (innerLang Cw cw M)ᶜ ∈ NP
  refine mem_NP_iff_exists_length_le.mpr ⟨7 * Cw + 12, cw + 1, badLang Cw cw M,
    badLang_mem_P Cw cw M, fun w => ?_⟩
  constructor
  · intro hw
    have hw' : ¬ ∀ v, pairEncode w v ∉ badLang Cw cw M := hw
    push_neg at hw'
    obtain ⟨v, hv⟩ := hw'
    set z := pairEncode w v with hz
    set u := pairEncode (pairEncode (vt z) (va z)) (pairEncode (vj z) (vp z)) with hu
    have hcoord : ∀ a, evalAtom Cw cw M a (pairEncode w u) = evalAtom Cw cw M a z := by
      intro a
      apply evalAtom_congr <;> simp [vx, vD, vt, va, vj, vp, z, u]
    have hbad : pairEncode w u ∈ badLang Cw cw M := by
      change badF M _ = true
      rw [show (fun a => evalAtom Cw cw M a (pairEncode w u)) = fun a => evalAtom Cw cw M a z
        from funext hcoord]
      exact hv
    refine ⟨u, ?_, hbad⟩
    -- the length bound, from the range condition of the counterexample
    have hlen : evalAtom Cw cw M .lenAll z = true := by
      have := hv
      change (evalAtom Cw cw M .lenAll z && _) = true at this
      simp only [Bool.and_eq_true] at this
      exact this.1
    simp only [evalAtom, decide_eq_true_eq] at hlen
    obtain ⟨h1, h2, h3, h4⟩ := hlen
    have h4' : (vp z).length ≤ wd Cw cw (vx z).length := by
      rw [← h4]; simp [bjw]
    have hn : (vx z).length ≤ w.length := by
      simp only [vx, z, pairFstD_pairEncode]; exact length_pairFstD_le w
    have hW : wd Cw cw (vx z).length ≤ Cw * (w.length + 1) ^ (cw + 1) := by
      simp only [wd]
      calc Cw * ((vx z).length + 1) ^ cw ≤ Cw * (w.length + 1) ^ cw :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        _ ≤ Cw * (w.length + 1) ^ (cw + 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hone : w.length + 1 ≤ (w.length + 1) ^ (cw + 1) := by
      calc w.length + 1 = (w.length + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [u, length_pairEncode]
    have : (7 * Cw + 12) * (w.length + 1) ^ (cw + 1) =
        7 * (Cw * (w.length + 1) ^ (cw + 1)) + 12 * (w.length + 1) ^ (cw + 1) := by ring
    rw [this]
    omega
  · rintro ⟨u, -, hu⟩ hin
    exact hin u hu

end Complexity.Meyer
