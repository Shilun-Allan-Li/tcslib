/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.Pseudorandom.Functions.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for pseudorandom functions: truncation and the GGM evaluator

Machine-level and bit-string infrastructure for `TCSlib.Cryptography.Asymptotic.PRF`
([PS10, §3.8, Theorem 97.3]): the reduction from an arbitrary generator to a length-doubling
one (Cor-97.a, "without loss of generality") and the efficiency clause of the GGM family
(Claim-97.c). Everything here is (i) a bit-string identity between `List.ofFn` encodings and
`List.take`/`List.drop`, (ii) a machine of the closure calculus of
`TCSlib.Complexity.Randomized` (foundation decision D2 of `PassShelatChapter2-4Plan.md`), or
(iii) a probability identity on uniform strings.

* **Truncation.** `Complexity.NUPPT.preComp` is the *parameter-aware* pre-processor: the
  machine `A(1^n, pre ⟨1^n, y⟩; r)` with `A`'s coins and advice (the catalogue's
  `NUPPT.exists_comp` pre-processes the argument without seeing `1^n`, which a truncation to
  `n + 1` bits needs). `acceptProb_castLE` says that the first `m` bits of a uniform `ℓ`-bit
  string are uniform, and `PRG.Secure.truncateTo_easy` / `PRG.Secure.truncateTo_negligible`
  are the two clauses of "the first `m(n) ≤ ℓ(n)` output bits of a secure generator form a
  secure generator", from which `PRG.Secure.truncate` and `PRG.Secure.doubling` follow.
* **The GGM evaluator.** `ggmStep E` is one step of the walk down the GGM tree on the state
  word `⟨y, rest⟩` (current label, remaining input bits): it replaces `y` by the half of
  `E y` selected by the head bit of `rest` and drops that bit; `ggmEval E` iterates it
  `|⟨s, x⟩|` times (`Complexity.polyTimeComputable_iterate`) and reads the label. The closed
  form `ggmStep_iterate` and `ggmFrom_eq_walk` identify the result with `ggmBits G s x`.

## Main definitions

* `Complexity.NUPPT.preComp` — parameter-aware polynomial-time pre-processing of an `NUPPT`.
* `TCSlib.Cryptography.selHalf`, `TCSlib.Cryptography.walk`, `TCSlib.Cryptography.ggmStep`,
  `TCSlib.Cryptography.ggmEval` — half selection, the tree walk and the GGM evaluator.

## Main results

* `TCSlib.Cryptography.take_ofFn_castLE`, `drop_take_ofFn_blocks`, `ofFn_prefixAt`,
  `take_ofFn_splitHalves`, `drop_ofFn_splitHalves`, `selHalf_ofFn` — the bit-string identities.
* `Complexity.NUPPT.runAt_preComp` — the activation of the pre-processed machine.
* `TCSlib.Cryptography.acceptProb_castLE` — a prefix of a uniform string is uniform.
* `TCSlib.Cryptography.PRG.Secure.truncateTo_easy`,
  `TCSlib.Cryptography.PRG.Secure.truncateTo_negligible` — truncation of a secure generator.
* `TCSlib.Cryptography.ggmFrom_eq_walk`, `TCSlib.Cryptography.ggmStep_iterate`,
  `TCSlib.Cryptography.ggmEval_poly`, `TCSlib.Cryptography.ggmEval_ofFn` — the GGM
  evaluator is polynomial-time and computes `ggmBits`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.8: Theorem 97.3 and its proof; §3.3.5: Lemma 80.5.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2 (Construction 3.3, footnote 4).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Bit-string identities -/

/-- The first `m` bits of the encoding of an `ℓ`-bit string (`m ≤ ℓ`) encode its restriction
along `Fin.castLE`. -/
theorem take_ofFn_castLE {ℓ m : ℕ} (h : m ≤ ℓ) (f : Fin ℓ → Bool) :
    (List.ofFn f).take m = List.ofFn fun i : Fin m => f (Fin.castLE h i) := by
  refine List.ext_getElem (by simp [List.length_take, h]) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_take, List.getElem_ofFn]
  rfl

/-- Block `k` of the encoding of a `q`-tuple of `ℓ`-bit strings (positions `ℓk, …, ℓk + ℓ − 1`)
is the encoding of the `k`-th component, read through `FunFamily.blocks`. -/
theorem drop_take_ofFn_blocks (q ℓ : ℕ) (w : Fin (q * ℓ) → Bool) {k : ℕ} (hk : k < q) :
    ((List.ofFn w).drop (ℓ * k)).take ℓ = List.ofFn (FunFamily.blocks q ℓ w ⟨k, hk⟩) := by
  have hlen : ℓ * k + ℓ ≤ q * ℓ := by
    have : (k + 1) * ℓ ≤ q * ℓ := Nat.mul_le_mul_right ℓ hk
    nlinarith
  refine List.ext_getElem ?_ fun j hj₁ hj₂ => ?_
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · simp only [List.length_take, List.length_drop, List.length_ofFn] at hj₁
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    show w _ = w (finProdFinEquiv (⟨k, hk⟩, ⟨j, by omega⟩))
    congr 1
    ext
    simp only [finProdFinEquiv, Equiv.coe_fn_mk]
    omega

/-- The encoding of the `i`-bit prefix `prefixAt x i` (`i ≤ n`) is the first `i` bits of the
encoding of `x`. -/
theorem ofFn_prefixAt {n : ℕ} (x : Fin n → Bool) {i : ℕ} (hi : i ≤ n) :
    List.ofFn (prefixAt x i) = (List.ofFn x).take i := by
  rw [take_ofFn_castLE hi]
  congr 1
  funext k
  have hk : (k : ℕ) < n := lt_of_lt_of_le k.isLt hi
  simp only [prefixAt, hk, dite_true]
  rfl

/-- The first `n` bits of the encoding of a `2n`-bit string encode the first component of
`splitHalves`. -/
theorem take_ofFn_splitHalves {n : ℕ} (z : Fin (2 * n) → Bool) :
    (List.ofFn z).take n = List.ofFn (splitHalves z).1 := by
  rw [take_ofFn_castLE (by omega)]
  rfl

/-- The last `n` bits of the encoding of a `2n`-bit string encode the second component of
`splitHalves`. -/
theorem drop_ofFn_splitHalves {n : ℕ} (z : Fin (2 * n) → Bool) :
    (List.ofFn z).drop n = List.ofFn (splitHalves z).2 := by
  refine List.ext_getElem (by simp; omega) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_drop, List.getElem_ofFn]
  rfl

/-- **Half selection on strings:** the first (`b = false`) or the last (`b = true`) `|u|` bits
of the word `v` — `g_b(x)` of [PS10, Theorem 97.3] read off the string `g(x) = g₀(x) ‖ g₁(x)`
with the reference length `|u| = n`. -/
def selHalf (b : Bool) (u v : List Bool) : List Bool :=
  if b then (v.drop u.length).take u.length else v.take u.length

/-- Half selection on the encoding of a `2n`-bit string (reference length `n`) is the
encoding of `pairSel b (splitHalves z)`. -/
theorem selHalf_ofFn {n : ℕ} (b : Bool) {u : List Bool} (hu : u.length = n)
    (z : Fin (2 * n) → Bool) :
    selHalf b u (List.ofFn z) = List.ofFn (pairSel b (splitHalves z)) := by
  cases b
  · simp only [selHalf, pairSel, Bool.false_eq_true, if_false, hu, take_ofFn_splitHalves]
  · simp only [selHalf, pairSel, if_true, hu, drop_ofFn_splitHalves]
    exact List.take_of_length_le (le_of_eq List.length_ofFn)

/-- Half selection is at most as long as the reference word. -/
theorem length_selHalf_le (b : Bool) (u v : List Bool) : (selHalf b u v).length ≤ u.length := by
  unfold selHalf
  split_ifs <;> exact List.length_take_le _ _

/-- Half selection is polynomial-time in its three polynomial-time arguments (the typed cuts
`takeLen_poly`/`dropLen_poly` and `Complexity.polyTimeComputable_ite`). -/
theorem selHalf_poly {p : List Bool → Bool} {u v : List Bool → List Bool}
    (hp : PolyTimeComputable fun w => [p w]) (hu : PolyTimeComputable u)
    (hv : PolyTimeComputable v) : PolyTimeComputable fun w => selHalf (p w) (u w) (v w) :=
  polyTimeComputable_ite hp (takeLen_poly hu (dropLen_poly hu hv)) (takeLen_poly hu hv)

end TCSlib.Cryptography

namespace Complexity.NUPPT

open Turing

/-! ## Parameter-aware pre-processing -/

/-- The raw function of the parameter-aware pre-processor on the layout `⟨⟨⟨1^n, y⟩, α⟩, r⟩`:
run `A.output` on `⟨⟨⟨1^n, pre ⟨1^n, y⟩⟩, α⟩, r⟩`. -/
def preFun (A : NUPPT) (pre : List Bool → List Bool) (z : List Bool) : List Bool :=
  A.output (layout (inParam z) (pre (pairEncode (inParam z) (inArg z))) (inAdvice z) (inCoins z))

/-- The raw function of the pre-processor is polynomial-time. -/
theorem preFun_poly (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre) :
    PolyTimeComputable (A.preFun pre) :=
  A.polyTimeComputable_output.comp (polyTimeComputable_layout polyTimeComputable_inParam
    (hpre.comp (polyTimeComputable_inParam.pairEncode polyTimeComputable_inArg))
    polyTimeComputable_inAdvice polyTimeComputable_inCoins)

/-- **Parameter-aware pre-processing** [PS10, §2.1, the closure properties used implicitly]:
the machine with `A`'s coins and advice computing `A(1^n, pre ⟨1^n, y⟩; r)`. Unlike
`NUPPT.exists_comp`, the pre-processing sees the parameter (needed to truncate an input to
`n + 1` bits). The coin type is definitionally `A.Coins n`. -/
noncomputable def preComp (A : NUPPT) {pre : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) : NUPPT :=
  ofPolyTime (A.preFun_poly hpre) A.coins A.adv A.advice A.advice_length

/-- The coin polynomial of the pre-processed machine is `A`'s. -/
@[simp] theorem coins_preComp (A : NUPPT) {pre : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) : (A.preComp hpre).coins = A.coins := rfl

/-- The untyped activation of the pre-processed machine. -/
theorem runAtL_preComp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre)
    (n : ℕ) (y r : List Bool) :
    (A.preComp hpre).runAtL n y r = A.runAtL n (pre (pairEncode (List.replicate n true) y)) r := by
  unfold preComp
  rw [runAtL_ofPolyTime]
  simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- The typed activation of the pre-processed machine (its coin type is `A.Coins n`). -/
theorem runAt_preComp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre)
    (n : ℕ) (y : List Bool) (r : (A.preComp hpre).Coins n) :
    (A.preComp hpre).runAt n y r = A.runAt n (pre (pairEncode (List.replicate n true) y)) r :=
  runAtL_preComp A hpre n y (List.ofFn r)

end Complexity.NUPPT

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Truncation of a secure generator -/

/-- **A prefix of a uniform string is uniform:** restricting a uniform `ℓ`-bit string to its
first `m ≤ ℓ` bits gives a uniform `m`-bit string, so a distinguisher accepts the restriction
with the probability with which it accepts a uniform `m`-bit string. (Split the string along
`Fin ℓ ≃ Fin m ⊕ Fin (ℓ − m)` and forget the independent second half, `acceptProb_fst`.) -/
theorem acceptProb_castLE {ℓ m : ℕ} (h : m ≤ ℓ) {ρ : Type*} [Fintype ρ]
    (D : (Fin m → Bool) → ρ → Bool) :
    acceptProb (fun t : Fin ℓ → Bool => fun i : Fin m => t (Fin.castLE h i)) D =
      acceptProb (id : (Fin m → Bool) → Fin m → Bool) D := by
  let e : (Fin ℓ → Bool) ≃ (Fin m → Bool) × (Fin (ℓ - m) → Bool) :=
    ((Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' h)).symm (Equiv.refl Bool)).trans
      ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
        (Equiv.sumArrowEquivProdArrow _ _ _)))
  have he : (fun t : Fin ℓ → Bool => fun i : Fin m => t (Fin.castLE h i)) =
      fun t => (e t).1 := by
    funext t i
    rfl
  rw [he, acceptProb_comp_equiv e (fun p => p.1) D]
  exact acceptProb_fst (τ := Fin (ℓ - m) → Bool) (id : (Fin m → Bool) → Fin m → Bool) D

/-- **Truncation of a secure generator, efficiency clause:** the first `m(n) ≤ ℓ(n)` output
bits of a secure generator are computed by a polynomial-time string function (the evaluator
followed by the typed cut `Complexity.polyTimeComputable_pairTakePoly m`). -/
theorem PRG.Secure.truncateTo_easy {P : PRG} (hP : P.Secure) (m : PolyExpr)
    (hm : ∀ n, m.eval n ≤ P.stretch.eval n) :
    ∃ E' : List Bool → List Bool, PolyTimeComputable E' ∧
      ∀ n (s : Fin n → Bool),
        E' (List.ofFn s) = List.ofFn fun i : Fin (m.eval n) => P.G n s (Fin.castLE (hm n) i) := by
  obtain ⟨E, hE, hEs⟩ := hP.1
  refine ⟨fun w => (E w).take (m.eval w.length), ?_, fun n s => ?_⟩
  · convert (polyTimeComputable_pairTakePoly m).comp (polyTimeComputable_id.pairEncode hE) using 1
    funext w
    simp
  · simp only [List.length_ofFn]
    rw [hEs, take_ofFn_castLE (hm n)]

/-- **Truncation of a secure generator, pseudorandomness clause:** for every non-uniform PPT
`D`, the PRG advantage of `D(1^n, ·)` against the first `m(n) ≤ ℓ(n)` output bits of a secure
generator is negligible.

**Proof sketch.** The machine `D' := D.preComp (take m)` truncates its `ℓ(n)`-bit input to
`m(n)` bits and runs `D` (`Complexity.NUPPT.preComp`, `runAt_preComp`,
`take_ofFn_castLE`), so `D'.distinguisher n ℓ(n) = D.distinguisher n m(n) ∘ castLE`. By the
sunglass identity `distAdv_comp` its advantage against `G n` is the advantage of `D` between
the truncated generator and the truncation of a uniform `ℓ(n)`-bit string, which is uniform
(`acceptProb_castLE`). Security of `P` makes the former negligible. -/
theorem PRG.Secure.truncateTo_negligible {P : PRG} (hP : P.Secure) (m : PolyExpr)
    (hm : ∀ n, m.eval n ≤ P.stretch.eval n) (D : NUPPT) :
    Negligible fun n =>
      prgAdv (fun s : Fin n → Bool => fun i : Fin (m.eval n) => P.G n s (Fin.castLE (hm n) i))
        (D.distinguisher n (m.eval n)) := by
  have hpre : PolyTimeComputable fun w => (pairSndD w).take (m.eval (pairFstD w).length) :=
    polyTimeComputable_pairTakePoly m
  have hneg := hP.2 (D.preComp hpre)
  refine hneg.mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  have hfun : (D.preComp hpre).distinguisher n (P.stretch.eval n) =
      fun t r => D.distinguisher n (m.eval n) (fun i => t (Fin.castLE (hm n) i)) r := by
    funext t r
    unfold NUPPT.distinguisher
    rw [NUPPT.runAt_preComp]
    simp only [pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate]
    rw [take_ofFn_castLE (hm n)]
  show prgAdv (fun s : Fin n → Bool => fun i : Fin (m.eval n) => P.G n s (Fin.castLE (hm n) i))
      (D.distinguisher n (m.eval n)) =
    prgAdv (P.G n) ((D.preComp hpre).distinguisher n (P.stretch.eval n))
  rw [hfun, prgAdv, prgAdv,
    distAdv_comp (fun t : Fin (P.stretch.eval n) → Bool => fun i : Fin (m.eval n) =>
      t (Fin.castLE (hm n) i)) (P.G n) id (D.distinguisher n (m.eval n)), distAdv, distAdv]
  congr 2
  exact (acceptProb_castLE (hm n) _).symm

/-! ## The GGM evaluator -/

/-- **One step of the walk down the GGM tree** on the state word `⟨y, rest⟩` (current label
`y`, remaining input bits `rest`): if `rest` is empty, stay; otherwise replace `y` by the half
of `E y` selected by the head bit of `rest` (`selHalf`, reference length `|y|`) and drop that
bit. `E` is the evaluator of the length-doubling generator. -/
def ggmStep (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  if pairSndD w = [] then w
  else pairEncode (selHalf ((pairSndD w).headD false) (pairFstD w) (E (pairFstD w)))
    (pairSndD w).tail

/-- The walk down the tree from the label `y` along the bits `bs`:
`walk G' y [b₁, …, b_k] = G'_{b_k}(⋯ G'_{b₁}(y) ⋯)`. -/
def walk {S : Type*} (G' : S → S × S) (y : S) (bs : List Bool) : S :=
  bs.foldl (fun y b => pairSel b (G' y)) y

/-- `ggmFrom G' x i y` is the walk from `y` along the bits of `x` from position `i` on
(strong induction on `n − i`, `ggmFrom_of_lt`, `ggmFrom_of_le`). -/
theorem ggmFrom_eq_walk {S : Type*} (G' : S → S × S) {n : ℕ} (x : Fin n → Bool) :
    ∀ (i : ℕ) (y : S), ggmFrom G' x i y = walk G' y ((List.ofFn x).drop i)
  | i, y => by
    by_cases h : i < n
    · rw [ggmFrom_of_lt G' x h, ggmFrom_eq_walk G' x (i + 1)]
      have hd : (List.ofFn x).drop i = x ⟨i, h⟩ :: (List.ofFn x).drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using h), List.getElem_ofFn]
      rw [hd, walk, walk, List.foldl_cons]
    · rw [ggmFrom_of_le G' x (not_lt.1 h), List.drop_of_length_le (by simpa using not_lt.1 h)]
      rfl
termination_by i => n - i

/-- The GGM step never lengthens a word. -/
theorem length_ggmStep_le (E : List Bool → List Bool) (w : List Bool) :
    (ggmStep E w).length ≤ w.length := by
  unfold ggmStep
  split_ifs with h
  · exact le_rfl
  · obtain ⟨a, b, hw⟩ : ∃ a b, w = pairEncode a b := by
      cases hd : pairDecode w with
      | none => exact absurd (by simp [pairSndD, hd]) h
      | some ab => exact ⟨ab.1, ab.2, eq_pairEncode_of_pairDecode w ab.1 ab.2 hd⟩
    subst hw
    simp only [pairFstD_pairEncode, pairSndD_pairEncode] at h ⊢
    rw [length_pairEncode, length_pairEncode, List.length_tail]
    have h1 := length_selHalf_le (b.headD false) a (E a)
    have h2 : 0 < b.length := List.length_pos_of_ne_nil h
    omega

/-- The orbit of the GGM step stays within the input length. -/
theorem length_ggmStep_iterate_le (E : List Bool → List Bool) (w : List Bool) (k : ℕ) :
    ((ggmStep E)^[k] w).length ≤ w.length := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (length_ggmStep_le E _).trans ih

/-- The GGM step is polynomial-time (`Complexity.polyTimeComputable_ite` on the emptiness test
of `rest`, `selHalf_poly`, `StateLoop.headBit_poly`, `StateLoop.tail_poly`). -/
theorem ggmStep_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ggmStep E) := by
  have hsel : PolyTimeComputable fun w =>
      selHalf ((pairSndD w).headD false) (pairFstD w) (E (pairFstD w)) :=
    selHalf_poly (StateLoop.headBit_poly.comp polyTimeComputable_pairSndD)
      polyTimeComputable_pairFstD (hE.comp polyTimeComputable_pairFstD)
  have htest : PolyTimeComputable fun w => [decide (pairSndD w = [])] :=
    StateLoop.isNil_poly.comp polyTimeComputable_pairSndD
  convert polyTimeComputable_ite htest polyTimeComputable_id
    (hsel.pairEncode (StateLoop.tail_poly.comp polyTimeComputable_pairSndD)) using 1
  funext w
  simp [ggmStep]

/-- **Closed form of the GGM step's orbit on encoded data:** from `⟨s, bs⟩` with `s` an
`n`-bit label, after `k` steps the state is `⟨walk s (bs.take k), bs.drop k⟩`.

**Proof sketch.** Induction on `k`. On an empty `rest` the step is the identity and the walk
is trivial. On `b :: bs` the step replaces the label by the half of `E (ofFn s) = ofFn (G s)`
selected by `b`, which is `ofFn (pairSel b (splitHalves (G s)))` by `selHalf_ofFn`, and drops
`b`; the induction hypothesis from the new label and `bs` finishes. -/
theorem ggmStep_iterate {n : ℕ} {G : (Fin n → Bool) → Fin (2 * n) → Bool}
    {E : List Bool → List Bool} (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s)) :
    ∀ (k : ℕ) (y : Fin n → Bool) (bs : List Bool),
      (ggmStep E)^[k] (pairEncode (List.ofFn y) bs) =
        pairEncode (List.ofFn (walk (splitHalves ∘ G) y (bs.take k))) (bs.drop k)
  | 0, y, bs => by simp [walk]
  | k + 1, y, bs => by
    rw [Function.iterate_succ_apply]
    cases bs with
    | nil =>
      have h0 : ggmStep E (pairEncode (List.ofFn y) []) = pairEncode (List.ofFn y) [] := by
        simp [ggmStep]
      rw [h0, ggmStep_iterate hG k y []]
      simp [walk]
    | cons b bs =>
      have h1 : ggmStep E (pairEncode (List.ofFn y) (b :: bs)) =
          pairEncode (List.ofFn (pairSel b (splitHalves (G y)))) bs := by
        simp only [ggmStep, pairSndD_pairEncode, pairFstD_pairEncode, List.headD_cons,
          List.tail_cons, hG]
        rw [if_neg (List.cons_ne_nil _ _), selHalf_ofFn b List.length_ofFn]
      rw [h1, ggmStep_iterate hG k]
      simp [walk, List.take_succ_cons, List.drop_succ_cons, List.foldl_cons]

/-- **The GGM evaluator** (Claim-97.c): on `⟨s, x⟩` iterate the GGM step `|⟨s, x⟩|` times
(at least `|x|`, after which the step is the identity) and read the label. -/
def ggmEval (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairFstD ((ggmStep E)^[w.length] w)

/-- The GGM evaluator is polynomial-time (`Complexity.polyTimeComputable_iterate` with
`R = P = var`, the orbit staying within the input length). -/
theorem ggmEval_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ggmEval E) := by
  have h := polyTimeComputable_iterate (ggmStep_poly hE) .var .var
    (fun x i _ => length_ggmStep_iterate_le E x i)
  exact polyTimeComputable_pairFstD.comp h

/-- The GGM evaluator on `⟨s, bs⟩` with an `n`-bit label `s` and an arbitrary bit list `bs`
computes the walk from `s` along `bs` (`ggmStep_iterate`; the word is at least as long as
`bs`, so all bits are consumed). -/
theorem ggmEval_ofFn_walk {n : ℕ} {G : (Fin n → Bool) → Fin (2 * n) → Bool}
    {E : List Bool → List Bool} (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s))
    (y : Fin n → Bool) (bs : List Bool) :
    ggmEval E (pairEncode (List.ofFn y) bs) = List.ofFn (walk (splitHalves ∘ G) y bs) := by
  unfold ggmEval
  rw [ggmStep_iterate hG, pairFstD_pairEncode,
    List.take_of_length_le (by rw [length_pairEncode]; omega)]

/-- **The GGM evaluator computes the GGM family:** on `⟨s, x⟩` with `s, x` `n`-bit strings it
returns the encoding of `ggmBits G s x = g_{x_n}(⋯ g_{x_1}(s) ⋯)` (`ggmStep_iterate`,
`ggmFrom_eq_walk`). -/
theorem ggmEval_ofFn {n : ℕ} {G : (Fin n → Bool) → Fin (2 * n) → Bool}
    {E : List Bool → List Bool} (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s))
    (s x : Fin n → Bool) :
    ggmEval E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (ggmBits G s x) := by
  unfold ggmEval
  rw [ggmStep_iterate hG, pairFstD_pairEncode]
  congr 1
  rw [List.take_of_length_le (by rw [length_pairEncode]; simp)]
  show walk _ s (List.ofFn x) = ggmFrom (splitHalves ∘ G) x 0 s
  rw [ggmFrom_eq_walk, List.drop_zero]

end TCSlib.Cryptography
