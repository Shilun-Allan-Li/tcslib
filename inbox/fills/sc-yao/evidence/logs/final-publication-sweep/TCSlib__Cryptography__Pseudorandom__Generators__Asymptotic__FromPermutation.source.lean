/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCorePermutation.GoldreichLevin
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Stretch

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Asymptotic pseudorandom generators from one-way permutations

For a one-way permutation family `f` with hard-core predicate `h`,
[PS10, Theorem 79.4] appends `h(s)` to `f(s)` to gain one output bit.
The finite prediction bound comes from [Gar26, Theorem 3.2]. The efficient
evaluator and predictor machine are in `Asymptotic.HardCoreLemmas`.
The iterated construction in [PS10, Corollary 81.7] emits `h` at each
step along the orbit of `f` and uses the stretch theorem from `Stretch`.

To start from a one-way permutation alone, the balanced Goldreich–Levin
construction in `Asymptotic.HardCorePermutation.GoldreichLevin` supplies a
permutation with a hard-core bit at every length [PS10, Theorem 87.3].

**Deviation.** Theorem 79.4 uses the direct reduction of [Gar26, Theorem 3.2].
One call to the distinguisher with a uniformly guessed last bit gives
prediction probability `1/2 + ε` at distinguishing advantage `ε`.
Corollary 81.7 outputs `ℓ(n) + 1` bits indexed from zero and assumes
`n ≤ ℓ(n)` (source error 38).

## Main definitions

* `TCSlib.Cryptography.owpGenPRG` is the one-bit extension `s ↦ f(s) ‖ h(s)`.
* `TCSlib.Cryptography.owpPredictorSnoc` uses a distinguisher for that extension
  to predict the last bit.
* `TCSlib.Cryptography.PermFamily.iterPRG` emits `h` along the permutation orbit.

## Main results

* `TCSlib.Cryptography.owp_hardcore_prg` proves security of the one-bit extension.
* `TCSlib.Cryptography.cor_81_7` proves security of the iterated generator by
  applying `prg_expand` to the one-bit generator.
* `TCSlib.Cryptography.exists_securePRG_of_owp` composes the balanced
  Goldreich–Levin theorem with the one-bit extension.

Shamir's generator [PS10, §3.3.2, inventory Constr-77.a] motivates this
construction. Uniformity under an iterate of a permutation (Claim-78.a)
is an instance of `uprob_comp_equiv`. For Claim-78.b, the concrete example
in `HardcoreBit/NoFixedBit.lean` reveals the bits of the position while each
fixed input bit has prediction advantage `1/(2(n + 1))`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §§3.3.2–3.3.5 and §§3.4.2–3.4.3.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 and §3.3 (Theorem 3.2).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## The generator `f(s) ‖ h(s)` [PS10, Theorem 79.4] -/

/-- The generator `G(s) = f(s) ‖ h(s)` of [PS10, Theorem 79.4] for a permutation family `f`
and a predicate `h`: output length `n + 1`, the bit `h(s)` in the last position. -/
def owpGenPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) : PRG :=
  { stretch := .add .var (.const 1)
    G := fun n s => Fin.snoc (P.f n s) (h n s)
    expands := fun n => Nat.lt_succ_self n }

/-- **The outputs of the generator of Theorem 79.4 are `{0,1}^{n+1}`**: the published
equivalence `{0,1}^{stretch(n)} ≃ {0,1}^{n+1}` (the identity on the definition). -/
def owpGenPRG_outEquiv (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) :
    (Fin ((owpGenPRG P h).stretch.eval n) → Bool) ≃ (Fin (n + 1) → Bool) :=
  Equiv.refl _

/-- The generator of Theorem 79.4 through its output equivalence: `G(s) = f(s) ‖ h(s)`. -/
theorem owpGenPRG_G_outEquiv (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (s : Fin n → Bool) :
    owpGenPRG_outEquiv P h n ((owpGenPRG P h).G n s) = Fin.snoc (P.f n s) (h n s) := rfl

/-- The output equivalence keeps the string:
`List.ofFn (owpGenPRG_outEquiv P h n y) = List.ofFn y`. -/
theorem owpGenPRG_outEquiv_ofFn (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (y : Fin ((owpGenPRG P h).stretch.eval n) → Bool) :
    List.ofFn (owpGenPRG_outEquiv P h n y) = List.ofFn y := rfl

/-- Unfolding: the generator of Theorem 79.4 outputs `f(s)` on the first `n` positions. -/
theorem owpGenPRG_G_castSucc (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (s : Fin n → Bool) (i : Fin n) : (owpGenPRG P h).G n s i.castSucc = P.f n s i := by
  simp [owpGenPRG]

/-- Unfolding: the generator of Theorem 79.4 outputs `h(s)` in the last position. -/
theorem owpGenPRG_G_last (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (s : Fin n → Bool) : (owpGenPRG P h).G n s (Fin.last n) = h n s := by
  simp [owpGenPRG]

/-- The predictor of [Gar26, proof of Theorem 3.2] for a distinguisher of `f(s) ‖ h(s)`: on
input `y = f(s)` it draws a bit `σ` and coins for `D`, outputs `σ` if `D(y ‖ σ) = 1` and
`¬σ` otherwise, negated when `flip`. One call to `D`, one extra coin. -/
def owpPredictorSnoc {ρ : Type*} {n : ℕ} (D : (Fin (n + 1) → Bool) → ρ → Bool) (flip : Bool) :
    (Fin n → Bool) → Bool × ρ → Bool :=
  fun y c => owpPredictor (fun z : (Fin n → Bool) × Unit × Bool => fun r => D (Fin.snoc z.1 z.2.2) r)
    flip (y, ()) c

/-- Unfolding: `owpPredictorSnoc D flip` is the concrete `owpPredictor` [Gar26, proof of
Theorem 3.2] for the distinguisher `(y, (), σ) ↦ D(y ‖ σ)`, at the point `(y, ())`. -/
theorem owpPredictorSnoc_eq {ρ : Type*} {n : ℕ} (D : (Fin (n + 1) → Bool) → ρ → Bool)
    (flip : Bool) (y : Fin n → Bool) (c : Bool × ρ) :
    owpPredictorSnoc D flip y c = owpPredictor
      (fun z : (Fin n → Bool) × Unit × Bool => fun r => D (Fin.snoc z.1 z.2.2) r) flip (y, ()) c :=
  rfl

/-- **PRG from a one-way permutation, concrete form** [PS10, Theorem 79.4; Gar26, Theorem 3.2]:
if `D` distinguishes `f(s) ‖ B(s)` from a uniform `(n+1)`-bit string with advantage `ε`, then
for one sign `flip` the predictor `owpPredictorSnoc D flip` predicts `B(s)` from `f(s)` with
probability exactly `1/2 + ε`. Only bijectivity of `f` is used.

**Proof sketch.** Instance of `exists_owpPredictor` with the trivial second component
`β := Unit` and the bit `B'(s, ()) = B(s)`: `owpPair f ≃ f` and `owpGen f B' ≃ f(s) ‖ B(s)`
under the bijections `(s, ()) ↦ s` (seeds, `acceptProb_fst`) and
`(y, (), b) ↦ y ‖ b` (outputs, `prgAdv_comp_equiv`); the prediction experiments correspond
under `(s, c) ↦ ((s, ()), c)` (`uprob_eq_of_equiv`). -/
theorem exists_owpPredictorSnoc {ρ : Type*} [Fintype ρ] [Nonempty ρ] {n : ℕ}
    (f : (Fin n → Bool) ≃ (Fin n → Bool)) (B : (Fin n → Bool) → Bool)
    (D : (Fin (n + 1) → Bool) → ρ → Bool) :
    ∃ flip : Bool, predProb f B (owpPredictorSnoc D flip) =
      1 / 2 + prgAdv (fun s => Fin.snoc (f s) (B s)) D := by
  let e : (Fin n → Bool) × Unit × Bool ≃ (Fin (n + 1) → Bool) :=
    { toFun := fun z => Fin.snoc z.1 z.2.2
      invFun := fun t => (Fin.init t, (), t (Fin.last n))
      left_inv := fun z => by
        obtain ⟨a, -, b⟩ := z
        simp [Fin.init_snoc, Fin.snoc_last]
      right_inv := fun t => by simp [Fin.snoc_init_self] }
  obtain ⟨flip, hflip⟩ := exists_owpPredictor (β := Unit) f (fun w => B w.1)
    (fun z r => D (e z) r)
  refine ⟨flip, ?_⟩
  have h1 : predProb f B (owpPredictorSnoc D flip) =
      predProb (owpPair f) (fun w : (Fin n → Bool) × Unit => B w.1)
        (owpPredictor (fun z r => D (e z) r) flip) := by
    simp only [predProb_def]
    exact uprob_eq_of_equiv
      ({ toFun := fun z : (Fin n → Bool) × (Bool × ρ) => ((z.1, ()), z.2)
         invFun := fun z => (z.1.1, z.2)
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl } :
        (Fin n → Bool) × (Bool × ρ) ≃ ((Fin n → Bool) × Unit) × (Bool × ρ))
      fun _ => Iff.rfl
  have h2 : prgAdv (fun s => Fin.snoc (f s) (B s)) D =
      prgAdv (owpGen f fun w : (Fin n → Bool) × Unit => B w.1) (fun z r => D (e z) r) := by
    rw [← prgAdv_comp_equiv e]
    simp only [prgAdv_eq, distAdv_def]
    rw [← acceptProb_fst (τ := Unit) (fun s => Fin.snoc (f s) (B s)) D]
    rfl
  rw [h1, h2, hflip]

/-- **PRG from a one-way permutation** [PS10, Theorem 79.4]: if `f` is a one-way permutation
and `h` is a hard-core predicate for `f`, then `G(s) = f(s) ‖ h(s)` is a pseudorandom
generator.

**Deviation:** proved by the direct reduction of [Gar26, Theorem 3.2] (one call of `D` on
`f(s) ‖ σ` for a random bit `σ`, exact bound `1/2 + ε`) rather than through the next-bit
test as in the text (which loses a factor `1/(n+1)`); the text's proof writes "predicts
the `i`th bit with probability `1/p(n)`" for "advantage" and "`b` is hard-core" for `h`.

**Proof sketch.** *Easy:* from `hP.easy = ⟨F, hF, hFx⟩` and `hh.easy = ⟨H, hH, hHx⟩` the
evaluator `s ↦ F ⟨1^{|s|}, s⟩ ++ H ⟨1^{|s|}, s⟩` is polynomial-time
(`polyTimeComputable_unary`, `PolyTimeComputable.pairEncode`, `.comp`, `.append`) and
computes `List.ofFn (Fin.snoc (f s) (h s)) = List.ofFn (f s) ++ [h s]` (`List.ofFn_succ'`,
`Fin.snoc_castSucc`, `Fin.snoc_last`). *Pseudorandom:* fix `D : NUPPT`. At every `n`,
`exists_owpPredictorSnoc (P.f n) (h n) (D.distinguisher n (n+1))` gives a sign `flip_n`
(chosen by `Classical.choose`). The predictor machine `A`: advice `⟨[flip_n], D.advice n⟩`
(`NUPPT.exists_withAdvice`, length `≤ D.adv + 6`), coins `1 + D.coins`
(`NUPPT.exists_split (const 1)`: the first coin `σ` is passed as data), on `⟨1^n, y⟩` it forms
`y ++ [σ]` (`PolyTimeComputable.append`), calls `D` once on `⟨1^n, y ++ [σ]⟩` with the remaining
coins (`NUPPT.exists_seq`) and outputs `[xor (if D accepts then σ else !σ) flip_n]`
(`polyTimeComputable_ite`, `polyTimeComputable_pairEq`, `NUPPT.exists_comp`). Functional
identity: `A.predictor n n y r = owpPredictorSnoc (D.distinguisher n (n+1)) flip_n y (c r)`
with `c : A.Coins n ≃ Bool × D.Coins n` the coin split (`Fin.consEquiv`), so
`predProb (P.f n) (h n) (A.predictor n n) = 1/2 + prgAdv ((owpGenPRG P h).G n) (D.distinguisher n (n+1))`
(`uprob_comp_equiv`). Then `hh.hard A` gives a negligible `ε` with the left side `≤ 1/2 + ε n`,
so `0 ≤ prgAdv ≤ ε n` for all `n` and `Negligible.mono` closes `PRG.secure_iff`. -/
theorem owp_hardcore_prg (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (hP : OneWayPermutation P) (hh : P.HardCore h) : (owpGenPRG P h).Secure := by
  obtain ⟨F, hF, hFx⟩ := hP.evaluator
  obtain ⟨H, hH, hHx⟩ := hh.easy
  rw [PRG.secure_iff]
  refine ⟨(PRG.easy_iff _).2 (exists_owpGenEvaluator P h hF hH hFx hHx), fun D => ?_⟩
  have hflip : ∀ n, ∃ flip : Bool,
      predProb (P.f n) (h n) (owpPredictorSnoc (D.distinguisher n (n + 1)) flip) =
        1 / 2 + prgAdv (fun s => Fin.snoc (P.f n s) (h n s)) (D.distinguisher n (n + 1)) :=
    fun n => exists_owpPredictorSnoc (P.f n) (h n) _
  choose flip hflip using hflip
  obtain ⟨ε, hε, hbound⟩ := hh.hard (owpPredMachine D flip)
  refine hε.mono ⟨0, fun n _ => ?_⟩
  have h1 : predProb (P.f n) (h n) ((owpPredMachine D flip).predictor n n) ≤ 1 / 2 + ε n :=
    hbound n
  rw [owpPredMachine_predProb] at h1
  have h2 := hflip n
  have h3 : predProb (P.f n) (h n) (owpPredictorSnoc (D.distinguisher n (n + 1)) (flip n)) =
      predProb (P.f n) (h n) (fun y (c : Bool × D.Coins n) =>
        xor (if D.distinguisher n (n + 1) (Fin.snoc y c.1) c.2 then c.1 else !c.1) (flip n)) :=
    congrArg _ (funext fun y => funext fun c => by rw [owpPredictorSnoc_eq, owpPredictor_apply])
  rw [← h3, h2] at h1
  show |prgAdv (fun s => Fin.snoc (P.f n s) (h n s)) (D.distinguisher n (n + 1))| ≤ |ε n|
  have h4 : 0 ≤ prgAdv (fun s => Fin.snoc (P.f n s) (h n s)) (D.distinguisher n (n + 1)) := by
    rw [prgAdv_eq, distAdv_def]
    exact abs_nonneg _
  rw [abs_of_nonneg h4]
  exact le_trans (by linarith) (le_abs_self _)

/-! ## The iterated generator [PS10, Corollary 81.7] -/

/-- The generator `G(x) = h(x) ‖ h(f(x)) ‖ h(f^{(2)}(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))` of
[PS10, Corollary 81.7]: output bit `i` (`0 ≤ i ≤ ℓ(n)`) is `h(f^{(i)}(x))`; output length
`ℓ(n) + 1`, expanding when `n ≤ ℓ(n)`.

**Deviation:** the text's formula lists `ℓ(n) + 1` bits where Lemma 80.5 produces `ℓ(n)`
(source error 38); the stretch is `ℓ + 1` and the expansion hypothesis is `n ≤ ℓ(n)`. -/
def PermFamily.iterPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (ℓ : PolyExpr)
    (hℓ : ∀ n, n ≤ ℓ.eval n) : PRG where
  stretch := .add ℓ (.const 1)
  G n s := fun i => h n ((⇑(P.f n))^[i] s)
  expands n := Nat.lt_succ_of_le (hℓ n)

/-- **The closed form of Corollary 81.7**: the iterated generator is the `(ℓ(n) + 1)`-bit
expansion (Lemma 80.5) of the one-bit generator `f(s) ‖ h(s)` (Theorem 79.4), since the seed
update of `oneBitStep (f(s) ‖ h(s))` is `f` (`Fin.init_snoc`) and its output bit is `h`
(`Fin.snoc_last`).

**Proof sketch.** Read the expanded generator’s stretch and output from its field equations.
The seed update and emitted bit simplify to `f` and `h`. Rewrite the stretch first to
align the dependent output types, then compare the generators pointwise. -/
theorem PermFamily.iterPRG_eq_expand (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (ℓ : PolyExpr) (hℓ : ∀ n, n ≤ ℓ.eval n) :
    P.iterPRG h ℓ hℓ = PRG.expand (fun n s => Fin.snoc (P.f n s) (h n s)) (.add ℓ (.const 1))
      (fun n => Nat.lt_succ_of_le (hℓ n)) := by
  let G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool) :=
    fun n s => Fin.snoc (P.f n s) (h n s)
  let Q := PRG.expand G (.add ℓ (.const 1)) (fun n => Nat.lt_succ_of_le (hℓ n))
  have hlen : Q.stretch = .add ℓ (.const 1) := PRG.expand_stretch _ _ _
  have hclosed (n : ℕ) (s : Fin n → Bool) (i : Fin (Q.stretch.eval n)) :
      Q.G n s i = h n ((⇑(P.f n))^[i] s) := by
    change (PRG.expand G _ _).G n s i = _
    rw [PRG.expand_G_stretch]
    simp only [G, Fin.init_snoc, Fin.snoc_last]
  change P.iterPRG h ℓ hℓ = Q
  generalize Q = R at hlen hclosed ⊢
  cases R with
  | mk len out expands =>
    change len = .add ℓ (.const 1) at hlen
    subst len
    unfold PermFamily.iterPRG
    congr 1
    funext n s i
    exact (hclosed n s i).symm

/-- **The iterated generator is a PRG** [PS10, Corollary 81.7]: for a one-way permutation `f`
with hard-core predicate `h`, `G(x) = h(x) ‖ h(f(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))` is a PRG, by
Theorem 79.4 (`owp_hardcore_prg`) and Lemma 80.5 (`prg_expand`) through the closed form
`PermFamily.iterPRG_eq_expand`. -/
theorem cor_81_7 (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (ℓ : PolyExpr)
    (hℓ : ∀ n, n ≤ ℓ.eval n) (hP : OneWayPermutation P) (hh : P.HardCore h) :
    (P.iterPRG h ℓ hℓ).Secure := by
  rw [PermFamily.iterPRG_eq_expand]
  apply prg_expand
  have hgen := owp_hardcore_prg P h hP hh
  rw [PRG.secure_iff, PRG.easy_iff] at hgen
  exact (PRG.oneBit_secure_iff _).2 hgen

/-! ## From any one-way permutation -/

/-- **Pseudorandom generators from any one-way permutation** [PS10, §3.4, p. 84: "a PRG can
be constructed from any one-way permutation"; Theorems 79.4 and 87.3]: if a one-way
permutation exists then a secure pseudorandom generator exists, namely
`owpGenPRG P.glHalf glHalfBit`, `s ↦ glHalf f (s) ‖ glHalfBit s` (`owp_hardcore_prg` applied to
`OneWayPermutation.glHalf`). -/
theorem exists_securePRG_of_owp (h : ∃ P : PermFamily, OneWayPermutation P) :
    ∃ G : PRG, G.Secure :=
  let ⟨P, hP⟩ := h
  ⟨owpGenPRG P.glHalf glHalfBit, owp_hardcore_prg P.glHalf glHalfBit hP.glHalf.1 hP.glHalf.2⟩

end TCSlib.Cryptography
