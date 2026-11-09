/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.StretchMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Asymptotic PRG stretch extension

Iterating a secure one-bit generator gives a secure generator of any polynomial
output length that exceeds the seed length at every parameter [PS10, Lemma 80.5].
The finite hybrid bound lifts to a non-uniform polynomial-time reduction through
the evaluator and hybrid machine in `StretchMachine`. Truncation to one extra bit,
expansion to `2n + 1` bits, and truncation to `2n` give the length-doubling generator
used by GGM [PS10, proof of Theorem 97.3].

## Main definitions

* `TCSlib.Cryptography.PRG.oneBit` packages the one-bit-stretch generator.
* `TCSlib.Cryptography.PRG.expand` gives the iterated generator.
* `TCSlib.Cryptography.expandRed` gives the finite hybrid reduction.
* `TCSlib.Cryptography.DoublingPRG` gives the security contract for length doubling.

## Main results

* `TCSlib.Cryptography.exists_expandRed_ge` gives the finite advantage bound.
* `TCSlib.Cryptography.prg_expand` proves secure polynomial stretch.
* `TCSlib.Cryptography.PRG.Secure.truncate` and
  `TCSlib.Cryptography.PRG.Secure.doubling` give the secure truncation and doubling results.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.3.5, Lemma 80.5, and §3.8, proof of Theorem 97.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.3.1, Theorem 3.1.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-- A one-bit-stretch generator `G n : {0,1}^n → {0,1}^{n+1}` as a `PRG` with stretch
`n + 1` ("Let `G : {0,1}^n → {0,1}^{n+1}` be a PRG", [PS10, Lemma 80.5]). -/
def PRG.oneBit (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) : PRG where
  stretch := .add .var (.const 1)
  G := G
  expands n := Nat.lt_succ_self n

/-- Field equation: the stretch of `PRG.oneBit G` is `n + 1`. -/
theorem PRG.oneBit_stretch (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) :
    (PRG.oneBit G).stretch = .add .var (.const 1) := rfl

/-- Field equation: the generator of `PRG.oneBit G` at seed length `n` is `G n`. -/
theorem PRG.oneBit_G (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (n : ℕ)
    (s : Fin n → Bool) : (PRG.oneBit G).G n s = G n s := rfl

/-- **Security of `PRG.oneBit G` unfolded**: it is secure iff some polynomial-time string
function computes `G n s` from the seed string, and for every non-uniform PPT `D` the PRG
advantage `prgAdv (G n) (D(1^n, ·))` on `n + 1` bits is negligible (`PRG.secure_iff` at
`oneBit`, where the generator's type depends on the stretch). -/
theorem PRG.oneBit_secure_iff (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) :
    (PRG.oneBit G).Secure ↔
      (∃ F : List Bool → List Bool, PolyTimeComputable F ∧
        ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G n s)) ∧
      ∀ D : NUPPT, Negligible fun n => prgAdv (G n) (D.distinguisher n (n + 1)) := by
  rw [PRG.secure_iff, PRG.easy_iff]
  rfl

/-! ## Expansion of a one-bit-stretch generator [PS10, Lemma 80.5] -/

/-- A one-bit-stretch generator read in the text's order `X_{i+1} ‖ b_{i+1} ← G(X_i)`
[PS10, Lemma 80.5]: the output bit is the last bit of `G(s)` and the next seed is its first
`n` bits (`(Fin.snocEquiv _).symm (G s)`); this is the `S → Bool × S` form of
[Gar26, Construction 3.1], which reads the bit first. -/
def oneBitStep {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) :
    (Fin n → Bool) → Bool × (Fin n → Bool) :=
  fun s => (G s (Fin.last n), Fin.init (G s))

/-- Unfolding: one step outputs the last bit of `G(s)` and the next seed `init G(s)`. -/
theorem oneBitStep_eq {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) (s : Fin n → Bool) :
    oneBitStep G s = (G s (Fin.last n), Fin.init (G s)) := rfl

/-- The **expanded generator** `G'(s) = b_1 ⋯ b_{ℓ(n)}` of [PS10, Lemma 80.5]: `X_0 = s`,
`X_{i+1} ‖ b_{i+1} ← G(X_i)`, output the `ℓ(n)` bits (the final seed is dropped). Formally
the first component of the concrete `prgExt (oneBitStep (G n)) (ℓ n)` [Gar26,
Construction 3.1]; the expansion clause `n < ℓ(n)`, at every `n` (see `PRG`), is the
hypothesis `hℓ`.

**Deviation:** `G(X_i)` is read seed-first/bit-last as in the text; the output drops the
final seed (as in the text), the concrete `prgExt` keeps it. The text's "for any polynomial
`ℓ`" is restricted to `ℓ(n) > n` at every `n`, `n = 0` included (the cost of `PRG.expands`:
`2n` and `n^c` are excluded, `2n + 1` and `n^c + 1` are not; gate 03c, finding 1, ruling
G3-2). -/
def PRG.expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) : PRG where
  stretch := ℓ
  G n s := (prgExt (oneBitStep (G n)) (ℓ.eval n) s).1
  expands := hℓ

/-- Field equation: the stretch of `PRG.expand G ℓ hℓ` is `ℓ`. -/
theorem PRG.expand_stretch (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) : (PRG.expand G ℓ hℓ).stretch = ℓ := rfl

/-- Closed form of the expansion: output bit `i` is the last bit of `G(X_i)`, where
`X_i` is the `i`-th iterate of `s ↦ init (G s)` on the seed (`b_{i+1}` in the text's
1-indexed notation). -/
theorem PRG.expand_G (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) (n : ℕ) (s : Fin n → Bool) (i : Fin (ℓ.eval n)) :
    (PRG.expand G ℓ hℓ).G n s i = G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := rfl

/-- Closed form of the expansion with the output index typed by the stretch:
`G'(s)_i = last bit of G((s ↦ init G(s))^i (s))` for
`i : Fin ((PRG.expand G ℓ hℓ).stretch.eval n)` (`PRG.expand_G` on the PRG's own output space). -/
theorem PRG.expand_G_stretch (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) (n : ℕ) (s : Fin n → Bool)
    (i : Fin ((PRG.expand G ℓ hℓ).stretch.eval n)) :
    (PRG.expand G ℓ hℓ).G n s i = G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) :=
  PRG.expand_G G ℓ hℓ n s i

/-- The hybrid-`k` reduction of [PS10, Lemma 80.5] (the machine `M(y)` of the proof) in the
text's seed-first convention: on `T ∈ {0,1}^{n+1}` read `(b, X) := (T_{n+1}, T_1 ⋯ T_n)`, draw
`k` uniform bits `b_prev`, put `b` at position `k`, iterate `G` on `X` for the remaining
positions and call `D` once on the `ℓ` bits. Cost: that of `prgExtRed` (`l − k − 1` calls to
`G`, one to `D`, `l` coins of which `k` are used). -/
def expandRed {ρ : Type*} {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) (l k : ℕ)
    (D : (Fin l → Bool) → ρ → Bool) : (Fin (n + 1) → Bool) → (Fin l → Bool) × ρ → Bool :=
  fun T c => prgExtRed (oneBitStep G) l k (fun z r => D z.1 r) (T (Fin.last n), Fin.init T) c

/-- Unfolding: `expandRed G l k D` on `T` is the concrete hybrid-`k` reduction `prgExtRed`
[Gar26, Theorem 3.1] of `oneBitStep G` against `D ∘ fst`, on the re-encoded input
`(T_{n+1}, T_1 ⋯ T_n)`. -/
theorem expandRed_eq {ρ : Type*} {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) (l k : ℕ)
    (D : (Fin l → Bool) → ρ → Bool) (T : Fin (n + 1) → Bool) (c : (Fin l → Bool) × ρ) :
    expandRed G l k D T c =
      prgExtRed (oneBitStep G) l k (fun z r => D z.1 r) (T (Fin.last n), Fin.init T) c := rfl

/-- Dropping an independent uniform component from a generator's output does not change
PRG advantages: `prgAdv (fst ∘ X) D = prgAdv X (D ∘ fst)` (the projection is a deterministic
post-processing and the projection of a uniform pair is uniform). -/
theorem prgAdv_fst {σ γ δ ρ : Type*} [Fintype σ] [Fintype γ] [Fintype δ] [Nonempty δ]
    [Fintype ρ] (X : σ → γ × δ) (D : γ → ρ → Bool) :
    prgAdv (fun s => (X s).1) D = prgAdv X (fun z r => D z.1 r) := by
  simp only [prgAdv_eq, distAdv_def]
  rw [← acceptProb_fst (τ := δ) (id : γ → γ) D]
  rfl

/-- **Expansion, concrete form** [PS10, Lemma 80.5; Gar26, Theorem 3.1]: if `D` distinguishes
the `l`-bit expansion of `G` (`l ≥ 1`, bits only) from a uniform `l`-bit string with advantage
`ε`, then for some hybrid index `k < l` the reduction `expandRed G l k D` distinguishes
`G` from a uniform `(n+1)`-bit string with advantage at least `ε / l`.

**Proof sketch.** `prgAdv_fst` moves the projection onto the distinguisher;
`exists_prgExtRed_ge` for `oneBitStep G` gives `k`; `prgAdv_comp_equiv` with the bijection
`(Fin.snocEquiv _).symm : {0,1}^{n+1} ≃ Bool × {0,1}^n` re-encodes the reduction's input. -/
theorem exists_expandRed_ge {ρ : Type*} [Fintype ρ] {n : ℕ}
    (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) {l : ℕ} (hl : 0 < l)
    (D : (Fin l → Bool) → ρ → Bool) :
    ∃ k < l, prgAdv (fun s => (prgExt (oneBitStep G) l s).1) D / l ≤
      prgAdv G (expandRed G l k D) := by
  obtain ⟨k, hk, h⟩ := exists_prgExtRed_ge (oneBitStep G) hl (fun z r => D z.1 r)
  refine ⟨k, hk, ?_⟩
  rw [prgAdv_fst]
  refine h.trans_eq ?_
  exact prgAdv_comp_equiv (Fin.snocEquiv fun _ => Bool).symm G
    (prgExtRed (oneBitStep G) l k fun z r => D z.1 r)

/-- **Expansion of a PRG** [PS10, Lemma 80.5]: if the one-bit-stretch generator `G` is a PRG
then so is its `ℓ(n)`-bit expansion `G'` (`ℓ(n) > n` at every `n`, see `PRG`).

The input is a one-bit-stretch `G : {0,1}^n → {0,1}^{n+1}`, as in the text ("Let
`G : {0,1}^n → {0,1}^{n+1}` be a PRG"), not a general `P : PRG` (the shape recorded at DESIGN
§2.12); a general secure `P` reaches it through its truncation to `n + 1` bits, `PRG.truncate`
with `PRG.Secure.truncate : (PRG.oneBit P.truncate).Secure` (below, following gate 03c,
finding 4).

**Deviation:** `G'` drops the final seed and reads `G(X_i)` seed-first, as the text; the
text's proof interchanges `m(n)` and `ℓ(n)`, starts the hybrids at `i = 1` (they must start
at `0`) and reads `M(y)` bit-first against the construction (source error 34). The text's
"for any polynomial `ℓ`" is restricted to `ℓ(n) > n` at every `n`, `n = 0` included (the cost
of `PRG.expands`; gate 03c, finding 1, ruling G3-2); the security half uses only `ℓ(n) > 0`.

**Proof sketch.** *Easy:* from `h.1 = ⟨F, hF, hFs⟩`, `G'` is computed by
`polyTimeComputable_iterateEmit` with step `x ↦ (F x).dropLast` (the next seed,
`Turing.FinTM.computesFunInTime_stripLast`) and emission `x ↦ [(F x).getLast]`, `R := ℓ`,
orbit bound `P := var` (all seeds have length `n`), truncated to the first `ℓ(n)` bits
(`polyTimeComputable_pairTakePoly ℓ` on `⟨1^{|s|}, ·⟩`); the identity with
`PRG.expand_G` is `List.ofFn_succ'`. *Pseudorandom* (`PRG.secure_iff`): fix `D : NUPPT`.
At every `n`, `exists_expandRed_ge (G n) (hl := Nat.lt_of_le_of_lt (Nat.zero_le n) (hℓ n))`
with `D.distinguisher n (ℓ n)` gives a hybrid index `k_n < ℓ(n)`. The reduction machine
`M`: advice `⟨⟨1^{k_n}, 1^{ℓ(n) − k_n − 1}⟩, D.advice n⟩` (`NUPPT.exists_withAdvice`,
length `≤ 2ℓ + D.adv + 8`), coins `ℓ + D.coins` (`NUPPT.exists_split ℓ`), on `⟨1^n, T⟩` it
takes the first `k_n` coins as `b_prev` (`pairTakePoly`), the last bit of `T` as `b` and its
first `n` bits as `X` (`stripLast`, `pairDropPoly`), iterates `F` `ℓ(n) − k_n − 1` times
emitting the last bits (`polyTimeComputable_iterateEmit` with the unary advice as fuel),
concatenates `b_prev ++ [b] ++ b_next` and calls `D` once (`NUPPT.exists_seq`). Functional
identity: `M.distinguisher n (n+1) T r = expandRed (G n) (ℓ n) k_n (D.distinguisher n (ℓ n)) T (c r)`
with `c : M.Coins n ≃ (Fin (ℓ n) → Bool) × D.Coins n` (`Fin.appendEquiv`), hence
`prgAdv (G n) (M.distinguisher n (n+1)) ≥ prgAdv ((PRG.expand G ℓ hℓ).G n) (D.distinguisher n (ℓ n)) / ℓ(n)`
(`uprob_comp_equiv`). By `h.2 M` the left side is negligible; `ℓ(n) ≤ C (n+1)^c`
(`PolyExpr.eval_le`), so the right side is negligible by `Negligible.mul_pow`,
`Negligible.const_mul` and `Negligible.mono`. -/
theorem prg_expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) (h : (PRG.oneBit G).Secure) : (PRG.expand G ℓ hℓ).Secure := by
  rw [PRG.secure_iff] at h ⊢
  obtain ⟨hE1, hsec⟩ := h
  obtain ⟨F, hF, hFs⟩ := (PRG.easy_iff _).1 hE1
  have hFs' : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G n s) := hFs
  refine ⟨?_, fun D => ?_⟩
  · obtain ⟨E, hE, hEs⟩ := exists_expandEvaluator G hFs' hF ℓ
    exact (PRG.easy_iff _).2 ⟨E, hE, fun n s => by rw [hEs]; rfl⟩
  · have hk : ∀ n, ∃ k < ℓ.eval n,
        prgAdv (fun s => (prgExt (oneBitStep (G n)) (ℓ.eval n) s).1) (D.distinguisher n (ℓ.eval n)) /
          ℓ.eval n ≤
        prgAdv (G n) (expandRed (G n) (ℓ.eval n) k (D.distinguisher n (ℓ.eval n))) :=
      fun n => exists_expandRed_ge (G n) (Nat.lt_of_le_of_lt (Nat.zero_le n) (hℓ n)) _
    choose k hk hle using hk
    have hneg : Negligible fun n =>
        prgAdv (G n) ((expandRedMachine D hF ℓ k hk).distinguisher n (n + 1)) :=
      hsec (expandRedMachine D hF ℓ k hk)
    have hred : ∀ n, prgAdv (G n) ((expandRedMachine D hF ℓ k hk).distinguisher n (n + 1)) =
        prgAdv (G n) (expandRed (G n) (ℓ.eval n) (k n) (D.distinguisher n (ℓ.eval n))) := by
      intro n
      refine prgAdv_coins_equiv _ _ _ (Fin.appendEquiv (ℓ.eval n) (D.coinLen n)) fun T c => ?_
      obtain ⟨a, c⟩ := c
      exact expandRedMachine_distinguisher G hFs' D hF ℓ k hk n T a c _ (ofFn_appendEquiv a c)
    simp only [hred] at hneg
    refine (hneg.polyExpr_mul ℓ).mono ⟨0, fun n _ => ?_⟩
    have hpos : (0 : ℝ) < ℓ.eval n := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le n) (hℓ n)
    have h1 := hle n
    rw [div_le_iff₀ hpos] at h1
    show |prgAdv (fun s => (prgExt (oneBitStep (G n)) (ℓ.eval n) s).1) (D.distinguisher n (ℓ.eval n))| ≤
      |(ℓ.eval n : ℝ) * prgAdv (G n) (expandRed (G n) (ℓ.eval n) (k n) (D.distinguisher n (ℓ.eval n)))|
    have h2 : 0 ≤ prgAdv (fun s => (prgExt (oneBitStep (G n)) (ℓ.eval n) s).1)
        (D.distinguisher n (ℓ.eval n)) := abs_nonneg _
    have h3 : 0 ≤ prgAdv (G n) (expandRed (G n) (ℓ.eval n) (k n) (D.distinguisher n (ℓ.eval n))) :=
      abs_nonneg _
    rw [abs_of_nonneg h2, abs_of_nonneg (mul_nonneg hpos.le h3)]
    linarith

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
  obtain ⟨E, hE, hEs⟩ := (PRG.easy_iff P).1 ((PRG.secure_iff P).1 hP).1
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
  have hneg := ((PRG.secure_iff P).1 hP).2 (D.preComp hpre)
  refine hneg.mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  have hfun : ∀ t r, D.distinguisher n (m.eval n) (fun i => t (Fin.castLE (hm n) i))
      (D.preComp_coinsEquiv hpre n r) = (D.preComp hpre).distinguisher n (P.stretch.eval n) t r := by
    intro t r
    rw [NUPPT.distinguisher_eq, NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq,
      NUPPT.distinguisherL_eq, NUPPT.runAt_preComp]
    simp only [pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate]
    rw [take_ofFn_castLE (hm n)]
  rw [← prgAdv_coins_equiv (P.G n) _ _ (D.preComp_coinsEquiv hpre n) hfun, prgAdv_eq, prgAdv_eq,
    distAdv_comp (fun t : Fin (P.stretch.eval n) → Bool => fun i : Fin (m.eval n) =>
      t (Fin.castLE (hm n) i)) (P.G n) id (D.distinguisher n (m.eval n)), distAdv_def,
    distAdv_def]
  congr 2
  exact (acceptProb_castLE (hm n) _).symm

/-! ### Length-doubling generators (Cor-97.a) -/

/-- The output ensemble `{s ← U_n : G(s)}` of a length-doubling generator
`G : {0,1}^n → {0,1}^{2n}`, with the stretch `2n` as the syntactic polynomial `2 · var` (D9). -/
def doublingEnsemble (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)) :
    Ensemble (.mul (.const 2) .var) where
  σ n := Fin n → Bool
  X := G

/-- **A length-doubling pseudorandom generator** `g : {0,1}^n → {0,1}^{2n}` [PS10, proof of
Theorem 97.3, "let `g` be a length-doubling pseudorandom generator"]: efficiently computable
and with a pseudorandom output ensemble, exactly as `PRG.Secure` [PS10, Definition 77.1] but
with the stretch `2n`.

**Deviation:** a length-doubling generator is not a `PRG` of this library (the expansion
clause `n < 2n` fails at `n = 0`), hence this separate predicate; `PRG.Secure.doubling`
(Cor-97.a) produces one from any `PRG`. -/
structure DoublingPRG (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)) : Prop where
  /-- Efficiency: a polynomial-time string function computes `G n s` from the seed string. -/
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s : Fin n → Bool), E (List.ofFn s) = List.ofFn (G n s)
  /-- Pseudorandomness of the output ensemble [PS10, Definition 74.1]. -/
  pseudorandom : (doublingEnsemble G).Pseudorandom

/-- **Pseudorandomness of a length-doubling generator unfolded**: for every non-uniform PPT
`D` the concrete PRG advantage `prgAdv (G n) (D(1^n, ·))` [Gar26, Definition 3.5] between
`G(U_n)` and `U_{2n}` is negligible (definitional, `Ensemble.pseudorandom_iff_prgAdv`). -/
theorem DoublingPRG.negligible_prgAdv {G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)}
    (hG : DoublingPRG G) (D : NUPPT) :
    Negligible fun n => prgAdv (G n) (D.distinguisher n (2 * n)) :=
  (Ensemble.pseudorandom_iff_prgAdv (doublingEnsemble G)).1 hG.pseudorandom D

/-- **Truncation of a generator to `n + 1` bits** (first step of Cor-97.a): the first `n + 1`
output bits of `G n` (the stretch `ℓ(n) > n` makes them available). -/
def PRG.truncate (P : PRG) : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool) :=
  fun n s i => P.G n s (Fin.castLE (P.expands n) i)

/-- The stretch `2n + 1` used to produce a length-doubling generator from a one-bit-stretch
generator by [PS10, Lemma 80.5]: it exceeds `n` at every `n` (unlike `2n`). -/
theorem two_mul_add_one_expands (n : ℕ) :
    n < (PolyExpr.add (.mul (.const 2) .var) (.const 1)).eval n := by
  rw [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
    PolyExpr.eval_const]
  omega

/-- **The length-doubling generator obtained from an arbitrary PRG** (Cor-97.a, the "without
loss of generality" of [PS10, proof of Theorem 97.3]): truncate `G` to `n + 1` bits
(`PRG.truncate`), expand the one-bit-stretch generator to `2n + 1` bits by the construction of
[PS10, Lemma 80.5] (`PRG.expand`), and keep the first `2n` bits. -/
def PRG.doubling (P : PRG) : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool) :=
  fun n s i => (PRG.expand P.truncate (.add (.mul (.const 2) .var) (.const 1))
    two_mul_add_one_expands).G n s (Fin.cast (by
      rw [PRG.expand_stretch]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var])
      (Fin.castLE (Nat.le_succ (2 * n)) i))

/-- Closed form of the length-doubling generator: bit `i` of `P.doubling n s` is the last bit
of the truncated generator applied to the `i`-th iterate of `s ↦ init (G₁(s))` on `s`
(`PRG.expand_G`). -/
theorem PRG.doubling_apply (P : PRG) (n : ℕ) (s : Fin n → Bool) (i : Fin (2 * n)) :
    P.doubling n s i =
      P.truncate n ((fun x => Fin.init (P.truncate n x))^[i] s) (Fin.last n) := by
  unfold PRG.doubling
  exact PRG.expand_G_stretch P.truncate _ two_mul_add_one_expands n s _

/-- **Truncation preserves pseudorandomness** (first half of Cor-97.a): if `G` is a secure
PRG then its truncation to `n + 1` bits is a secure one-bit-stretch PRG.

**Proof sketch.** *Easy:* the evaluator of `G` followed by `List.take (n + 1)`
(`Complexity.polyTimeComputable_pairTakePoly (.add .var (.const 1))` on `⟨1^n, G(s)⟩`, with
`1^n = replicate |s| true` by `polyTimeComputable_unaryPoly .var`); `List.take` of `ofFn` is
`ofFn` of the restriction (`List.ofFn_castLE`-style, `List.take_ofFn`). *Pseudorandom:* for a
distinguisher `D` of the truncation, the machine `D'` that truncates its `ℓ(n)`-bit input to
`n + 1` bits and runs `D` (`NUPPT.exists_comp` with `pre := pairTakePoly`) satisfies
`prgAdv (G n) (D'.distinguisher n (ℓ n)) = prgAdv (P.truncate n) (D.distinguisher n (n+1))` by
the sunglass identity `distAdv_comp` with the projection `t ↦ t ∘ castLE` (a uniform
`ℓ(n)`-bit string projects to a uniform `(n+1)`-bit string, `uprob_comp_equiv` on
`Fin.appendEquiv`/`Equiv.funSplitAt`), and `PRG.secure_iff` applied to `hP` gives the
negligible bound; `Negligible.mono` with the equality. -/
theorem PRG.Secure.truncate {P : PRG} (hP : P.Secure) : (PRG.oneBit P.truncate).Secure := by
  have hm : ∀ n, (PolyExpr.add .var (.const 1)).eval n ≤ P.stretch.eval n := fun n => by
    rw [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
    exact P.expands n
  refine (PRG.oneBit_secure_iff _).2 ⟨?_, fun D => ?_⟩
  · obtain ⟨E, hE, hEs⟩ := hP.truncateTo_easy _ hm
    exact ⟨E, hE, fun n s => hEs n s⟩
  · exact hP.truncateTo_negligible _ hm D

/-- **Any PRG yields a length-doubling PRG** (Cor-97.a, [PS10, proof of Theorem 97.3, first
paragraph]): if `G` is a secure PRG then `P.doubling : {0,1}^n → {0,1}^{2n}` is a secure
length-doubling generator.

**Proof sketch.** By `PRG.Secure.truncate` the one-bit-stretch generator `P.truncate` is
secure, so by [PS10, Lemma 80.5] (`prg_expand` with `ℓ := 2 · var + 1`) the expansion to
`2n + 1` bits is a secure `PRG`; `P.doubling` is its truncation to `2n` bits
(`PRG.doubling_apply`, `PRG.expand_G`). *Easy:* the evaluator of the expansion followed by
`List.take (2n)` (`polyTimeComputable_pairTakePoly (.mul (.const 2) .var)`). *Pseudorandom:*
exactly as in `PRG.Secure.truncate`: a distinguisher `D` of `P.doubling` becomes the
distinguisher `D ∘ take (2n)` of the expansion (`NUPPT.exists_comp`), `distAdv_comp` with the
projection `Fin (2n + 1) → Fin (2n)` and `uprob_comp_equiv` identify the advantages, and the
pseudorandomness of the expansion (`PRG.secure_iff`) gives the negligible bound. -/
theorem PRG.Secure.doubling {P : PRG} (hP : P.Secure) : DoublingPRG P.doubling := by
  have hQ : (PRG.expand P.truncate (.add (.mul (.const 2) .var) (.const 1))
      two_mul_add_one_expands).Secure :=
    prg_expand P.truncate _ two_mul_add_one_expands hP.truncate
  have hm : ∀ n, (PolyExpr.mul (.const 2) .var).eval n ≤
      (PRG.expand P.truncate (.add (.mul (.const 2) .var) (.const 1))
        two_mul_add_one_expands).stretch.eval n := fun n => by
    rw [PRG.expand_stretch]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  refine ⟨?_, (Ensemble.pseudorandom_iff_prgAdv _).2 fun D => ?_⟩
  · obtain ⟨E, hE, hEs⟩ := hQ.truncateTo_easy _ hm
    exact ⟨E, hE, fun n s => hEs n s⟩
  · exact hQ.truncateTo_negligible _ hm D

end TCSlib.Cryptography
