/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.HardcoreBit.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as adversaries of the concrete experiments

The bridge between the machine layer (`Complexity.NUPPT`, strings `List Bool`) and the
concrete security experiments of `TCSlib.Cryptography.Foundations.Experiments` (typed
inputs `Fin m → Bool`, adversaries as functions of the input and of a uniform coin string).
An `NUPPT` `A` activated at parameter `n` becomes

* an *inverter* `A.inverter n ℓ m : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)`
  [PS10, Definitions 27.3, 28.4]: `A(1^n, y)` with the output decoded as an `ℓ`-bit string;
* its literal variant `A.inverterLit ℓ m` for [PS10, Definition 26.1] (`A(f(x))`, activation
  at the input length `m`, no `1^n`);
* a *distinguisher* / *predictor* `A.distinguisher n m`, `A.predictor n m`
  [PS10, Definitions 69.4, 75.2, 78.3]: `A(1^n, t) = 1`, i.e. the output is the string `[true]`;
  `A.distinguisherL n` takes an untyped sample.

Inversion with a possibly failing decoder is `invProbOpt` (the probability that the decoded
output is a preimage); it is bridged to the concrete `invProb` by `invProbOpt_le_invProb`
(any default for a failure can only increase the probability) and `invProbOpt_some` (a total
inverter has the same probability). Foundation decision D5: inverses are sought in the
domain at the current parameter, and a wrong-length output counts as failure.

The file also records that "computes `f` with probability one" [PS10, Definition 24.6]
is, on the finite uniform coin space, the same as "for every coin string"
(`Complexity.NUPPT.computes_iff_uprob`), which justifies the frozen form of
`Complexity.NUPPT.Computes`.

**Deviation:** `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable
by `ifEq`).

## Main definitions

* `TCSlib.Cryptography.coinBlock` — the common indexed coin-tape segment.
* `TCSlib.Cryptography.decodeFin` — decode a string as an `ℓ`-bit string, failure on a wrong
  length; `TCSlib.Cryptography.padFin` — pad/truncate (for samplers).
* `TCSlib.Cryptography.blocksEquivX`, `TCSlib.Cryptography.FunFamily.blocks` — the canonical
  block bijection `(Fin (q·ℓ) → X) ≃ (Fin q → Fin ℓ → X)` and its Bool form, with the readers
  `blocksEquivX_apply`, `blocksEquivX_symm_apply`, `FunFamily.blocks_apply`,
  `FunFamily.blocks_symm_apply`.
* `Complexity.NUPPT.inverter`, `Complexity.NUPPT.inverterLit` — an `NUPPT` as an inverter
  (with `1^n`, and literal).
* `Complexity.NUPPT.distinguisher`, `Complexity.NUPPT.distinguisherL`,
  `Complexity.NUPPT.predictor` — an `NUPPT` as a distinguisher / predictor.
* `TCSlib.Cryptography.invProbOpt` — inversion probability of a possibly failing inverter.

## Main results

* `TCSlib.Cryptography.coinBlock_eq`, `TCSlib.Cryptography.length_coinBlock` — the segment
  equation and its full-length condition.
* `TCSlib.Cryptography.decodeFin_ofFn`, `TCSlib.Cryptography.padFin_ofFn` — decoding and
  padding invert `List.ofFn`; `TCSlib.Cryptography.decodeFin_eq_some_iff` — decoding succeeds
  exactly on the encoding.
* `TCSlib.Cryptography.invProbOpt_le_invProb`, `TCSlib.Cryptography.invProbOpt_some` — the
  bridges to the concrete `invProb`.
* `TCSlib.Cryptography.invProbOpt_nonneg`, `TCSlib.Cryptography.invProbOpt_le_one` — bounds.
* `Complexity.NUPPT.computes_iff_uprob` — probability one is every coin string
  [PS10, Definition 24.6].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1–2.2: Definitions 24.6, 26.1, 27.3; §3.1–3.3: Definitions 69.4, 75.2, 78.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definitions 2.1, 2.3, 3.2–3.4 (the concrete experiments).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-- The `i`-th segment of `B` bits of a coin string; a short final segment is truncated. -/
def coinBlock (B i : ℕ) (r : List Bool) : List Bool := (r.drop (i * B)).take B

/-- The defining equation of `coinBlock`: `coinBlock B i r = (r.drop (i·B)).take B`. -/
theorem coinBlock_eq (B i : ℕ) (r : List Bool) : coinBlock B i r = (r.drop (i * B)).take B := rfl

/-- A coin segment has exactly `B` bits when its end lies within the input tape. -/
theorem length_coinBlock {B i : ℕ} {r : List Bool} (h : (i + 1) * B ≤ r.length) :
    (coinBlock B i r).length = B := by
  simp only [coinBlock_eq, List.length_take, List.length_drop]
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

/-- Decode a string as an `ℓ`-bit string: `some` of its bits if the length is exactly `ℓ`,
`none` otherwise (a wrong-length answer of an inverter is a failure, D5). -/
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool) :=
  if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none

/-- The defining equation of `decodeFin`: `decodeFin ℓ w` is `some` of the bits of `w` when
`|w| = ℓ`, and `none` otherwise. -/
theorem decodeFin_eq (ℓ : ℕ) (w : List Bool) :
    decodeFin ℓ w = if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none :=
  rfl

/-- Pad with `false` or truncate a string to exactly `ℓ` bits (the output convention of
samplers, where no failure is possible). -/
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i false

/-- The defining equation of `padFin`: `padFin ℓ w = fun i => w.getD i false`. -/
theorem padFin_def (ℓ : ℕ) (w : List Bool) :
    padFin ℓ w =
      (fun i => w.getD i false :
        Fin ℓ → Bool) := rfl

/-- Bit `i` of `padFin ℓ w` is bit `i` of `w`, default `false`. -/
theorem padFin_apply (ℓ : ℕ) (w : List Bool) (i : Fin ℓ) : padFin ℓ w i = w.getD i false :=
  rfl

/-- Decoding the encoding of an `ℓ`-bit string returns it. -/
theorem decodeFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : decodeFin ℓ (List.ofFn x) = some x := by
  simp [decodeFin]

/-- A decoded string has exactly the decoded length. -/
theorem length_eq_of_decodeFin_eq_some {ℓ : ℕ} {w : List Bool} {x : Fin ℓ → Bool}
    (h : decodeFin ℓ w = some x) : w.length = ℓ := by
  by_contra hw
  simp [decodeFin, hw] at h

/-- **Decoding succeeds exactly on the encoding**: `decodeFin ℓ w = some x ↔ w = List.ofFn x`,
for every width `ℓ` (`ℓ = 0` included) and every string `w`.

**Proof sketch.** A successful decoding has `|w| = ℓ` (`length_eq_of_decodeFin_eq_some`); after
substituting the width, `w = List.ofFn (w.get ·)` (`List.ofFn_get`) decodes to the bits of `w`
(`decodeFin_ofFn`), which are therefore `x`. Conversely `decodeFin_ofFn`. -/
theorem decodeFin_eq_some_iff (ℓ : ℕ) (w : List Bool) (x : Fin ℓ → Bool) :
    decodeFin ℓ w = some x ↔ w = List.ofFn x := by
  constructor
  · intro h
    have hw := length_eq_of_decodeFin_eq_some h
    subst hw
    have h' := decodeFin_ofFn (fun j : Fin w.length => w.get j)
    rw [List.ofFn_get, h, Option.some.injEq] at h'
    rw [h']
    exact (List.ofFn_get w).symm
  · rintro rfl
    exact decodeFin_ofFn x

/-- Padding the encoding of an `ℓ`-bit string returns it. -/
theorem padFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padFin ℓ (List.ofFn x) = x := by
  funext i
  simp [padFin]

/-! ### Blocks of a flat tuple -/

/-- A tuple of `q · ℓ` entries with values in an arbitrary type `X` as `q` consecutive blocks of
`ℓ` entries: block `i`, position `j` is entry `finProdFinEquiv (i, j) = j + ℓ·i` (Mathlib's
`finProdFinEquiv` and `Equiv.curry`). All `q`, `ℓ` (zero included). -/
def blocksEquivX (q ℓ : ℕ) (X : Type*) : (Fin (q * ℓ) → X) ≃ (Fin q → Fin ℓ → X) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl X)).trans (Equiv.curry _ _ _)

/-- The forward reader of `blocksEquivX`: block `i`, position `j` of `x` is entry
`finProdFinEquiv (i, j)` of `x`. -/
theorem blocksEquivX_apply (q ℓ : ℕ) {X : Type*} (x : Fin (q * ℓ) → X) (i : Fin q) (j : Fin ℓ) :
    blocksEquivX q ℓ X x i j = x (finProdFinEquiv (i, j)) := rfl

/-- The inverse of `blocksEquivX` reads block `p.divNat`, position `p.modNat`. -/
theorem blocksEquivX_symm_apply (q ℓ : ℕ) {X : Type*} (t : Fin q → Fin ℓ → X) (p : Fin (q * ℓ)) :
    (blocksEquivX q ℓ X).symm t p = t p.divNat p.modNat := rfl

/-- A string of `q · ℓ` bits as `q` consecutive blocks of `ℓ` bits (block `i` occupies the
positions `ℓ·i, …, ℓ·i + ℓ - 1`): the encoding of the tuple `(x₁, …, x_q)` of
[PS10, Theorem 35.1] as the `q·ℓ`-bit concatenation; the Bool specialization of
`blocksEquivX`. -/
def FunFamily.blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  blocksEquivX q ℓ Bool

/-- The defining equation of `blocks`: block `i`, position `j` is position `ℓ·i + j` of `x`. -/
theorem FunFamily.blocks_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    FunFamily.blocks q ℓ x i j = x (finProdFinEquiv (i, j)) :=
  blocksEquivX_apply q ℓ x i j

/-- The inverse of `blocks` reads block `k.divNat`, position `k.modNat`. -/
theorem FunFamily.blocks_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (k : Fin (q * ℓ)) :
    (FunFamily.blocks q ℓ).symm t k = t k.divNat k.modNat :=
  blocksEquivX_symm_apply q ℓ t k

/-- `A(1^n, y)` as an inverter: output decoded as an `ℓ`-bit string, wrong length = failure
[PS10, Definitions 27.3 and 28.4, the experiment `f(A(1^n, y)) = y`].

**Deviation:** wrong-length output = failure (D5). For a typed family this loses nothing. For
a string function `f : {0,1}* → {0,1}*` the text's experiment also accepts a preimage of
another length, so the typed experiment can count fewer successes and typed one-wayness is
implied by, but weaker than, the text's, unless `|f(x)|` determines `|x|` (length-regular `f`
whose output length is a non-constant `PolyExpr`, hence injective in the input length; with
constant output length neither notion is satisfiable). The proviso is stated where string functions enter the typed world,
`FunFamily.ofString` (`Asymptotic/OneWay.lean`; gate 03a, note 15). -/
def _root_.Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt n (List.ofFn y) r)

/-- The defining equation of `NUPPT.inverter`: the output of `A(1^n, y; r)` decoded as an
`ℓ`-bit string, `A.inverter n ℓ m y r = decodeFin ℓ (A.runAt n (List.ofFn y) r)`. -/
theorem _root_.Complexity.NUPPT.inverter_def (A : NUPPT) (n ℓ m : ℕ) (y : Fin m → Bool)
    (r : A.Coins n) : A.inverter n ℓ m y r = decodeFin ℓ (A.runAt n (List.ofFn y) r) := rfl

/-- The literal inverter `A(y)` of [PS10, Definition 26.1]: activation at parameter `|y| = m`
(the text gives the adversary `f(x)` only; the `1^{|y|}` prefix carries no information). -/
def _root_.Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt m (List.ofFn y) r)

/-- `A(1^n, t)` as a distinguisher: accepts iff the output is the string `[true]`
[PS10, Definition 69.4]. -/
def _root_.Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  fun t r => decide (A.runAt n (List.ofFn t) r = [true])

/-- `A(1^n, w)` as a distinguisher of untyped samples (ciphertexts, views, histories). -/
def _root_.Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool :=
  fun w r => decide (A.runAt n w r = [true])

/-- The defining equation of `distinguisherL`:
`A.distinguisherL n w r = decide (A.runAt n w r = [true])`. -/
theorem _root_.Complexity.NUPPT.distinguisherL_eq (A : NUPPT) (n : ℕ) (w : List Bool)
    (r : A.Coins n) : A.distinguisherL n w r = decide (A.runAt n w r = [true]) := rfl

/-- `A(1^n, y)` as a predictor of a bit: the same verdict convention as a distinguisher
[PS10, Definitions 75.2 and 78.3]. -/
def _root_.Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  A.distinguisher n m

/-- The literal inverter is the inverter at parameter `m`. -/
theorem _root_.Complexity.NUPPT.inverterLit_eq (A : NUPPT) (ℓ m : ℕ) :
    A.inverterLit ℓ m = A.inverter m ℓ m := rfl

/-- The typed distinguisher is the untyped one on `List.ofFn t`. -/
theorem _root_.Complexity.NUPPT.distinguisher_eq (A : NUPPT) (n m : ℕ) (t : Fin m → Bool)
    (r : A.Coins n) : A.distinguisher n m t r = A.distinguisherL n (List.ofFn t) r := rfl

/-- The predictor is the distinguisher. -/
theorem _root_.Complexity.NUPPT.predictor_eq (A : NUPPT) (n m : ℕ) :
    A.predictor n m = A.distinguisher n m := rfl

/-- The inverter succeeds on `(y, r)` iff the machine's output is the encoding of some `x'`. -/
theorem _root_.Complexity.NUPPT.inverter_eq_some_iff (A : NUPPT) (n ℓ m : ℕ) (y : Fin m → Bool)
    (r : A.Coins n) (x' : Fin ℓ → Bool) :
    A.inverter n ℓ m y r = some x' ↔ A.runAt n (List.ofFn y) r = List.ofFn x' := by
  constructor
  · intro h
    have hw : (A.runAt n (List.ofFn y) r).length = ℓ := length_eq_of_decodeFin_eq_some h
    simp only [NUPPT.inverter, decodeFin, dif_pos hw, Option.some.injEq] at h
    subst h
    refine List.ext_get (by simp [hw]) fun i h₁ h₂ => ?_
    simp
  · intro h
    show decodeFin ℓ _ = _
    rw [h, decodeFin_ofFn]

/-- The probability that a possibly failing inverter `A`, given `f x` for uniform `x` and
uniform coins, outputs `some x'` with `f x' = f x` (the typed experiment of
[PS10, Definition 27.3] with a wrong-length output counted as failure, D5). -/
noncomputable def invProbOpt {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : ℝ :=
  uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1

/-- The defining equation of `invProbOpt`:
`invProbOpt f A = Pr_{(x, r)}[∃ x', A(f x, r) = some x' ∧ f x' = f x]`, over uniform
`(x, r) ∈ α × ρ`. -/
theorem invProbOpt_def {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A = uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1 := rfl

/-- Replacing a failure by any default can only increase the inversion probability: the
bridge from `invProbOpt` to the concrete `invProb` [Gar26, Definition 2.1]. -/
theorem invProbOpt_le_invProb {α β ρ : Type*} [Fintype α] [Fintype ρ] [Inhabited α] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default) := by
  rw [invProbOpt_def, invProb_def]
  refine uprob_mono ?_
  rintro ⟨x, r⟩ ⟨x', hx', hf⟩
  simp [hx', hf]

/-- A total inverter has the same probability under both conventions. -/
theorem invProbOpt_some {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → α) :
    invProbOpt f (fun y r => some (A y r)) = invProb f A := by
  unfold invProbOpt
  simp only [invProb_def]
  congr 1
  funext z
  simp

/-- The inversion probability is nonnegative. -/
theorem invProbOpt_nonneg {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : 0 ≤ invProbOpt f A :=
  uprob_nonneg _

/-- The inversion probability is at most one. -/
theorem invProbOpt_le_one {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : invProbOpt f A ≤ 1 :=
  uprob_le_one _

/-- **"With probability one" is "for every coin string"** [PS10, Definition 24.6]: `A`
computes `f` in the frozen sense (`Complexity.NUPPT.Computes`, equality for every coin
string) iff at every parameter and argument the event `A(1^n, y; r) = f(⟨1^n, y⟩)` has
probability one over the uniform coins. (On a finite uniform space an event of probability
one is the whole space, `HardcoreBit.forall_of_uprob_eq_one`.) -/
theorem _root_.Complexity.NUPPT.computes_iff_uprob (A : NUPPT) (f : List Bool → List Bool) :
    A.Computes f ↔
      ∀ n y, uprob (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = 1 := by
  rw [NUPPT.computes_iff]
  constructor
  · intro h n y
    have hp : (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = fun _ => True :=
      funext fun r => propext ⟨fun _ => trivial, fun _ => h n y r⟩
    rw [hp, uprob_true]
  · intro h n y r
    exact HardcoreBit.forall_of_uprob_eq_one (h n y) r

end TCSlib.Cryptography
