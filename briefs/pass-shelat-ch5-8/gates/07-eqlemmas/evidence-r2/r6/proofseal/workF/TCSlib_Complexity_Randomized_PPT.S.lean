/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PolyExpr

attribute [local irreducible] Complexity.PolyTimeComputable Complexity.pairFstD Turing.moveInputPos Turing.pairDecode Turing.pairEncode Turing.Action.apply Turing.Cfg.init Turing.Cfg.inputSymbol Turing.Cfg.workTapeSymbols Turing.FinTM.ComputesFunInTime Turing.FinTM.ComputesInTime Turing.MultiTapeTM.ComputesInTimeAndSpace Turing.MultiTapeTM.initCfg Turing.MultiTapeTM.runFrom Turing.MultiTapeTM.spaceUsed Turing.MultiTapeTM.spaceUsedByTape Turing.MultiTapeTM.step Turing.MultiTapeTM.visitedByTapeHead

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic polynomial-time machines, uniform and non-uniform

The randomized machine model of [PS10, §2.1]: the probabilistic polynomial-time Turing
machine (PPT) [PS10, Definition 23.4] with the worst-case running-time convention
[PS10, Definition 23.5], the notion "computes `f` with probability one"
[PS10, Definition 24.6], and the non-uniform PPT of [PS10, Definition 26.8] in its advice
formulation ("a uniform p.p.t. machine `A` that receives an advice string for each input
length"). One structure, `Complexity.NUPPT`, carries all of them (foundation decisions D3
and D4 of `PassShelatChapter2-4Plan.md`):

* a finite binary machine `M : Turing.FinTM Bool` that halts on **every** input `z` within
  `Ct * (|z| + 1) ^ ct` steps;
* an explicit coin polynomial `coins : PolyExpr` (`coins.eval n` uniform coins at parameter
  `n`) and an advice polynomial `adv : PolyExpr` with an advice function `advice : ℕ → List Bool`
  of length `≤ adv.eval n`;
* the single semantic primitive `output z` (the output tape when the budget expires), which is
  `PolyTimeComputable` (`NUPPT.polyTimeComputable_output`), and conversely every
  `PolyTimeComputable` function is the output of some `NUPPT` (`NUPPT.ofPolyTime`).

The activation at security parameter `n` on argument `y` with coins `r` is
`runAt n y r := output ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with `r : Fin (coins.eval n) → Bool`
(pairs are `Turing.pairEncode`, `1^n = List.replicate n true`). The random tape is part of the
input, so the time bound holds for every coin string, which is exactly the worst-case
convention of [PS10, Definition 23.5]; "`A` computes `f` with probability 1"
[PS10, Definition 24.6] is `NUPPT.Computes`: equality for every coin string (on the finite
uniform coin space, probability one is the same as every coin string, see
`TCSlib.Cryptography.Asymptotic.Adversary`). A PPT [PS10, Definition 23.4] is an `NUPPT` with
empty advice (`NUPPT.Uniform`); `Complexity.PPT` is the subtype. `Computes` does not require
`Uniform`: [PS10, Definition 24.6] is about a randomized algorithm, i.e. a PPT, and is the case
`A.Uniform ∧ A.Computes f`; for a non-uniform `A`, `Computes` is the advice analogue and holds
for uncomputable `f` (advice `[h n]` for an arbitrary `h : ℕ → Bool`, read back by the machine).
So `∃ A : NUPPT, A.Computes f` does not say that a PPT computes `f`. Efficient computation of
`f` on the encodings `⟨1^n, y⟩` is `∃ A, A.Uniform ∧ A.Computes f`
(`NUPPT.exists_uniform_computes`, and conversely `NUPPT.Computes.polyTimeComputable` of
`TCSlib.Complexity.Randomized.Closure`, which gives polynomial-time computability of
`z ↦ f ⟨1^{|fst z|}, snd z⟩`). `Computes` says nothing about `f` off those encodings, so it is
not [PS10, Definition 24.6] for an arbitrary `f : {0,1}* → {0,1}*`, which constrains every
input string (gate 03a, round 2, R2-1). The
input-length-indexed activation `A_{|y|}(y)` of [PS10, Definition 26.8] is `NUPPT.runLit`; the
lemmas about it and about uniformity are in `TCSlib.Complexity.Randomized.NonUniform`.

## Deviations (DESIGN.md §5, items 1–2)

1. `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time in the
   machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
2. `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core (optional
   module).

In detail (D3): a machine that is polynomial-time on well-formed inputs can be clocked by
`Turing.timed_universal` into one that halts on every input, so requiring totality does not
change the class of behaviours (the optional lemma `NUPPT.ofPartial` doing this is not needed
by any theorem of chapters 2–4); the time bound is measured in the length of the machine
input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`, a polynomial in `n + |y|`, so the classes "polynomial in
`n`" (for `|y|` polynomial in `n`, the only case the experiments produce) and "polynomial in
the machine input" coincide.

**Interdefinability of the `1^n`-indexed and the input-length-indexed forms (D3/D4).** The
text indexes advice and coins by the input length (`A_{|x|}(x)`), while `NUPPT` indexes
them by the parameter `n` read from the unary prefix `1^n`. The two are interdefinable in
every experiment of the text: (i) an `NUPPT` run at `n := |y|` is exactly the text's
`A_{|y|}(y)`, by definition (`NUPPT.runLit`; the prefix `1^{|y|}` carries no information);
(ii) conversely, every experiment of the text hands the adversary strings
whose length is a fixed polynomial `ℓ(n)` of the parameter, and an input-length-indexed
machine at length `ℓ(n)` becomes a `1^n`-indexed one by hard-wiring its advice at `ℓ(n)` and
evaluating its coin polynomial at `ℓ(n)` (`exists_reparam_advice` with `φ := ℓ.eval`); for
injective `ℓ` the converse hard-wires `1^n` into the advice at length `ℓ(n)`. The `1^n`
indexing is what makes one random tape per `n` well-typed for the oracle and interactive
layouts of chapters 3–4, where the machine is activated several times at one parameter on
inputs of varying length. Both forms are kept side by side where the text uses the literal
one (Definitions 26.1 and 69.4) and are related by explicit lemmas, never unified silently.

## Main definitions

* `Complexity.NUPPT` — non-uniform PPT [PS10, Definition 26.8, advice formulation]; a PPT
  [PS10, Definition 23.4] is the case `NUPPT.Uniform` (empty advice).
* `Complexity.NUPPT.output` — the output of the machine on a raw input (the semantic
  primitive); `NUPPT.timeBound`, `NUPPT.coinLen`, `NUPPT.adviceLen`.
* `Complexity.NUPPT.advInput` — the adversary input `⟨1^n, y⟩`; `NUPPT.Coins` — the coin type
  at parameter `n`; `NUPPT.runAt`, `NUPPT.runAtL`, `NUPPT.runLit` — activations.
* `Complexity.NUPPT.Uniform` — no advice (a PPT); `Complexity.PPT` — the subtype.
* `Complexity.NUPPT.Computes` — computes `f` with probability one: [PS10, Definition 24.6] for a
  uniform `A` (`NUPPT.Uniform`), the advice analogue otherwise.
* `Complexity.NUPPT.ofPolyTime`, `Complexity.NUPPT.ofPolyTimeUniform` — the `NUPPT` with a
  given polynomial-time output function, with and without advice.

## Main results

* `Complexity.NUPPT.output_spec`, `NUPPT.computesFunInTime`,
  `NUPPT.polyTimeComputable_output` — the output function is computed by the machine within
  its budget, hence is polynomial-time computable.
* `Complexity.NUPPT.output_eq_of_computesInTime` — determinism: any completed computation of
  the machine names `output`.
* `Complexity.NUPPT.output_ofPolyTime`, `NUPPT.ofPolyTimeUniform_uniform` — the converse
  direction: `ofPolyTime hf` outputs `f`, and `ofPolyTimeUniform` is uniform.
* `Complexity.NUPPT.exists_uniform_computes` — every polynomial-time computable function is
  computed with probability one by a PPT [PS10, Definition 24.6, non-vacuity].
* `Complexity.NUPPT.nonempty` — the class is inhabited.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1: Definitions 23.4, 23.5, 24.6 and 26.8.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Definition 1.3, time-bounded computation; §6.3, advice.)
-/

namespace Complexity

open Turing

/-- A non-uniform probabilistic polynomial-time machine [PS10, Definition 26.8, advice
formulation]: a finite binary machine halting on **every** input `z` within
`Ct (|z|+1)^ct` steps, the explicit polynomial `coins` giving the number of uniform coins at
parameter `n`, and an advice string of length at most `adv.eval n` per parameter.
A PPT [PS10, Definition 23.4] is the case of empty advice (`Uniform`); the time bound holds
for every coin string, the worst-case convention of [PS10, Definition 23.5].

**Deviation:** `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time
in the machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
**Deviation:** `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core
(optional module). -/
structure NUPPT where
  /-- The underlying deterministic finite machine; coins and advice are input components. -/
  M : FinTM Bool
  /-- Coefficient of the running-time bound `Ct * (|z| + 1) ^ ct`. -/
  Ct : ℕ
  /-- Degree of the running-time bound. -/
  ct : ℕ
  /-- The coin polynomial: `coins.eval n` uniform coins at parameter `n`. -/
  coins : PolyExpr
  /-- The advice polynomial: `|advice n| ≤ adv.eval n`. -/
  adv : PolyExpr
  /-- The advice string per parameter (empty for a uniform machine). -/
  advice : ℕ → List Bool
  /-- The advice is polynomially bounded. -/
  advice_length : ∀ n, (advice n).length ≤ adv.eval n
  /-- The machine halts on every input within its polynomial budget. -/
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT

variable (A : NUPPT)

/-- The running-time budget of `A` on inputs of length `m`: `Ct * (m + 1) ^ ct`. -/
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct

/-- The number of coins of `A` at parameter `n`. -/
def coinLen (n : ℕ) : ℕ := A.coins.eval n

/-- The defining equation of `coinLen`: `A.coinLen n = A.coins.eval n`. -/
theorem coinLen_eq (n : ℕ) : A.coinLen n = A.coins.eval n := rfl

/-- The advice-length bound of `A` at parameter `n`. -/
def adviceLen (n : ℕ) : ℕ := A.adv.eval n

/-- The output of `A` on the raw machine input `z`: the output tape when the budget expires
(the machine has halted by then, `output_spec`). This is the single semantic primitive; all
activations are instances of it. -/
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output

/-- The machine halts on `z` within its budget with `output z` on the output tape. -/
theorem output_spec (z : List Bool) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length) := by
  obtain ⟨out, h⟩ := A.halts z
  obtain ⟨hs, -⟩ := (FinTM.computesInTime_iff _ _ _ _).mp h
  exact (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩

/-- The machine computes the function `output` within the budget `timeBound`. -/
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound :=
  fun z => A.output_spec z

/-- The output function of an `NUPPT` is polynomial-time computable: the black box through
which every reduction of the campaign is exhibited as a machine (D2). -/
theorem polyTimeComputable_output : PolyTimeComputable A.output :=
  ⟨A.M, A.Ct, A.ct, A.computesFunInTime⟩

/-- Determinism: any completed computation of the machine on `z` produces `output z`
(`Turing.FinTM.ComputesInTime.output_unique`). -/
theorem output_eq_of_computesInTime {z w : List Bool} {t : ℕ} (h : A.M.ComputesInTime z w t) :
    A.output z = w :=
  (A.output_spec z).output_unique h

/-- The output is no longer than the budget (a machine emits at most one symbol per step,
`Turing.MultiTapeTM.output_length_le`). -/
theorem output_length_le (z : List Bool) : (A.output z).length ≤ A.timeBound z.length :=
  A.M.tm.output_length_le z (A.timeBound z.length)

/-- The adversary input `⟨1^n, y⟩`: the unary security parameter paired with the argument,
exactly as the text writes `A(1^n, y)` [PS10, Definition 27.3]. -/
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y

/-- The defining equation of `advInput`: `advInput n y = pairEncode (List.replicate n true) y`
(the pair `⟨1^n, y⟩`). -/
theorem advInput_eq (n : ℕ) (y : List Bool) :
    advInput n y = pairEncode (List.replicate n true) y := rfl

/-- The length of the adversary input `⟨1^n, y⟩` is `2n + 2 + |y|`. -/
theorem length_advInput (n : ℕ) (y : List Bool) : (advInput n y).length = 2 * n + 2 + y.length := by
  simp [advInput, length_pairEncode]

/-- The coin type of `A` at parameter `n`: `coins.eval n` uniform bits
[PS10, Definition 23.4, "each bit of the random tape is uniformly and independently chosen"]. -/
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool

/-- Activation at parameter `n` on argument `y` with coins `r`: machine input
`⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The sampler `r ↦ runAt n y r` on the uniform coin type
`Coins n` is the distribution `A(1^n, y)` of the text. -/
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))

/-- Activation with an untyped coin string (the interactive and oracle layouts of
chapters 3–4 hand the machine a coin string of the right length as a list). -/
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)

/-- The defining equation of `runAtL`:
`A.runAtL n y r = A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)`. -/
theorem runAtL_eq (n : ℕ) (y r : List Bool) :
    A.runAtL n y r = A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r) := rfl

/-- The typed activation is the untyped one on `List.ofFn r`. -/
theorem runAt_eq (n : ℕ) (y : List Bool) (r : A.Coins n) :
    A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl

/-- **The coins of two machines with the same coin polynomial**: `A.Coins n ≃ B.Coins n` when
`A.coins = B.coins` (`finCongr` on the coin lengths). A construction that keeps the coins of the
machine it is built from publishes its coin identification through it, so that consumers move
between the two coin types without reducing `coinLen` or the construction. -/
def coinsCongr {A B : NUPPT} (h : A.coins = B.coins) (n : ℕ) : A.Coins n ≃ B.Coins n :=
  Equiv.arrowCongr (finCongr (by rw [coinLen_eq, coinLen_eq, h])) (Equiv.refl Bool)

/-- The coin equivalence keeps the coin string: `List.ofFn (coinsCongr h n r) = List.ofFn r`. -/
theorem coinsCongr_ofFn {A B : NUPPT} (h : A.coins = B.coins) (n : ℕ) (r : A.Coins n) :
    List.ofFn (coinsCongr h n r) = List.ofFn r :=
  (List.ofFn_congr (by rw [coinLen_eq, coinLen_eq, h]) r).symm

/-- Running `B` on coins carried over from `A`: `B.runAt n y (coinsCongr h n r) =
B.runAtL n y (List.ofFn r)`. -/
theorem runAt_coinsCongr {A B : NUPPT} (h : A.coins = B.coins) (n : ℕ) (y : List Bool)
    (r : A.Coins n) : B.runAt n y (coinsCongr h n r) = B.runAtL n y (List.ofFn r) := by
  rw [runAt_eq, coinsCongr_ofFn]

/-- **The coins of a machine with a known coin polynomial**: `A.Coins n ≃ {0,1}^{c(n)}` when
`A.coins = c` (`finCongr` on the coin length). The interface through which a statement reads the
coins of a construction as bit strings of the polynomial's length, without reducing `coinLen` or
the construction. -/
def coinsEquivPoly {A : NUPPT} {c : PolyExpr} (h : A.coins = c) (n : ℕ) :
    A.Coins n ≃ (Fin (c.eval n) → Bool) :=
  Equiv.arrowCongr (finCongr (by rw [coinLen_eq, h])) (Equiv.refl Bool)

/-- The coin equivalence keeps the coin string:
`List.ofFn (coinsEquivPoly h n r) = List.ofFn r`. -/
theorem coinsEquivPoly_ofFn {A : NUPPT} {c : PolyExpr} (h : A.coins = c) (n : ℕ) (r : A.Coins n) :
    List.ofFn (coinsEquivPoly h n r) = List.ofFn r :=
  (List.ofFn_congr (by rw [coinLen_eq, h]) r).symm

/-- The inverse coin equivalence keeps the coin string:
`List.ofFn ((coinsEquivPoly h n).symm w) = List.ofFn w`. -/
theorem coinsEquivPoly_symm_ofFn {A : NUPPT} {c : PolyExpr} (h : A.coins = c) (n : ℕ)
    (w : Fin (c.eval n) → Bool) : List.ofFn ((coinsEquivPoly h n).symm w) = List.ofFn w := by
  rw [← coinsEquivPoly_ofFn h n, Equiv.apply_symm_apply]

/-- The input-length-indexed activation `A_{|y|}(y)` of [PS10, Definition 26.8]: the
parameter is the input length (the `1^{|y|}` prefix carries no information). It is the layout
of the literal forms of [PS10, Definition 26.1] and [PS10, Definition 69.4] (D5). -/
def runLit (y : List Bool) (r : A.Coins y.length) : List Bool := A.runAt y.length y r

/-- `A` is *uniform* — a PPT [PS10, Definition 23.4] — when its advice is empty at every
parameter. -/
def Uniform : Prop := ∀ n, A.advice n = []

/-- Uniformity is the conjunction of the advice clauses (definitional unfolding):
`A.Uniform ↔ ∀ n, A.advice n = []`. -/
theorem uniform_iff : A.Uniform ↔ ∀ n, A.advice n = [] := Iff.rfl

/-- A uniform machine has empty advice at every parameter. -/
theorem Uniform.advice_eq {A : NUPPT} (h : A.Uniform) (n : ℕ) : A.advice n = [] := h n

/-- `A` computes `f` with probability one [PS10, Definition 24.6]: at every parameter `n`,
on every argument `y` and for **every** coin string `r`, `A(1^n, y; r) = f(⟨1^n, y⟩)`. On
the finite uniform coin space "probability one" is the same as "every coin string"
(`TCSlib.Cryptography.Asymptotic.Adversary`, `NUPPT.computes_iff_uprob`).

The definition does not require `A.Uniform`. [PS10, Definition 24.6] is about a randomized
algorithm, i.e. a PPT, and is the case `A.Uniform ∧ A.Computes f`. For a non-uniform `A` this
is the advice analogue, which holds for uncomputable functions: with advice `[h n]` at
parameter `n` for an arbitrary `h : ℕ → Bool` (`ofPolyTime` of the advice projection), `A`
computes `w ↦ [h |fst w|]`. So `∃ A : NUPPT, A.Computes f` does **not** mean "a PPT computes
`f`"; where the text means efficient computation, the form is `A.Uniform ∧ A.Computes f`
(`exists_uniform_computes`; conversely `NUPPT.Computes.polyTimeComputable` of
`TCSlib.Complexity.Randomized.Closure`, which assumes `Uniform`).

`Computes f` constrains `f` only on the encodings `advInput n y = ⟨1^n, y⟩`: off them `f` is
arbitrary, even uncomputable, so `A.Uniform ∧ A.Computes f` is efficient computation of `f` on
those encodings, not of `f` on every string (the converse gives polynomial-time computability of
`z ↦ f ⟨1^{|fst z|}, snd z⟩`; gate 03a, round 2, R2-1). -/
def Computes (f : List Bool → List Bool) : Prop :=
  ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)

/-- A machine that computes `f` returns `f ⟨1^n, y⟩` on every activation. -/
theorem Computes.runAt_eq {f : List Bool → List Bool} (h : A.Computes f) (n : ℕ)
    (y : List Bool) (r : A.Coins n) : A.runAt n y r = f (advInput n y) :=
  h n y r

/-- The `NUPPT` whose machine is a polynomial-time machine for `f` (chosen from the
`PolyTimeComputable` witness), with the given coin polynomial and advice. Its output function
is `f` (`output_ofPolyTime`). This is how every reduction of the campaign is packaged: the
reduction is an FP function of the raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` (D2). -/
noncomputable def ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool)
    (hα : ∀ n, (advice n).length ≤ adv.eval n) : NUPPT where
  M := Classical.choose hf
  Ct := Classical.choose (Classical.choose_spec hf)
  ct := Classical.choose (Classical.choose_spec (Classical.choose_spec hf))
  coins := coins
  adv := adv
  advice := advice
  advice_length := hα
  halts := fun z => ⟨f z, Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hf)) z⟩

/-- The output function of `ofPolyTime hf …` is `f` (determinism of completed outputs). -/
theorem output_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).output = f := by
  funext z
  exact (ofPolyTime hf coins adv advice hα).output_eq_of_computesInTime
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hf)) z)

/-- The coin polynomial of `ofPolyTime hf coins adv advice hα` is `coins`. -/
@[simp] theorem coins_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).coins = coins := rfl

/-- **The coins of `ofPolyTime hf coins …`** are `coins(n)` bits: the published equivalence
`(ofPolyTime hf coins adv advice hα).Coins n ≃ {0,1}^{coins(n)}` (`coinsEquivPoly`). -/
noncomputable def coinsEquiv_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (n : ℕ) : (ofPolyTime hf coins adv advice hα).Coins n ≃ (Fin (coins.eval n) → Bool) :=
  coinsEquivPoly (coins_ofPolyTime hf coins adv advice hα) n

/-- The coin equivalence of `ofPolyTime` keeps the coin string. -/
theorem coinsEquiv_ofPolyTime_ofFn {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (n : ℕ) (r : (ofPolyTime hf coins adv advice hα).Coins n) :
    List.ofFn (coinsEquiv_ofPolyTime hf coins adv advice hα n r) = List.ofFn r :=
  coinsEquivPoly_ofFn _ n r

/-- The advice polynomial of `ofPolyTime hf coins adv advice hα` is `adv`. -/
@[simp] theorem adv_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).adv = adv := rfl

/-- The advice of `ofPolyTime hf coins adv advice hα` is `advice`. -/
@[simp] theorem advice_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).advice = advice := rfl

/-- The untyped activation of `ofPolyTime hf …` is `f` on the raw layout. -/
theorem runAtL_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (n : ℕ) (y r : List Bool) :
    (ofPolyTime hf coins adv advice hα).runAtL n y r =
      f (pairEncode (pairEncode (advInput n y) (advice n)) r) := by
  simp [runAtL, output_ofPolyTime]

/-- The uniform `NUPPT` with output function `f`: `ofPolyTime` with empty advice. -/
noncomputable def ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : NUPPT :=
  ofPolyTime hf coins (.const 0) (fun _ => []) (fun _ => by simp)

/-- `ofPolyTimeUniform hf coins` is uniform. -/
theorem ofPolyTimeUniform_uniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).Uniform := fun _ => rfl

/-- The output function of `ofPolyTimeUniform hf coins` is `f`. -/
theorem output_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).output = f :=
  output_ofPolyTime hf coins (.const 0) (fun _ => []) (fun _ => by simp)

/-- The coin polynomial of `ofPolyTimeUniform hf coins` is `coins`. -/
@[simp] theorem coins_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).coins = coins := rfl

/-- **The coins of `ofPolyTimeUniform hf coins`** are `coins(n)` bits: the published equivalence
`(ofPolyTimeUniform hf coins).Coins n ≃ {0,1}^{coins(n)}` (`coinsEquivPoly`). -/
noncomputable def coinsEquiv_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) (n : ℕ) : (ofPolyTimeUniform hf coins).Coins n ≃ (Fin (coins.eval n) → Bool) :=
  coinsEquivPoly (coins_ofPolyTimeUniform hf coins) n

/-- The coin equivalence of `ofPolyTimeUniform` keeps the coin string. -/
theorem coinsEquiv_ofPolyTimeUniform_ofFn {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) (n : ℕ) (r : (ofPolyTimeUniform hf coins).Coins n) :
    List.ofFn (coinsEquiv_ofPolyTimeUniform hf coins n r) = List.ofFn r :=
  coinsEquivPoly_ofFn _ n r

/-- The untyped activation of `ofPolyTimeUniform hf coins` is `f` on the raw layout with
empty advice. -/
theorem runAtL_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) (n : ℕ) (y r : List Bool) :
    (ofPolyTimeUniform hf coins).runAtL n y r =
      f (pairEncode (pairEncode (advInput n y) []) r) := by
  simp [runAtL, ofPolyTimeUniform, output_ofPolyTime]

/-- **Non-vacuity of [PS10, Definition 24.6].** Every polynomial-time computable function
`f` is computed with probability one by a PPT (a uniform `NUPPT`): the machine for
`f ∘ pairFstD ∘ pairFstD` applied to the raw input `⟨⟨⟨1^n, y⟩, []⟩, r⟩` ignores the advice
and the coins and returns `f ⟨1^n, y⟩`. (This is the direction "`PolyTimeComputable f` gives a
PPT computing `f`" of the equivalence behind Deviation 3, `FunFamily.Easy`.) -/
theorem exists_uniform_computes {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : ∃ A : NUPPT, A.Uniform ∧ A.coins = coins ∧ A.Computes f := by
  have hF : PolyTimeComputable fun z => f (pairFstD (pairFstD z)) :=
    hf.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  refine ⟨ofPolyTimeUniform hF coins, ofPolyTimeUniform_uniform hF coins, rfl, fun n y r => ?_⟩
  rw [runAt_eq, runAtL_ofPolyTimeUniform]
  simp

end NUPPT

/-- PPT [PS10, Definition 23.4] = non-uniform PPT with empty advice: the subtype of uniform
`NUPPT`s. -/
def PPT : Type 1 := {A : NUPPT // A.Uniform}

/-- Non-vacuity: the class is inhabited (the identity machine with no coins). -/
theorem NUPPT.nonempty : Nonempty NUPPT :=
  ⟨NUPPT.ofPolyTimeUniform polyTimeComputable_id (.const 0)⟩

/-- Non-vacuity: the class of PPTs is inhabited. -/
theorem PPT.nonempty : Nonempty PPT :=
  ⟨⟨NUPPT.ofPolyTimeUniform polyTimeComputable_id (.const 0),
    NUPPT.ofPolyTimeUniform_uniform _ _⟩⟩

end Complexity
