import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.CircuitComplexity.Advice
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.OneWayFunctions.Amplification
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import TCSlib.Cryptography.Pseudorandom.Functions.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! # Scratch: FROZEN signatures for the Pass–shelat ch. 2–4 computational-model layer -/

namespace Complexity

open Turing

/-! ## PolyExpr (TCSlib/Complexity/Randomized/PolyExpr.lean) -/

/-- Syntactic polynomial expressions in the parameter `n`: every length of the campaign
(coins, advice, input/output lengths, query and round budgets) is one of these, never an
abstract `ℕ → ℕ`. `normal C c` is the campaign normal form `C * (n + 1) ^ c`. -/
inductive PolyExpr : Type
  | const : ℕ → PolyExpr
  | var : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  deriving DecidableEq, Repr

namespace PolyExpr

/-- Evaluation at the parameter `n`. -/
def eval : PolyExpr → ℕ → ℕ
  | const c, _ => c
  | var, n => n
  | add p q, n => p.eval n + q.eval n
  | mul p q, n => p.eval n * q.eval n
  | pow p c, n => (p.eval n) ^ c

/-- Substitution `p[q/n]`. -/
def subst : PolyExpr → PolyExpr → PolyExpr
  | const c, _ => const c
  | var, q => q
  | add p p', q => add (p.subst q) (p'.subst q)
  | mul p p', q => mul (p.subst q) (p'.subst q)
  | pow p c, q => pow (p.subst q) c

/-- The campaign normal form `C * (n + 1) ^ c`. -/
def normal (C c : ℕ) : PolyExpr := mul (const C) (pow (add var (const 1)) c)

@[simp] theorem eval_const (c n : ℕ) : (const c).eval n = c := rfl
@[simp] theorem eval_var (n : ℕ) : var.eval n = n := rfl
@[simp] theorem eval_add (p q : PolyExpr) (n : ℕ) : (add p q).eval n = p.eval n + q.eval n := rfl
@[simp] theorem eval_mul (p q : PolyExpr) (n : ℕ) : (mul p q).eval n = p.eval n * q.eval n := rfl
@[simp] theorem eval_pow (p : PolyExpr) (c n : ℕ) : (pow p c).eval n = (p.eval n) ^ c := rfl
theorem eval_normal (C c n : ℕ) : (normal C c).eval n = C * (n + 1) ^ c := rfl

theorem eval_subst (p q : PolyExpr) (n : ℕ) : (p.subst q).eval n = p.eval (q.eval n) := by
  induction p <;> simp_all [subst, eval]

/-- Evaluation is monotone in the parameter. -/
theorem eval_mono (p : PolyExpr) : Monotone p.eval := by
  induction p with
  | const k => intro a b _; exact le_rfl
  | var => intro a b h; exact h
  | add p q hp hq => intro a b h; exact Nat.add_le_add (hp h) (hq h)
  | mul p q hp hq => intro a b h; exact Nat.mul_le_mul (hp h) (hq h)
  | pow p k hp => intro a b h; exact Nat.pow_le_pow_left (hp h) k

/-- Every expression is bounded by a normal form: the bridge to `PolyBound`. -/
theorem eval_le (p : PolyExpr) : ∃ C c : ℕ, ∀ n, p.eval n ≤ C * (n + 1) ^ c := by
  induction p with
  | const k => exact ⟨k, 0, fun n => by simp⟩
  | var => exact ⟨1, 1, fun n => by simp⟩
  | add p q hp hq =>
    obtain ⟨C₁, c₁, h₁⟩ := hp
    obtain ⟨C₂, c₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, max c₁ c₂, fun n => ?_⟩
    have e1 : (n + 1) ^ c₁ ≤ (n + 1) ^ (max c₁ c₂) :=
      Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_left _ _)
    have e2 : (n + 1) ^ c₂ ≤ (n + 1) ^ (max c₁ c₂) :=
      Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_right _ _)
    calc (add p q).eval n = p.eval n + q.eval n := rfl
      _ ≤ C₁ * (n + 1) ^ c₁ + C₂ * (n + 1) ^ c₂ := Nat.add_le_add (h₁ n) (h₂ n)
      _ ≤ C₁ * (n + 1) ^ (max c₁ c₂) + C₂ * (n + 1) ^ (max c₁ c₂) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
      _ = (C₁ + C₂) * (n + 1) ^ (max c₁ c₂) := by ring
  | mul p q hp hq =>
    obtain ⟨C₁, c₁, h₁⟩ := hp
    obtain ⟨C₂, c₂, h₂⟩ := hq
    refine ⟨C₁ * C₂, c₁ + c₂, fun n => ?_⟩
    calc (mul p q).eval n = p.eval n * q.eval n := rfl
      _ ≤ (C₁ * (n + 1) ^ c₁) * (C₂ * (n + 1) ^ c₂) := Nat.mul_le_mul (h₁ n) (h₂ n)
      _ = (C₁ * C₂) * (n + 1) ^ (c₁ + c₂) := by ring
  | pow p k hp =>
    obtain ⟨C, c, h⟩ := hp
    refine ⟨C ^ k, c * k, fun n => ?_⟩
    calc (pow p k).eval n = (p.eval n) ^ k := rfl
      _ ≤ (C * (n + 1) ^ c) ^ k := Nat.pow_le_pow_left (h n) k
      _ = C ^ k * (n + 1) ^ (c * k) := by rw [mul_pow, ← pow_mul]

end PolyExpr

/-- `1^{p(|x|)}` is polynomial-time computable for every syntactic polynomial `p`
(induction on `p`: `polyTimeComputable_const`, `_unary`, `.append`, and the new unary
multiplication primitive `computesFunInTime_unaryMul` for `mul`/`pow`). -/
theorem polyTimeComputable_unaryPoly (p : PolyExpr) :
    PolyTimeComputable fun x => List.replicate (p.eval x.length) true := by
  sorry

/-! ## NUPPT (TCSlib/Complexity/Randomized/PPT.lean) -/

/-- A non-uniform probabilistic polynomial-time machine [PS10, Definition 26.8, advice
formulation]: a finite binary machine halting on **every** input `z` within
`Ct (|z|+1)^ct` steps, the explicit polynomial `coins` giving the number of uniform coins at
parameter `n`, and an advice string of length at most `adv.eval n` per parameter.
A PPT [PS10, Definition 23.4] is the case of empty advice (`Uniform`). -/
structure NUPPT where
  M : FinTM Bool
  Ct : ℕ
  ct : ℕ
  coins : PolyExpr
  adv : PolyExpr
  advice : ℕ → List Bool
  advice_length : ∀ n, (advice n).length ≤ adv.eval n
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT

variable (A : NUPPT)

def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct
def coinLen (n : ℕ) : ℕ := A.coins.eval n
def adviceLen (n : ℕ) : ℕ := A.adv.eval n

/-- The output tape when the budget expires (the machine has halted by then). -/
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output

theorem output_spec (z : List Bool) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length) := by
  obtain ⟨out, h⟩ := A.halts z
  obtain ⟨hs, -⟩ := (FinTM.computesInTime_iff _ _ _ _).mp h
  exact (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩

theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound :=
  fun z => A.output_spec z

theorem polyTimeComputable_output : PolyTimeComputable A.output :=
  ⟨A.M, A.Ct, A.ct, A.computesFunInTime⟩

theorem output_eq_of_computesInTime {z w : List Bool} {t : ℕ} (h : A.M.ComputesInTime z w t) :
    A.output z = w :=
  (A.output_spec z).output_unique h

/-- The adversary input `⟨1^n, y⟩`. -/
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y

theorem length_advInput (n : ℕ) (y : List Bool) : (advInput n y).length = 2 * n + 2 + y.length := by
  simp [advInput, length_pairEncode]

abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool

/-- Activation at parameter `n` on argument `y` with coins `r`: machine input
`⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. -/
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))

/-- Untyped coins (interactive and oracle layouts). -/
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)

theorem runAt_eq (n : ℕ) (y : List Bool) (r : A.Coins n) :
    A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl

/-- The input-length-indexed activation `A_{|y|}(y)` of [PS10, Definition 26.8]: the
parameter is the input length (the `1^{|y|}` prefix carries no information). -/
def runLit (y : List Bool) (r : A.Coins y.length) : List Bool := A.runAt y.length y r

def Uniform : Prop := ∀ n, A.advice n = []

/-- Computes `f` with probability one [PS10, Definition 24.6]. -/
def Computes (f : List Bool → List Bool) : Prop :=
  ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)

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

theorem output_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).output = f := by
  funext z
  exact (ofPolyTime hf coins adv advice hα).output_eq_of_computesInTime
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hf)) z)

noncomputable def ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : NUPPT :=
  ofPolyTime hf coins (.const 0) (fun _ => []) (fun _ => by simp)

theorem ofPolyTimeUniform_uniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).Uniform := fun _ => rfl

end NUPPT

/-- PPT [PS10, Definition 23.4] = non-uniform PPT with empty advice. -/
def PPT : Type 1 := {A : NUPPT // A.Uniform}

/-- Non-vacuity: the class is inhabited. -/
theorem NUPPT.nonempty : Nonempty NUPPT :=
  ⟨NUPPT.ofPolyTimeUniform polyTimeComputable_id (.const 0)⟩

/-! ## Primitives (TCSlib/Complexity/Randomized/Primitives.lean) -/

namespace Turing.FinTM

/-- NEW primitive: `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩` (coin splitting at a unary length). -/
theorem computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
          | none => [])
        fun n => c * (n + 1) := by
  sorry

/-- NEW primitive: unary multiplication `⟨1^a, 1^b⟩ ↦ 1^{a·b}` (makes every `PolyExpr`
unary-computable without the repetition lemma). -/
theorem computesFunInTime_unaryMul :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (u, v) => List.replicate (u.length * v.length) true
          | none => [])
        fun n => c * (n + 1) ^ 2 := by
  sorry

end Turing.FinTM

theorem polyTimeComputable_pairTakePoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).take (p.eval (pairFstD z).length) := by
  sorry

theorem polyTimeComputable_pairDropPoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).drop (p.eval (pairFstD z).length) := by
  sorry

/-! ## Repetition (TCSlib/Complexity/Randomized/Repetition.lean) -/

/-- The load-bearing lemma: polynomially many rounds of a polynomial-time step with a
polynomially bounded orbit; first accepted orbit point's payload (`[]` on exhaustion). -/
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
  sorry

theorem polyTimeComputable_iterate {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x => g^[R.eval x.length] x := by
  sorry

theorem polyTimeComputable_iterateEmit {g emit : List Bool → List Bool}
    (hg : PolyTimeComputable g) (hemit : PolyTimeComputable emit) (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      (List.range (R.eval x.length + 1)).flatMap fun i => emit (g^[i] x) := by
  sorry

theorem polyTimeComputable_majority :
    PolyTimeComputable fun w => [decide (w.length < 2 * w.count true)] := by
  sorry

theorem polyTimeComputable_pairXor :
    PolyTimeComputable fun z => List.zipWith xor (pairFstD z) (pairSndD z) := by
  sorry

theorem polyTimeComputable_pairEq :
    PolyTimeComputable fun z => [decide (pairFstD z = pairSndD z)] := by
  sorry

/-- Apply `g` to the consecutive blocks of length `b.eval |pairFstD z|` of `pairSndD z`
and concatenate (block map; `pairFstD z` carries `1^n`). -/
theorem polyTimeComputable_blockMap (b : PolyExpr) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun z =>
      (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
        g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length)) := by
  sorry

/-! ## Closure (TCSlib/Complexity/Randomized/Closure.lean) -/

theorem NUPPT.exists_comp (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r) := by
  sorry

/-- Parameter change `n ↦ p(n)` (uniform: `1^{p(n)}` is computed). -/
theorem NUPPT.exists_reparam (A : NUPPT) (p : PolyExpr) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ (A.Uniform → B.Uniform) ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (p.eval n) y r := by
  sorry

/-- Parameter change along an arbitrary polynomially bounded `φ` (non-uniform: `1^{φ n}` and
`A.advice (φ n)` are advice); extra coins are unread. -/
theorem NUPPT.exists_reparam_advice (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr)
    (hφ : ∀ n, φ n ≤ p.eval n) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (φ n) y (r.take (A.coinLen (φ n))) := by
  sorry

theorem NUPPT.exists_withAdvice (A : NUPPT) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = A.coins ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (β n)) r := by
  sorry

/-- Extra coins passed as data: the first `p n` coins become part of the input. -/
theorem NUPPT.exists_split (A : NUPPT) (p : PolyExpr) :
    ∃ B : NUPPT, B.coins = .add p A.coins ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r =
        A.runAtL n (pairEncode y (r.take (p.eval n))) (r.drop (p.eval n)) := by
  sorry

/-- Sequential composition with input pass-through and fresh coins (sunglass). -/
theorem NUPPT.exists_seq (A B : NUPPT) :
    ∃ C : NUPPT, C.coins = .add A.coins B.coins ∧ (A.Uniform → B.Uniform → C.Uniform) ∧
      ∀ n y r, C.runAtL n y r =
        B.runAtL n (pairEncode y (A.runAtL n y (r.take (A.coinLen n)))) (r.drop (A.coinLen n)) := by
  sorry

/-- Def 26.8 (advice form) decides exactly the languages of `DTIMEAdvice`-style machines
(sanity bridge to `Turing.FinTM.DecidesWithAdviceInTime`; not on the critical path). -/
theorem NUPPT.decides_of_decidesWithAdviceInTime (M : FinTM Bool) (L : Language Bool)
    (α : ℕ → List Bool) (C c Ca ca : ℕ) (hα : ∀ n, (α n).length = Ca * (n + 1) ^ ca)
    (h : M.DecidesWithAdviceInTime L α (fun n => C * (n + 1) ^ c)) :
    ∃ A : NUPPT, ∀ x (r : A.Coins x.length),
      A.runAt x.length x r = [MultiTapeTM.indicator (L : Set (List Bool)) x] := by
  sorry

end Complexity

namespace TCSlib.Cryptography

open Complexity Turing

/-! ## Sampling (TCSlib/Cryptography/Asymptotic/Sampling.lean) -/

/-- Statistical closeness of two samplers in the sup-over-test-sets form (usable for
samples in the infinite type `List Bool`). -/
def StatClose {σ τ γ : Type*} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
  ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ

theorem distAdv_le_of_statClose {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ]
    (X : σ → γ) (Y : τ → γ) {δ : ℝ} (h : StatClose X Y δ) (D : γ → ρ → Bool) :
    distAdv X Y D ≤ δ := by
  sorry

theorem StatClose.prod {σ σ' τ τ' γ γ' : Type*} [Fintype σ] [Fintype σ'] [Fintype τ] [Fintype τ']
    {X : σ → γ} {X' : τ → γ} {Y : σ' → γ'} {Y' : τ' → γ'} {δ δ' : ℝ}
    (h : StatClose X X' δ) (h' : StatClose Y Y' δ') :
    StatClose (fun z : σ × σ' => (X z.1, Y z.2)) (fun z : τ × τ' => (X' z.1, Y' z.2)) (δ + δ') := by
  sorry

theorem StatClose.map {σ τ γ γ' : Type*} [Fintype σ] [Fintype τ] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (g : γ → γ') : StatClose (fun s => g (X s)) (fun t => g (Y t)) δ := by
  sorry

/-- The number with the given binary digits (most significant first). -/
def bitsToNat {k : ℕ} (b : Fin k → Bool) : ℕ :=
  (List.ofFn b).foldl (fun a c => 2 * a + (if c then 1 else 0)) 0

/-- One rejection trial: `k` bits read as a number, accepted iff below `m`. -/
def uniformFromBits (m k : ℕ) (b : Fin k → Bool) : Option (Fin m) :=
  if h : bitsToNat b < m then some ⟨_, h⟩ else none

/-- `T` rejection trials of `k` bits each; the first accepted value. Uniform on `Fin m`
conditioned on `some`; `none` with probability `(1 - m/2^k)^T`. -/
def rejectionSample (m k T : ℕ) (b : Fin T → Fin k → Bool) : Option (Fin m) :=
  (List.finRange T).findSome? fun t => uniformFromBits m k (b t)

theorem rejectionSample_uniform_of_some (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) (i j : Fin m) :
    uprob (fun b : Fin T → Fin k → Bool => rejectionSample m k T b = some i) =
      uprob (fun b : Fin T → Fin k → Bool => rejectionSample m k T b = some j) := by
  sorry

theorem uprob_rejectionSample_none (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) :
    uprob (fun b : Fin T → Fin k → Bool => rejectionSample m k T b = none) =
      (1 - (m : ℝ) / 2 ^ k) ^ T := by
  sorry

/-- Fallback-to-default makes a total sampler within `(1 - m/2^k)^T` of uniform. -/
theorem statClose_rejectionSample (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) (d : Fin m) :
    StatClose (fun b : Fin T → Fin k → Bool => (rejectionSample m k T b).getD d) (id : Fin m → Fin m)
      ((1 - (m : ℝ) / 2 ^ k) ^ T) := by
  sorry

/-! ## Adversary bridges (TCSlib/Cryptography/Asymptotic/Adversary.lean) -/

def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool) :=
  if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none

def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i false

/-- `A(1^n, y)` as an inverter: output decoded as an `ℓ`-bit string, wrong length = failure. -/
def _root_.Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt n (List.ofFn y) r)

/-- The literal inverter `A(y)` of [PS10, Definition 26.1]: activation at parameter `|y| = m`. -/
def _root_.Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt m (List.ofFn y) r)

def _root_.Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  fun t r => decide (A.runAt n (List.ofFn t) r = [true])

def _root_.Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool :=
  fun w r => decide (A.runAt n w r = [true])

def _root_.Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  A.distinguisher n m

noncomputable def invProbOpt {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : ℝ :=
  uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1

theorem invProbOpt_le_invProb {α β ρ : Type*} [Fintype α] [Fintype ρ] [Inhabited α] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default) := by
  refine uprob_mono ?_
  rintro ⟨x, r⟩ ⟨x', hx', hf⟩
  simp [hx', hf]

theorem invProbOpt_some {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → α) :
    invProbOpt f (fun y r => some (A y r)) = invProb f A := by
  unfold invProbOpt invProb
  congr 1
  funext z
  simp

/-! ## One-way functions (TCSlib/Cryptography/Asymptotic/OneWay.lean) -/

/-- A family `f n : {0,1}^{inLen n} → {0,1}^{outLen n}` with explicit polynomial lengths. -/
structure FunFamily where
  inLen : PolyExpr
  outLen : PolyExpr
  f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)

namespace FunFamily

/-- Easy to compute: a polynomial-time string function computes `f n x` from `⟨1^n, x⟩`. -/
def Easy (𝓕 : FunFamily) : Prop :=
  ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
    ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)

noncomputable def invProbAt (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : ℝ :=
  invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n))

/-- [PS10, Definition 27.3]. -/
structure StrongOneWay (𝓕 : FunFamily) : Prop where
  easy : 𝓕.Easy
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n

/-- [PS10, Definition 28.4]; `0 < q n` is load-bearing (`1 - 1/0 = 1` would be vacuous). -/
structure WeakOneWay (𝓕 : FunFamily) : Prop where
  easy : 𝓕.Easy
  hard : ∃ q : PolyExpr, (∀ n, 0 < q.eval n) ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀,
    𝓕.invProbAt A n ≤ 1 - 1 / (q.eval n : ℝ)

/-- [PS10, Definition 26.1], literal: the adversary receives `f(x)` only. -/
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins (𝓕.outLen.eval n) =>
      ∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
        𝓕.f n x' = 𝓕.f n x) = 1

def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ := (f (List.replicate n false)).length

/-- The textbook `f : {0,1}* → {0,1}*` with the output length `p`: parameter = input length. -/
def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily where
  inLen := .var
  outLen := p
  f _ x i := (f (List.ofFn x)).getD i false

def LengthRegular (f : List Bool → List Bool) (p : PolyExpr) : Prop :=
  ∀ x, (f x).length = p.eval x.length

def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- The direct product `f'_n = (f_n)^{q n}` of [PS10, Theorem 35.1]. -/
def prod (𝓕 : FunFamily) (q : PolyExpr) : FunFamily where
  inLen := .mul q 𝓕.inLen
  outLen := .mul q 𝓕.outLen
  f n x := (blocks (q.eval n) (𝓕.outLen.eval n)).symm
    (TCSlib.Cryptography.OneWay.prodFun (𝓕.f n) (q.eval n) (blocks (q.eval n) (𝓕.inLen.eval n) x))

end FunFamily

/-- [PS10, Theorem 35.1]: the proof takes `q := 2 · var · q_w` (the text's `m = 2nq(n)`). -/
theorem weak_to_strong {𝓕 : FunFamily} (h : FunFamily.WeakOneWay 𝓕) :
    ∃ q : PolyExpr, FunFamily.StrongOneWay (𝓕.prod q) := by
  sorry

/-- [PS10, Theorem 35.2]. -/
theorem strong_prod_two {𝓕 : FunFamily} (h : FunFamily.StrongOneWay 𝓕) :
    FunFamily.StrongOneWay (𝓕.prod (.const 2)) := by
  sorry

/-- Sanity: strong implies weak. -/
theorem FunFamily.StrongOneWay.weak {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) : 𝓕.WeakOneWay := by
  sorry

/-- Sanity (non-vacuity of the adversary class): the identity is not one-way. -/
theorem not_strongOneWay_id : ¬ FunFamily.StrongOneWay (FunFamily.ofString id .var) := by
  sorry

/-- A family of permutations of `{0,1}^n` (the single one-way permutation of
[PS10, Theorems 79.4, 126.4]). -/
structure PermFamily where
  f : ∀ n, (Fin n → Bool) ≃ (Fin n → Bool)

def PermFamily.toFunFamily (P : PermFamily) : FunFamily where
  inLen := .var
  outLen := .var
  f n := P.f n

def OneWayPermutation (P : PermFamily) : Prop := P.toFunFamily.StrongOneWay

/-! ## Hard-core predicates, PRGs, next-bit test (Asymptotic/{HardCore,Pseudorandom}.lean) -/

/-- [PS10, Definition 78.3]. -/
def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) : Prop :=
  (∃ H : List Bool → List Bool, PolyTimeComputable H ∧
    ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1 / 2 + ε n

/-- [PS10, Definition 77.1]: a length-regular generator with explicit stretch. -/
structure PRG where
  stretch : PolyExpr
  G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
  expands : ∀ n, n < stretch.eval n

def PRG.Easy (P : PRG) : Prop :=
  ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
    ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)

/-! ## Ensembles (TCSlib/Cryptography/Asymptotic/Ensembles.lean) -/

/-- [PS10, Definition 69.3]: at each `n` a sampler from a finite seed type into `{0,1}^{ℓ n}`. -/
structure Ensemble (ℓ : PolyExpr) where
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  X : ∀ n, σ n → (Fin (ℓ.eval n) → Bool)

attribute [instance] Ensemble.fintype

namespace Ensemble

variable {ℓ : PolyExpr}

def uniform (ℓ : PolyExpr) : Ensemble ℓ where
  σ n := Fin (ℓ.eval n) → Bool
  X _ := id

/-- Efficiently samplable (distribution level): a polynomial-time sampler from `s n` uniform
bits whose output law is exactly `X n`. -/
def Samplable (X : Ensemble ℓ) : Prop :=
  ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧
    ∀ n, StatClose (fun r : Fin (s.eval n) → Bool => padFin (ℓ.eval n) (S (NUPPT.advInput n (List.ofFn r))))
      (X.X n) 0

/-- [PS10, Definition 69.4] with the distinguisher given `1^n` (headline form). -/
def Indist (X Y : Ensemble ℓ) : Prop :=
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n))

/-- [PS10, Definition 69.4] literal: the distinguisher receives `t` only (activation at
parameter `|t| = ℓ n`). -/
def IndistLit (X Y : Ensemble ℓ) : Prop :=
  ∀ D : NUPPT, Negligible fun n =>
    distAdv (X.X n) (Y.X n) (D.distinguisher (ℓ.eval n) (ℓ.eval n))

def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)

def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ' where
  σ n := X.σ n × M.Coins n
  X n z := padFin (ℓ'.eval n) (M.runAt n (List.ofFn (X.X n z.1)) z.2)

def copies (t : PolyExpr) (X : Ensemble ℓ) : Ensemble (.mul t ℓ) where
  σ n := Fin (t.eval n) → X.σ n
  X n s := (FunFamily.blocks (t.eval n) (ℓ.eval n)).symm (TCSlib.Cryptography.copies (t.eval n) (X.X n) s)

end Ensemble

theorem Ensemble.Indist.toLit {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y) : X.IndistLit Y := by
  sorry

theorem Ensemble.IndistLit.toIndist {ℓ : PolyExpr} {X Y : Ensemble ℓ}
    (hℓ : Function.Injective ℓ.eval) (h : X.IndistLit Y) : X.Indist Y := by
  sorry

theorem Ensemble.Indist.refl {ℓ : PolyExpr} (X : Ensemble ℓ) : X.Indist X := by
  sorry

theorem Ensemble.Indist.symm {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y) : Y.Indist X := by
  sorry

/-- [PS10, Lemma 71.5]. -/
theorem Ensemble.Indist.push {ℓ ℓ' : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT) :
    (X.push M ℓ').Indist (Y.push M ℓ') := by
  sorry

/-- [PS10, Lemma 71.6], one parameter. -/
theorem hybrid_lemma {σ γ ρ : Type*} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m)
    (X : ℕ → σ → γ) (D : γ → ρ → Bool) :
    ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i + 1)) D := by
  obtain ⟨i, hi, h⟩ := exists_hybrid_gap (fun i => acceptProb (X i) D) hm
  exact ⟨i, hi, h⟩

theorem Ensemble.Indist.trans {ℓ : PolyExpr} {X Y Z : Ensemble ℓ} (h₁ : X.Indist Y) (h₂ : Y.Indist Z) :
    X.Indist Z := by
  sorry

/-- Polynomially many copies, with the samplability the multicopy reduction needs. -/
theorem Ensemble.Indist.copies {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y)
    (hX : X.Samplable) (hY : Y.Samplable) (t : PolyExpr) :
    (X.copies t).Indist (Y.copies t) := by
  sorry

def mixEnsemble {ℓ : PolyExpr} (X₀ X₁ : Ensemble ℓ) (n : ℕ) :
    Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ.eval n) → Bool) :=
  fun z => (z.1, if z.1 then X₁.X n z.2.2 else X₀.X n z.2.1)

/-- The identity behind [PS10, Lemma 73.8] (proved once, concrete). -/
theorem predict_eq {ℓ : ℕ} {σ₀ σ₁ ρ : Type*} [Fintype σ₀] [Fintype σ₁] [Fintype ρ]
    (X₀ : σ₀ → (Fin ℓ → Bool)) (X₁ : σ₁ → (Fin ℓ → Bool)) (D : (Fin ℓ → Bool) → ρ → Bool) :
    uprob (fun z : (Bool × (σ₀ × σ₁)) × ρ =>
        D (if z.1.1 then X₁ z.1.2.2 else X₀ z.1.2.1) z.2 = z.1.1) =
      1 / 2 + (acceptProb X₁ D - acceptProb X₀ D) / 2 := by
  sorry

/-- [PS10, Lemma 73.8]. -/
theorem prediction_lemma {ℓ : PolyExpr} (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ : ℕ → ℝ)
    (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv (X₀.X n) (X₁.X n) (D.distinguisher n (ℓ.eval n))) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1 / 2 + μ n / 2 <
      uprob fun z : (Bool × (X₀.σ n × X₁.σ n)) × A.Coins n =>
        A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1 := by
  sorry

def PRG.ensemble (P : PRG) : Ensemble P.stretch where
  σ n := Fin n → Bool
  X := P.G

/-- [PS10, Definition 77.1], clauses (1)+(3). -/
def PRG.Secure (P : PRG) : Prop := P.Easy ∧ P.ensemble.Pseudorandom

/-- The next-bit experiment at one parameter: predict bit `i` from the prefix of length `i`. -/
noncomputable def nextBitProb {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => A (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2 = X z.1 i

/-- [PS10, Definition 75.2] (`i` ranges over existing bits; `A` receives `1^n` and the prefix). -/
def Ensemble.NextBitUnpredictable {ℓ : PolyExpr} (X : Ensemble ℓ) : Prop :=
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1 / 2 + ε n

/-- [PS10, Theorem 75.4]. -/
theorem Ensemble.NextBitUnpredictable.pseudorandom {ℓ : PolyExpr} {X : Ensemble ℓ}
    (hℓ : ∀ n, 0 < ℓ.eval n) (h : X.NextBitUnpredictable) : X.Pseudorandom := by
  sorry

/-! ## Private-key encryption (Asymptotic/Encryption.lean, ZeroKnowledge/Encryption.lean) -/

/-- [PS10, Definition 24.7]: three PPTs; keys and ciphertexts are strings, messages `n` bits. -/
structure PrivateKeyScheme where
  gen : NUPPT
  enc : NUPPT
  dec : NUPPT
  gen_uniform : gen.Uniform
  enc_uniform : enc.Uniform
  dec_uniform : dec.Uniform
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n) (rd : dec.Coins n),
    decodeFin n (dec.runAt n (pairEncode (gen.runAt n [] rg)
      (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) re)) rd) = some m

namespace PrivateKeyScheme

/-- `{k ← Gen(1^n) : Enc_k(m)}`. -/
def encDist (S : PrivateKeyScheme) (n : ℕ) (m : Fin n → Bool) :
    S.gen.Coins n × S.enc.Coins n → List Bool :=
  fun r => S.enc.runAt n (pairEncode (S.gen.runAt n [] r.1) (List.ofFn m)) r.2

/-- [PS10, Definition 91.1]. -/
def SingleMessageSecure (S : PrivateKeyScheme) : Prop :=
  ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool),
    distAdv (S.encDist n m₀) (S.encDist n m₁) (D.distinguisherL n) ≤ ε n

def encodeList : List (List Bool) → List Bool
  | [] => []
  | m :: ms => pairEncode m (encodeList ms)

/-- `q n + 1` encryptions under one key with independent coins. -/
def multiEncDist (S : PrivateKeyScheme) (n : ℕ) (q : ℕ) (m : Fin (q + 1) → Fin n → Bool) :
    S.gen.Coins n × (Fin (q + 1) → S.enc.Coins n) → List Bool :=
  fun r => encodeList (List.ofFn fun i =>
    S.enc.runAt n (pairEncode (S.gen.runAt n [] r.1) (List.ofFn (m i))) (r.2 i))

/-- [PS10, Definition 93.1]. -/
def MultiMessageSecure (S : PrivateKeyScheme) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
      distAdv (S.multiEncDist n (q.eval n) m) (S.multiEncDist n (q.eval n) m') (D.distinguisherL n) ≤ ε n

/-- [PS10, Definition 111.1]: zero-knowledge encryption. -/
def ZeroKnowledge (S : PrivateKeyScheme) : Prop :=
  ∃ Sim : NUPPT, Sim.Uniform ∧ ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (m : Fin n → Bool),
      distAdv (S.encDist n m) (Sim.runAt n []) (D.distinguisherL n) ≤ ε n

end PrivateKeyScheme

/-- [PS10, Theorem 112.2]. -/
theorem PrivateKeyScheme.singleMessageSecure_iff_zeroKnowledge (S : PrivateKeyScheme) :
    S.SingleMessageSecure ↔ S.ZeroKnowledge := by
  sorry

/-! ## Public-key encryption (Asymptotic/PublicKey.lean) -/

/-- [PS10, Definition 102.1] (clause (4), the message enumerator, dropped: Deviation). -/
structure PublicKeyScheme where
  gen : NUPPT
  enc : NUPPT
  dec : List Bool → List Bool
  gen_uniform : gen.Uniform
  enc_uniform : enc.Uniform
  dec_poly : PolyTimeComputable dec
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin n (dec (pairEncode (pairSndD (gen.runAt n [] rg))
      (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m

namespace PublicKeyScheme

/-- `{(pk, sk) ← Gen(1^n) : (pk, Enc_pk(m))}`. -/
def pkEncDist (S : PublicKeyScheme) (n : ℕ) (m : Fin n → Bool) :
    S.gen.Coins n × S.enc.Coins n → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1))
    (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (List.ofFn m)) r.2)

/-- [PS10, Definition 102.2]. -/
def Secure (S : PublicKeyScheme) : Prop :=
  ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool),
    distAdv (S.pkEncDist n m₀) (S.pkEncDist n m₁) (D.distinguisherL n) ≤ ε n

end PublicKeyScheme

/-! ## Collections (Asymptotic/Collections.lean) -/

/-- [PS10, Definition 41.1]: a collection `{f_i : D_i → R_i}` with a string index generator
`Gen(1^n) = ⟨i, t⟩` (the trapdoor `t` is ignored by plain collections), a domain sampler and
an evaluator. -/
structure Collection where
  D : List Bool → Type
  [fintypeD : ∀ i, Fintype (D i)]
  [inhabitedD : ∀ i, Inhabited (D i)]
  encD : ∀ i, D i → List Bool
  decD : ∀ i, List Bool → Option (D i)
  decD_encD : ∀ i x, decD i (encD i x) = some x
  f : ∀ i, D i → List Bool
  gen : NUPPT
  gen_uniform : gen.Uniform
  sample : NUPPT
  sample_uniform : sample.Uniform
  eval : List Bool → List Bool
  eval_poly : PolyTimeComputable eval
  eval_spec : ∀ i x, eval (pairEncode i (encD i x)) = f i x

attribute [instance] Collection.fintypeD Collection.inhabitedD

namespace Collection

def index (F : Collection) (n : ℕ) (r : F.gen.Coins n) : List Bool := pairFstD (F.gen.runAt n [] r)
def trap (F : Collection) (n : ℕ) (r : F.gen.Coins n) : List Bool := pairSndD (F.gen.runAt n [] r)

/-- The sampler is within `δ n` of uniform on `D_i` (Deviation: dyadic samplers; Q3). -/
def SampleClose (F : Collection) (δ : ℕ → ℝ) : Prop :=
  ∀ n (r : F.gen.Coins n),
    StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.runAt n (F.index n r) s))
      (fun x : F.D (F.index n r) => some x) (δ n)

/-- `Pr[i ← Gen(1^n); x ← D_i; y ← f_i(x) : f_i(A(1^n, i, y)) = y]` (ideal uniform `x`). -/
noncomputable def invProbAt (F : Collection) (A : NUPPT) (n : ℕ) : ℝ :=
  uexp fun r : F.gen.Coins n =>
    uprob fun z : F.D (F.index n r) × A.Coins n =>
      ∃ x', F.decD (F.index n r)
          (A.runAt n (pairEncode (F.index n r) (F.f (F.index n r) z.1)) z.2) = some x' ∧
        F.f (F.index n r) x' = F.f (F.index n r) z.1

structure OneWay (F : Collection) : Prop where
  sampleClose : ∃ δ : ℕ → ℝ, Negligible δ ∧ F.SampleClose δ
  hard : ∀ A : NUPPT, Negligible fun n => F.invProbAt A n

/-- Hard-core predicate for a collection (unnumbered, needed by 84.1/104.4/126.4). -/
def HardCore (F : Collection) (h : ∀ i, F.D i → Bool) : Prop :=
  (∃ H : List Bool → List Bool, PolyTimeComputable H ∧ ∀ i x, H (pairEncode i (F.encD i x)) = [h i x]) ∧
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    uexp (fun r : F.gen.Coins n =>
      uprob fun z : F.D (F.index n r) × A.Coins n =>
        A.distinguisherL n (pairEncode (F.index n r) (F.f (F.index n r) z.1)) z.2 = h (F.index n r) z.1)
      ≤ 1 / 2 + ε n

end Collection

/-- [PS10, Definition 55.1]. -/
structure PermCollection extends Collection where
  perm : ∀ i, D i ≃ D i
  f_perm : ∀ i x, f i x = encD i (perm i x)

/-- [PS10, Definition 56.1]: the trapdoor inverter. -/
structure TrapdoorCollection extends PermCollection where
  inv : NUPPT
  inv_uniform : inv.Uniform
  inv_spec : ∀ n (r : gen.Coins n) (y : D (pairFstD (gen.runAt n [] r))) (s : inv.Coins n),
    decD _ (inv.runAt n (pairEncode (pairSndD (gen.runAt n [] r)) (encD _ y)) s) = some ((perm _).symm y)

/-- [PS10, Theorem 42.2] (⇒ direction, the exercise): a collection gives a strong OWF. -/
theorem Collection.OneWay.exists_strongOneWay {F : Collection} (h : F.OneWay) :
    ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay := by
  sorry

/-! ## Oracle indistinguishability and PRFs (Asymptotic/PRF.lean) -/

structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)

attribute [instance] OracleEnsemble.fintype

def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂ where
  σ n := (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
  O _ := randomFunction _ _

def OracleEnsemble.keyed {ℓ₁ ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) :
    OracleEnsemble ℓ₁ ℓ₂ where
  σ n := Fin n → Bool
  O n := F n

inductive OracleMove (ℓ₁ : ℕ)
  | query (x : Fin ℓ₁ → Bool)
  | ret (b : Bool)

def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁ :=
  match pairDecode w, w with
  | some ([false], x), _ => match decodeFin ℓ₁ x with
    | some x => .query x
    | none => .ret false
  | _, [true, b] => .ret b
  | _, _ => .ret false

def encodeHist {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool :=
  h.foldr (fun p acc => pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) acc) []

def buildTree {ℓ₁ ℓ₂ : ℕ} (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ℕ → List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
  | 0, hist => match next hist with
    | .ret b => .ret b
    | .query _ => .ret false
  | q + 1, hist => match next hist with
    | .ret b => .ret b
    | .query x => .query x (fun o => buildTree next q (hist ++ [(x, o)]))

/-- The query tree of the next-query machine `D` at parameter `n` with budget `q`
([PS10, Definition 96.1]; D7: no oracle tapes, one activation per query on the history). -/
def _root_.Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) :=
  fun r => buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []

theorem _root_.Complexity.NUPPT.toOracleAdversary_boundedBy (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q := by
  sorry

/-- [PS10, Definition 96.1]: every next-query NUPPT with every polynomial query budget. -/
def OracleEnsemble.Indist {ℓ₁ ℓ₂ : PolyExpr} (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n =>
    distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))

theorem OracleEnsemble.Indist.refl {ℓ₁ ℓ₂ : PolyExpr} (O : OracleEnsemble ℓ₁ ℓ₂) : O.Indist O := by
  sorry

/-- [PS10, Definition 96.2]. -/
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)

theorem prfAdv_toOracleAdversary (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (D : NUPPT) (n q : ℕ) :
    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).O n) ((OracleEnsemble.random .var .var).O n)
        (oracleDist (D.toOracleAdversary n n n q)) =
      prfAdv (F n) (D.toOracleAdversary n n n q) := rfl

/-! ## Chapter 4: strategies, protocols, executions, views (ZeroKnowledge/Interaction.lean) -/

/-- A next-message strategy [PS10, §4.4]: `(x, z, r, received) ↦ next message`; on the
complete history the value is the party's output. The random tape has explicit polynomial
length `coins.eval |x|`. -/
structure Strategy where
  next : List Bool → List Bool → List Bool → List (List Bool) → List Bool
  coins : PolyExpr

namespace Strategy

def coinLen (S : Strategy) (n : ℕ) : ℕ := S.coins.eval n
abbrev Coins (S : Strategy) (n : ℕ) : Type := Fin (S.coinLen n) → Bool

def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []

/-- One activation of a machine at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the whole
random tape. -/
def ofNUPPT (A : NUPPT) : Strategy where
  next x z r hist := A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r
  coins := A.coins

/-- PPT strategy (time complexity of an ITM, [PS10, §4.4]; Deviation: per-activation time
polynomial in the total input length). -/
def Efficient (S : Strategy) : Prop :=
  ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧
    ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist

end Strategy

/-- Which party moves at move `k` (0-indexed). -/
def moverIsV (vFirst : Bool) (k : ℕ) : Bool :=
  if vFirst then decide (k % 2 = 0) else decide (k % 2 = 1)

/-- Messages received by `(P, V)` after `k` moves. -/
def exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) :
    ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 =>
    let e := exec P V vFirst x zP zV rP rV k
    if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2)
    else (e.1, e.2 ++ [P.next x zP rP e.1])

structure View where
  x : List Bool
  z : List Bool
  r : List Bool
  received : List (List Bool)

def View.encode (v : View) : List Bool :=
  pairEncode (pairEncode v.x v.z) (pairEncode v.r (Strategy.encodeMsgs v.received))

/-- A protocol: two strategies, the number of messages exchanged (explicit polynomial) and
the first mover. The verifier's verdict is its next-message function on the complete history. -/
structure Protocol where
  P : Strategy
  V : Strategy
  rounds : PolyExpr
  verifierFirst : Bool

namespace Protocol

abbrev ExecCoins (π : Protocol) (P' : Strategy) (x : List Bool) : Type :=
  P'.Coins x.length × π.V.Coins x.length

def withV (π : Protocol) (V' : Strategy) : Protocol := { π with V := V' }

/-- The transcript (messages received by `P'`, by `V`) of `P'_{r₁}(x, y) ↔ V_{r₂}(x, z)`. -/
def transcriptWith (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) :
    List (List Bool) × List (List Bool) :=
  exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)

def outV (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) : List Bool :=
  π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2

def outP (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : List Bool :=
  π.P.next x y (List.ofFn r.1) (π.transcriptWith π.P x y z r).1

def viewV (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
  ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩

def viewP (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
  ⟨x, y, List.ofFn r.1, (π.transcriptWith π.P x y z r).1⟩

end Protocol

/-- [PS10, Definition 116.1], literal `out_V = 0` as `[false]`. -/
structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
  efficientV : π.V.Efficient
  complete : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  sound : ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - ε x.length < uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])

/-- Soundness error `s` (constant-error proofs, [PS10, §4.5]). -/
structure InteractiveProofErr (π : Protocol) (L : Language Bool) (s : ℕ → ℝ) : Prop where
  efficientV : π.V.Efficient
  complete : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  sound : ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - s x.length ≤ uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])

/-- A witness relation [PS10, Appendix B]. -/
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  bounded : ∃ p : PolyExpr, ∀ x y, R x y → y.length ≤ p.eval x.length
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧
    ∀ x y, T (pairEncode x y) = true ↔ R x y

/-- [PS10, Definition 119.5]. -/
structure EfficientProverProof (π : Protocol) (L : Language Bool)
    (R : List Bool → List Bool → Prop) : Prop extends InteractiveProof π L where
  efficientP : π.P.Efficient
  completeWitness : ∀ x y, R x y → ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1

structure EfficientProverProofErr (π : Protocol) (L : Language Bool)
    (R : List Bool → List Bool → Prop) (s : ℕ → ℝ) : Prop extends InteractiveProofErr π L s where
  efficientP : π.P.Efficient
  completeWitness : ∀ x y, R x y → ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1

/-- The simulator's output on `(x, z)` (a word read as an encoded view). -/
def _root_.Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) : List Bool :=
  S.runAt x.length (pairEncode x z) r

/-- [PS10, Definition 121.1], strict PPT simulator; auxiliary inputs bounded by an arbitrary
polynomial `Lz` (Deviation, see docstring). -/
def HVZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length

/-- [PS10, Definition 121.2], strict PPT simulator. -/
def ZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧
    ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
        distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z)
          (D.distinguisherL x.length) ≤ ε x.length

/-- Statistical zero-knowledge with error `δ |x|` (all auxiliary inputs; all test sets). -/
def StatZK (π : Protocol) (R : List Bool → List Bool → Prop) (δ : ℕ → ℝ) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)

def PerfectZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop := StatZK π R (fun _ => 0)

/-- Perfect zero-knowledge with abort [Goldreich, Def. 4.3.1]: the strict-PPT simulator may
output `⊥ = []` with probability `≤ 1/2`; conditioned on not aborting its output has exactly
the law of the view. -/
def PerfectZKAbort (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1 / 2 ∧
    ∀ T : List Bool → Prop,
      uprob (fun r : (π.withV V').ExecCoins π.P x => T ((π.withV V').viewV x y z r).encode) *
          uprob (fun r : S.Coins x.length => S.simulate x z r ≠ []) =
        uprob (fun r : S.Coins x.length => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))

theorem StatZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R := by
  sorry

theorem StatZK.hvzk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R := by
  sorry

/-- [PS10, Definition 126.3] with the binding clause repaired (`v₀ ≠ v₁`). -/
structure Commitment (Com : List Bool → List Bool) (ℓ : PolyExpr) : Prop where
  easy : PolyTimeComputable Com
  binding : ∀ n (v₀ v₁ r₀ r₁ : List Bool), v₀.length = n → v₁.length = n →
    r₀.length = ℓ.eval n → r₁.length = ℓ.eval n → v₀ ≠ v₁ →
    Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  hides : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
      (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r)))
      (D.distinguisherL n) ≤ ε n

/-! ## Graph isomorphism (ZeroKnowledge/GraphIsomorphism.lean): expressibility check -/

abbrev Graph (n : ℕ) := Fin n → Fin n → Bool

def permGraph {n : ℕ} (G : Graph n) (π : Equiv.Perm (Fin n)) : Graph n :=
  fun u v => G (π.symm u) (π.symm v)

def encGraph {n : ℕ} (G : Graph n) : List Bool :=
  List.ofFn fun k : Fin (n * n) => G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

def decGraph (w : List Bool) : Σ n, Graph n :=
  ⟨Nat.sqrt w.length, fun u v => w.getD (finProdFinEquiv (u, v)) false⟩

def encPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : List Bool :=
  List.ofFn fun k : Fin (n * n) =>
    decide (π (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm k).2)

noncomputable def decPerm (n : ℕ) (w : List Bool) : Equiv.Perm (Fin n) := by
  classical
  exact if h : Function.Bijective (fun i : Fin n =>
      (Fin.find (fun j : Fin n => w.getD (finProdFinEquiv (i, j)) false = true)).getD i)
    then Equiv.ofBijective _ h else 1

/-- Fisher–Yates from offsets: `c i` is reduced modulo the number of remaining positions. -/
def fisherYates (n : ℕ) (c : Fin n → ℕ) : Equiv.Perm (Fin n) :=
  (List.finRange n).foldr
    (fun i σ => Equiv.swap i ⟨(i + c i % (n - i)) % n,
      Nat.mod_lt _ (Nat.pos_of_ne_zero (by have := i.isLt; omega))⟩ * σ) 1

/-- A permutation from `n` rejection samplers (`T` trials of `k` bits for position `i`,
range `n - i`); uniform conditioned on `some`. -/
def permFromCoins (n k T : ℕ) (b : Fin n → Fin T → Fin k → Bool) : Option (Equiv.Perm (Fin n)) :=
  if h : ∀ i : Fin n, (rejectionSample (n - i) k T (b i)).isSome then
    some (fisherYates n fun i => ((rejectionSample (n - i) k T (b i)).get (h i)).val)
  else none

theorem permFromCoins_uniform_of_some (n k T : ℕ) (hk : n ≤ 2 ^ k) (π π' : Equiv.Perm (Fin n)) :
    uprob (fun b : Fin n → Fin T → Fin k → Bool => permFromCoins n k T b = some π) =
      uprob (fun b : Fin n → Fin T → Fin k → Bool => permFromCoins n k T b = some π') := by
  sorry

theorem uprob_permFromCoins_none_le (n k T : ℕ) (hk : n ≤ 2 ^ k) :
    uprob (fun b : Fin n → Fin T → Fin k → Bool => permFromCoins n k T b = none) ≤
      n * (1 / 2 : ℝ) ^ T := by
  sorry

/-- Coin table `n × T × k` read from a coin string. -/
def coinTable (n T k : ℕ) (r : List Bool) : Fin n → Fin T → Fin k → Bool :=
  fun i t j => r.getD (((i * T) + t) * k + j) false

/-- The GI prover [PS10, Protocol 120.6]: `π` by rejection sampling (`n` trials of `n` bits
per position, identity on failure). -/
noncomputable def giProver : Strategy where
  coins := .normal 1 2
  next x y r hist :=
    let n := (decGraph (pairFstD x)).1
    let G₀ : Graph n := (decGraph (pairFstD x)).2
    let σ := decPerm n y
    let π := (permFromCoins n n n (coinTable n n n r)).getD 1
    match hist with
    | [] => encGraph (permGraph G₀ π)
    | _ :: _ => encPerm (if (hist.headD []).headD false then π * σ⁻¹ else π)

/-- The GI verifier: sends the coin bit `b`, then outputs `[decide (γ(G_b) = H)]`. -/
noncomputable def giVerifier : Strategy where
  coins := .const 1
  next x _ r hist :=
    let n := (decGraph (pairFstD x)).1
    let G₀ : Graph n := (decGraph (pairFstD x)).2
    let G₁ : Graph n := fun u v => (pairSndD x).getD (finProdFinEquiv (u, v)) false
    let b := r.headD false
    match hist with
    | [H, γ] => [decide (encGraph (permGraph (if b then G₁ else G₀) (decPerm n γ)) = H)]
    | [_] => [b]
    | _ => [false]

/-- One iteration of [PS10, Protocol 120.6]: three messages, prover first. -/
noncomputable def giProtocol : Protocol where
  P := giProver
  V := giVerifier
  rounds := .const 3
  verifierFirst := false

def Liso : Language Bool :=
  {x | ∃ (n : ℕ) (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)),
    x = pairEncode (encGraph G₀) (encGraph G₁) ∧ permGraph G₀ σ = G₁}

def Riso (x y : List Bool) : Prop :=
  ∃ (n : ℕ) (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)),
    x = pairEncode (encGraph G₀) (encGraph G₁) ∧ y = encPerm σ ∧ permGraph G₀ σ = G₁

theorem Riso_witnessRelation : WitnessRelation Liso Riso := by
  sorry

/-- [PS10, Lemma 123.5], first half (exact, uniform permutation). -/
theorem gi_sim_H_dist {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (hσ : permGraph G₀ σ = G₁)
    (p : Graph n → Prop) :
    uprob (fun z : Equiv.Perm (Fin n) × Bool => p (permGraph (cond z.2 G₁ G₀) z.1)) =
      uprob (fun π : Equiv.Perm (Fin n) => p (permGraph G₀ π)) := by
  sorry

/-- [PS10, Lemma 123.5], second half. -/
theorem gi_sim_half {n : ℕ} {ρ : Type*} [Fintype ρ] (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n))
    (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool) :
    uprob (fun z : (Equiv.Perm (Fin n) × Bool) × ρ =>
      V (permGraph (cond z.1.2 G₁ G₀) z.1.1) z.2 = z.1.2) = 1 / 2 := by
  sorry

/-- [PS10, Proposition 120.7], one iteration: soundness error `1/2`, efficient prover. -/
theorem gi_efficientProverProofErr : EfficientProverProofErr giProtocol Liso Riso (fun _ => 1 / 2) := by
  sorry

/-- [PS10, Theorem 122.3], one iteration, statistical form (D8). -/
theorem gi_statZK : ∃ δ : ℕ → ℝ, Negligible δ ∧ StatZK giProtocol Riso δ := by
  sorry

/-- Sanity: the trivial one-message NP protocol (`P` sends `y`) is an interactive proof. -/
def npProtocol (T : List Bool → Bool) : Protocol where
  P := ⟨fun _ y _ _ => y, .const 0⟩
  V := ⟨fun x _ _ hist => [T (pairEncode x (hist.headD []))], .const 0⟩
  rounds := .const 1
  verifierFirst := false

theorem npProtocol_interactiveProof {L : Language Bool} {R : List Bool → List Bool → Prop}
    (hR : WitnessRelation L R) (T : List Bool → Bool) (hT : PolyTimeComputable fun z => [T z])
    (hTR : ∀ x y, T (pairEncode x y) = true ↔ R x y) :
    EfficientProverProof (npProtocol T) L R := by
  sorry

end TCSlib.Cryptography

#check @Complexity.NUPPT.runAt
#check @Complexity.NUPPT.ofPolyTime
#check @Complexity.polyTimeComputable_iterateFind
#check @TCSlib.Cryptography.FunFamily.StrongOneWay
#check @TCSlib.Cryptography.weak_to_strong
#check @TCSlib.Cryptography.Ensemble.Indist
#check @TCSlib.Cryptography.Ensemble.Indist.copies
#check @TCSlib.Cryptography.OracleEnsemble.Indist
#check @TCSlib.Cryptography.PRF
#check @TCSlib.Cryptography.ZK
#check @TCSlib.Cryptography.Commitment
#check @TCSlib.Cryptography.giProtocol
#check @TCSlib.Cryptography.Collection.OneWay
#check @TCSlib.Cryptography.OneWay.yao_amplification_exp
