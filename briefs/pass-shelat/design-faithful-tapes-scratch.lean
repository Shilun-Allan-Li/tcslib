import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.ClassNP
import TCSlib.Complexity.CircuitComplexity.Advice
import TCSlib.Cryptography.Foundations
import TCSlib.Cryptography.OneWayFunctions
import TCSlib.Cryptography.Pseudorandom
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps

set_option autoImplicit false

open Turing TCSlib.Cryptography

namespace Complexity.Randomized

structure Poly where
  C : ℕ
  c : ℕ

def Poly.eval (p : Poly) (n : ℕ) : ℕ := p.C * (n + 1) ^ p.c

theorem Poly.eval_pos (p : Poly) (hC : 0 < p.C) (n : ℕ) : 0 < p.eval n := by
  unfold Poly.eval; positivity

theorem Poly.eval_mono (p : Poly) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-! ### (a) Probabilistic machines with a random tape -/

def _root_.Turing.FinTM.runCoins (M : FinTM Bool) (x r : List Bool) (t : ℕ) :
    Cfg M.k Bool M.State x :=
  M.tm.runFrom (Cfg.ofWords M.tm.q₀ (stateWord M.k r)) t

structure PPT where
  M : FinTM Bool
  T : Poly
  halts : ∀ (x : List Bool) (r : Fin (T.eval x.length) → Bool),
    (M.runCoins x (List.ofFn r) (T.eval x.length)).state = none

abbrev PPT.Coins (A : PPT) (n : ℕ) : Type := Fin (A.T.eval n) → Bool

def PPT.runWith (A : PPT) (x r : List Bool) : List Bool :=
  (A.M.runCoins x r (A.T.eval x.length)).output

/-- Sampler at coin budget `N ≥ |x|`: coins beyond `T |x|` are never read. -/
def PPT.sampleAt (A : PPT) (N : ℕ) (x : List Bool) (r : A.Coins N) : List Bool :=
  A.runWith x (List.ofFn r)

def PPT.sample (A : PPT) (x : List Bool) (r : A.Coins x.length) : List Bool :=
  A.sampleAt x.length x r

def PPT.Computes (A : PPT) (f : List Bool → List Bool) : Prop :=
  ∀ x, uprob (fun r : A.Coins x.length => A.sample x r = f x) = 1

structure NUPPT where
  M : FinTM Bool
  T : Poly
  a : Poly
  advice : ℕ → List Bool
  advice_len : ∀ n, (advice n).length ≤ a.eval n
  halts : ∀ (x : List Bool) (r : Fin (T.eval x.length) → Bool),
    (M.runCoins (pairEncode x (advice x.length)) (List.ofFn r) (T.eval x.length)).state = none

abbrev NUPPT.Coins (A : NUPPT) (n : ℕ) : Type := Fin (A.T.eval n) → Bool

def NUPPT.runWith (A : NUPPT) (x r : List Bool) : List Bool :=
  (A.M.runCoins (pairEncode x (A.advice x.length)) r (A.T.eval x.length)).output

def NUPPT.sampleAt (A : NUPPT) (N : ℕ) (x : List Bool) (r : A.Coins N) : List Bool :=
  A.runWith x (List.ofFn r)

structure NUPPTSeq where
  mach : ℕ → CodeTM
  d : Poly
  size : ∀ n, (mach n).serialize.length < d.eval n
  halts : ∀ (x : List Bool) (r : Fin (d.eval x.length) → Bool),
    ((mach x.length).toFinTM.runCoins x (List.ofFn r) (d.eval x.length)).state = none

abbrev NUPPTSeq.Coins (A : NUPPTSeq) (n : ℕ) : Type := Fin (A.d.eval n) → Bool

def NUPPTSeq.runWith (A : NUPPTSeq) (x r : List Bool) : List Bool :=
  ((A.mach x.length).toFinTM.runCoins x r (A.d.eval x.length)).output

/-- Behavioural equivalence of two sampler families: same output for every input and every
sufficiently long coin tape. -/
def SameBehaviour (f g : List Bool → List Bool → List Bool) (ℓ : ℕ → ℕ) : Prop :=
  ∀ x r, ℓ x.length ≤ r.length → f x r = g x r

/-- The two formulations of [PS10, Definition 26.8] are equivalent (statement shape). -/
theorem nuppt_seq_iff_advice_shape :
    (∀ A : NUPPTSeq, ∃ B : NUPPT, SameBehaviour A.runWith B.runWith
        (fun n => max (A.d.eval n) (B.T.eval n))) ∧
    (∀ B : NUPPT, ∃ A : NUPPTSeq, SameBehaviour A.runWith B.runWith
        (fun n => max (A.d.eval n) (B.T.eval n))) := by
  sorry

/-- The D3 (coins-in-the-input) face: a deterministic polynomial-time machine on
`pairEncode x r`. Bridge (i)/(ii) of the design. -/
def PairForm (A : NUPPT) (f : List Bool → List Bool) : Prop :=
  PolyTimeComputable f ∧ ∀ x (r : A.Coins x.length),
    f (pairEncode x (List.ofFn r)) = A.sampleAt x.length x r

theorem exists_pairForm_shape (A : NUPPT) : ∃ f, PairForm A f := by sorry

def decodeBits (n : ℕ) (w : List Bool) : Option (Fin n → Bool) :=
  if w.length = n then some (fun i => w.getD i false) else none

def ones (n : ℕ) : List Bool := List.replicate n true

/-! ### (b) One-way functions -/

structure FunFamily where
  ℓ : Poly
  m : Poly
  f : ∀ n, (Fin (ℓ.eval n) → Bool) → Fin (m.eval n) → Bool

def FunFamily.str (F : FunFamily) (w : List Bool) : List Bool :=
  List.ofFn (F.f w.length (fun i => w.getD i false))

def FunFamily.advIn (F : FunFamily) (n : ℕ) : ℕ := 2 * n + 2 + F.m.eval n

noncomputable def invSucc (F : FunFamily) (A : NUPPT) (n : ℕ) : ℝ :=
  uprob fun z : (Fin (F.ℓ.eval n) → Bool) × A.Coins (F.advIn n) =>
    ∃ x', decodeBits (F.ℓ.eval n)
      (A.sampleAt (F.advIn n) (pairEncode (ones n) (List.ofFn (F.f n z.1))) z.2) = some x' ∧
      F.f n x' = F.f n z.1

def StrongOneWay (F : FunFamily) : Prop :=
  PolyTimeComputable F.str ∧ ∀ A : NUPPT, Negligible (invSucc F A)

def WeakOneWay (F : FunFamily) : Prop :=
  PolyTimeComputable F.str ∧ ∃ q : Poly, 0 < q.C ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀,
    invSucc F A n ≤ 1 - 1 / (q.eval n : ℝ)

def WorstCaseOneWay (F : FunFamily) : Prop :=
  PolyTimeComputable F.str ∧ ¬ ∃ A : NUPPT, ∀ n (x : Fin (F.ℓ.eval n) → Bool),
    uprob (fun r : A.Coins (F.advIn n) =>
      ∃ x', decodeBits (F.ℓ.eval n)
        (A.sampleAt (F.advIn n) (pairEncode (ones n) (List.ofFn (F.f n x))) r) = some x' ∧
        F.f n x' = F.f n x) = 1

/-- The direct product `f'(x₁, …, x_{m n}) = (f x₁, …, f x_{m n})` at parameter `n`,
flattened to bit strings [PS10, Theorem 35.1]. -/
def FunFamily.prod (F : FunFamily) (m : Poly) : FunFamily where
  ℓ := ⟨F.ℓ.C * m.C, F.ℓ.c + m.c⟩
  m := ⟨F.m.C * m.C, F.m.c + m.c⟩
  f := fun n x => by
    -- `Fin (ℓ.C m.C (n+1)^(ℓ.c + m.c)) ≃ Fin (m n) × Fin (ℓ n)`: `finProdFinEquiv` after `pow_add`
    exact fun i => sorry

theorem weak_to_strong_shape (F : FunFamily) (hF : WeakOneWay F) :
    ∃ m : Poly, StrongOneWay (F.prod m) := by sorry

/-! ### (c) Ensembles -/

structure Ensemble where
  s : Poly
  len : Poly
  X : ∀ n, (Fin (s.eval n) → Bool) → List Bool
  len_le : ∀ n r, (X n r).length ≤ len.eval n

def NUPPT.dist (D : NUPPT) (N : ℕ) : List Bool → D.Coins N → Bool :=
  fun t r => decide (D.sampleAt N t r = [true])

def CompIndist (X Y : Ensemble) : Prop :=
  ∀ D : NUPPT, Negligible fun n =>
    distAdv (X.X n) (Y.X n) (D.dist (max (X.len.eval n) (Y.len.eval n)))

/-- Seed budget of the mapped ensemble dominates seeds of `X` plus coins of `M`. -/
theorem mapSeed_le (X : Ensemble) (M : NUPPT) (n : ℕ) :
    X.s.eval n + M.T.eval (X.len.eval n) ≤
      (⟨X.s.C + M.T.C * (X.len.C + 1) ^ M.T.c, X.s.c + X.len.c * M.T.c⟩ : Poly).eval n := by
  sorry

/-- `M(X_n)`: post-processing an ensemble by a non-uniform PPT [PS10, Lemma 71.5]. -/
def Ensemble.map (X : Ensemble) (M : NUPPT) : Ensemble where
  s := ⟨X.s.C + M.T.C * (X.len.C + 1) ^ M.T.c, X.s.c + X.len.c * M.T.c⟩
  len := ⟨M.T.C * (X.len.C + 1) ^ M.T.c, X.len.c * M.T.c⟩
  X := fun n r =>
    let r' : Fin (X.s.eval n + M.T.eval (X.len.eval n)) → Bool :=
      fun i => r (Fin.castLE (mapSeed_le X M n) i)
    M.runWith (X.X n (fun i => r' (Fin.castAdd _ i)))
      (List.ofFn fun i : Fin (M.T.eval (X.len.eval n)) => r' (Fin.natAdd _ i))
  len_le := sorry

theorem closure_shape (X Y : Ensemble) (M : NUPPT) (h : CompIndist X Y) :
    CompIndist (X.map M) (Y.map M) := by sorry

/-- Hybrid lemma [PS10, Lemma 71.6] at one parameter, directly from `exists_hybrid_gap`. -/
theorem hybrid_shape {σ ρ γ : Type} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 1 < m)
    (X : Fin m → σ → γ) (D : γ → ρ → Bool) {ε : ℝ}
    (h : ε < distAdv (X ⟨0, by omega⟩) (X ⟨m - 1, by omega⟩) D) :
    ∃ i : ℕ, ∃ hi : i + 1 < m,
      ε / m < distAdv (X ⟨i, by omega⟩) (X ⟨i + 1, hi⟩) D := by sorry

/-- Prediction lemma [PS10, Lemma 73.8], concrete identity. -/
theorem prediction_shape {σ ρ γ : Type} [Fintype σ] [Fintype ρ] (X : Bool → σ → γ)
    (D : γ → ρ → Bool) :
    uprob (fun z : Bool × σ × ρ => D (X z.1 z.2.1) z.2.2 = z.1) =
      1 / 2 + (acceptProb (X true) D - acceptProb (X false) D) / 2 := by sorry

/-! ### (d) Oracle machines -/

structure FinOracleTM where
  k : ℕ
  State : Type
  [fintypeState : Fintype State]
  [decEqState : DecidableEq State]
  tm : OracleTM k Bool State
  wf : tm.WellFormed

attribute [instance] FinOracleTM.fintypeState FinOracleTM.decEqState

/-- Run with oracle `O`, coins on tape 0, query tape = last tape. -/
noncomputable def FinOracleTM.runCoins (M : FinOracleTM) (O : Language Bool) (x r : List Bool)
    (t : ℕ) : Cfg (M.k + 1) Bool M.State x :=
  M.tm.runFrom O (Cfg.ofWords M.tm.q₀ (stateWord (M.k + 1) r)) t

structure NUOraclePPT where
  M : FinOracleTM
  T : Poly
  a : Poly
  advice : ℕ → List Bool
  advice_len : ∀ n, (advice n).length ≤ a.eval n
  halts : ∀ (O : Language Bool) (x : List Bool) (r : Fin (T.eval x.length) → Bool),
    (M.runCoins O (pairEncode x (advice x.length)) (List.ofFn r) (T.eval x.length)).state = none

/-- A function oracle as a language: `⟨x, 1^i⟩ ∈ O_F ↔ F(x)_i = 1`. -/
def langOf {n : ℕ} (F : (Fin n → Bool) → Fin n → Bool) : Language Bool :=
  {w | ∃ (x : Fin n → Bool) (i : Fin n), w = pairEncode (List.ofFn x) (ones i) ∧ F x i = true}

abbrev NUOraclePPT.Coins (D : NUOraclePPT) (n : ℕ) : Type := Fin (D.T.eval n) → Bool

noncomputable def NUOraclePPT.oracleDist (D : NUOraclePPT) (n : ℕ) :
    ((Fin n → Bool) → Fin n → Bool) → D.Coins n → Bool :=
  fun F r => decide ((D.M.runCoins (langOf F) (pairEncode (ones n) (D.advice n))
    (List.ofFn r) (D.T.eval n)).output = [true])

def PRFFamily := ∀ n, (Fin n → Bool) → (Fin n → Bool) → Fin n → Bool

def IsPRF (F : PRFFamily) : Prop :=
  PolyTimeComputable (fun w => List.ofFn (F (Complexity.pairFstD w).length
      (fun i => (Complexity.pairFstD w).getD i false) (fun i => (Complexity.pairSndD w).getD i false))) ∧
  ∀ D : NUOraclePPT, Negligible fun n =>
    distAdv (F n) (randomFunction (Fin n → Bool) (Fin n → Bool)) (D.oracleDist n)

/-- The query tree of an oracle machine (existence shape). -/
theorem exists_queryTree_shape (D : NUOraclePPT) (n : ℕ) :
    ∃ A : OracleAdversary (D.Coins n) (Fin n → Bool) (Fin n → Bool),
      A.BoundedBy (D.T.eval n) ∧ ∀ F r, oracleDist A F r = D.oracleDist n F r := by sorry

/-! ### (e) Interaction -/

/-- Self-delimiting encoding of a list of strings: `⟨m₁, ⟨m₂, … ⟨m_k, []⟩⟩⟩`. -/
def encodeList : List (List Bool) → List Bool
  | [] => []
  | m :: ms => pairEncode m (encodeList ms)

structure Strategy where
  coins : ℕ → ℕ
  next : (x z : List Bool) → (Fin (coins x.length) → Bool) → List (List Bool) → List Bool

abbrev Strategy.Coins (S : Strategy) (x : List Bool) : Type := Fin (S.coins x.length) → Bool

/-- The strategy is computed by a PPT whose coin tape is the strategy's random tape. -/
def Strategy.IsPPT (S : Strategy) : Prop :=
  ∃ (A : PPT) (p : Poly), (∀ n, S.coins n = p.eval n) ∧
    ∀ x z (r : S.Coins x) hist,
      S.next x z r hist = A.runWith (pairEncode (pairEncode x z) (encodeList hist)) (List.ofFn r)

structure Protocol where
  A : Strategy
  B : Strategy
  rounds : Poly

/-- Messages received by `A` and by `B` after `k` alternating rounds, `A` speaking first. -/
def Protocol.exec (P : Protocol) (x z₁ z₂ : List Bool) (r₁ : P.A.Coins x) (r₂ : P.B.Coins x) :
    ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 =>
    let e := P.exec x z₁ z₂ r₁ r₂ k
    if k % 2 = 0 then (e.1, e.2 ++ [P.A.next x z₁ r₁ e.1])
    else (e.1 ++ [P.B.next x z₂ r₂ e.2], e.2)

def Protocol.viewB (P : Protocol) (x z₁ z₂ : List Bool) (r₁ : P.A.Coins x) (r₂ : P.B.Coins x) :
    List Bool × List Bool × List Bool × List (List Bool) :=
  (x, z₂, List.ofFn r₂, (P.exec x z₁ z₂ r₁ r₂ (2 * P.rounds.eval x.length)).2)

def Protocol.outB (P : Protocol) (x z₁ z₂ : List Bool) (r₁ : P.A.Coins x) (r₂ : P.B.Coins x) :
    List Bool :=
  P.B.next x z₂ r₂ (P.exec x z₁ z₂ r₁ r₂ (2 * P.rounds.eval x.length)).2

structure NPRelation where
  rel : List Bool → List Bool → Prop
  wlen : Poly
  inP : {w | ∃ x y, w = pairEncode x y ∧ rel x y} ∈ Complexity.P

def NPRelation.lang (R : NPRelation) : Language Bool :=
  {x | ∃ y, y.length ≤ R.wlen.eval x.length ∧ R.rel x y}

/-- [PS10, Definition 116.1]. -/
structure IsInteractiveProof (Pv V : Strategy) (rounds : Poly) (L : Language Bool) : Prop where
  V_ppt : V.IsPPT
  complete : ∀ x ∈ L, ∃ y : List Bool, ∀ z,
    uprob (fun r : (⟨Pv, V, rounds⟩ : Protocol).A.Coins x × V.Coins x =>
      (⟨Pv, V, rounds⟩ : Protocol).outB x y z r.1 r.2 = [true]) = 1
  sound : ∃ e : ℕ → ℝ, Negligible e ∧ ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - e x.length < uprob (fun r : P'.Coins x × V.Coins x =>
      (⟨P', V, rounds⟩ : Protocol).outB x [] z r.1 r.2 = [false])

/-- [PS10, Definition 119.5]. -/
structure HasEfficientProver (Pv V : Strategy) (rounds : Poly) (R : NPRelation) : Prop where
  ip : IsInteractiveProof Pv V rounds R.lang
  P_ppt : Pv.IsPPT
  complete_witness : ∀ x y, R.rel x y → ∀ z,
    uprob (fun r : Pv.Coins x × V.Coins x =>
      (⟨Pv, V, rounds⟩ : Protocol).outB x y z r.1 r.2 = [true]) = 1

def encodeView (v : List Bool × List Bool × List Bool × List (List Bool)) : List Bool := sorry

/-- [PS10, Definition 121.1], with a strict PPT simulator. -/
def HVZK (Pv V : Strategy) (rounds : Poly) (R : NPRelation) : Prop :=
  ∃ S : PPT, ∀ D : NUPPT, ∃ e : ℕ → ℝ, Negligible e ∧ ∀ x y z, R.rel x y →
    ∃ N, distAdv (fun r : Pv.Coins x × V.Coins x =>
          encodeView ((⟨Pv, V, rounds⟩ : Protocol).viewB x y z r.1 r.2))
        (fun r => S.sampleAt N (pairEncode x z) r) (D.dist N) ≤ e x.length

/-- [PS10, Definition 121.2], strict-PPT simulator. -/
def ZK (Pv V : Strategy) (rounds : Poly) (R : NPRelation) : Prop :=
  ∀ V' : Strategy, V'.IsPPT → ∃ S : PPT, ∀ D : NUPPT, ∃ e : ℕ → ℝ, Negligible e ∧
    ∀ x y z, R.rel x y → ∃ N,
      distAdv (fun r : Pv.Coins x × V'.Coins x =>
          encodeView ((⟨Pv, V', rounds⟩ : Protocol).viewB x y z r.1 r.2))
        (fun r => S.sampleAt N (pairEncode x z) r) (D.dist N) ≤ e x.length

/-- [PS10, Definition 126.3]. -/
structure Commitment where
  com : List Bool → List Bool → List Bool
  l : Poly
  poly : PolyTimeComputable (fun w => com (Complexity.pairFstD w) (Complexity.pairSndD w))

structure Commitment.Secure (C : Commitment) : Prop where
  binding : ∀ n (v₀ v₁ : Fin n → Bool) (r₀ r₁ : Fin (C.l.eval n) → Bool), v₀ ≠ v₁ →
    C.com (List.ofFn v₀) (List.ofFn r₀) ≠ C.com (List.ofFn v₁) (List.ofFn r₁)
  hide : ∀ D : NUPPT, ∃ e : ℕ → ℝ, Negligible e ∧ ∀ n (v₀ v₁ : Fin n → Bool), ∃ N,
    distAdv (fun r : Fin (C.l.eval n) → Bool => C.com (List.ofFn v₀) (List.ofFn r))
      (fun r : Fin (C.l.eval n) → Bool => C.com (List.ofFn v₁) (List.ofFn r)) (D.dist N) ≤ e n

/-- Graphs on `Fin n` with decidable adjacency, and isomorphism via permutations. -/
def graphIso {n : ℕ} (G₀ G₁ : SimpleGraph (Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), G₀.map σ.toEmbedding = G₁

#check @SimpleGraph.map
#check @Equiv.Perm
#check @TCSlib.Cryptography.uprob_bool_prod

end Complexity.Randomized
