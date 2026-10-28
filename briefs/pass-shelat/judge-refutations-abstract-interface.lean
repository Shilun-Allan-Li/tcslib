import TCSlib.Cryptography.Foundations
import TCSlib.Cryptography.Pseudorandom
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.CircuitComplexity.Advice
import TCSlib.Cryptography.HardcoreBit

set_option autoImplicit false

namespace TCSlib.Cryptography.Asymptotic

open Turing Complexity

/-! ### Explicit polynomial length expressions -/

/-- Syntactic polynomial expressions in one variable `n`, used for every length that
depends on the security parameter (coin, advice, message, output lengths, round and query
bounds). Explicit syntax, never an abstract `ℕ → ℕ`. -/
inductive PolyExpr : Type
  | const : ℕ → PolyExpr
  | var : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  deriving DecidableEq

namespace PolyExpr

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

theorem eval_normal (C c n : ℕ) : (normal C c).eval n = C * (n + 1) ^ c := rfl

theorem eval_subst (p q : PolyExpr) (n : ℕ) : (p.subst q).eval n = p.eval (q.eval n) := by
  induction p <;> simp_all [subst, eval]

end PolyExpr

/-! ### Randomized string functions -/

/-- A randomized string function with an explicit coin length: on input `x` and a coin
string `r` of length `coins.eval |x|` it outputs `run x r`. Members of an adversary class
are such objects; the run on coin strings of the wrong length is irrelevant. -/
structure RandFun where
  coins : PolyExpr
  run : List Bool → List Bool → List Bool

namespace RandFun

/-- Coin length at input length `n`. -/
def coinLen (A : RandFun) (n : ℕ) : ℕ := A.coins.eval n

/-- The sampler view at a fixed input: uniform coins in, output string out. -/
def sample (A : RandFun) (x : List Bool) : (Fin (A.coinLen x.length) → Bool) → List Bool :=
  fun r => A.run x (List.ofFn r)

/-- A deterministic string function as a member with no coins. -/
def ofFun (g : List Bool → List Bool) : RandFun := ⟨.const 0, fun x _ => g x⟩

/-- Pad or truncate to length `L`. -/
def padTo (L : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate L false).take L

/-- Sequential composition with fresh coins and input pass-through: on `x` with coins
`r = r₁ ‖ r₂`, run `A` on `x` with `r₁`, pad its answer to `q.eval |x|` bits, and run `B` on
`pairEncode x answer` with `r₂` (truncated to `B`'s coin length at that fixed input length). -/
def seq (A B : RandFun) (q : PolyExpr) : RandFun where
  coins := .add A.coins (B.coins.subst (.add (.mul (.const 2) .var) (.add (.const 2) q)))
  run x r :=
    let r₁ := r.take (A.coinLen x.length)
    let r₂ := r.drop (A.coinLen x.length)
    let y := pairEncode x (padTo (q.eval x.length) (A.run x r₁))
    B.run y (r₂.take (B.coinLen y.length))

/-- Polynomially many adaptive calls with fresh coins: the state starts as `pairEncode x []`;
each of the `R.eval |x|` rounds pads the query `pairSndD s` to `q.eval |x|` bits, calls `A`
on it with a fresh coin block, and lets the deterministic `step` update the state from
`pairEncode s answer`. The output is the final state. -/
def iter (A : RandFun) (step : List Bool → List Bool) (q R : PolyExpr) : RandFun where
  coins := .mul R (A.coins.subst q)
  run x r :=
    let L := q.eval x.length
    let ℓ := A.coinLen L
    (Nat.rec (motive := fun _ => List Bool × List Bool) (pairEncode x [], r)
      (fun _ st => (step (pairEncode st.1 (A.run (padTo L (pairSndD st.1)) (st.2.take ℓ))),
        st.2.drop ℓ)) (R.eval x.length)).1

/-- Tagged union: the first input bit selects which member runs on the rest. -/
def union (A B : RandFun) : RandFun where
  coins := .add A.coins B.coins
  run x r := match x with
    | [] => []
    | b :: x' => if b then A.run x' (r.take (A.coinLen x'.length))
        else B.run x' (r.take (B.coinLen x'.length))

/-- Hard-wiring an advice string `β n` of explicit length `a.eval n`: the member sees
`pairEncode x (β |x|)`. -/
def withAdvice (A : RandFun) (β : ℕ → List Bool) (a : PolyExpr) : RandFun where
  coins := A.coins.subst (.add (.mul (.const 2) .var) (.add (.const 2) a))
  run x r := A.run (pairEncode x (β x.length)) r

end RandFun

/-! ### The machine instance: PPT and non-uniform PPT -/

/-- [PS10, Definitions 23.4, 23.5]: `A` is a probabilistic polynomial-time machine when some
finite binary machine, run on `pairEncode x r`, halts within `Ct * (|input| + 1) ^ ct` steps
on **every** input (worst case over the random tape) and outputs `A.run x r` whenever `r`
has the declared coin length. -/
def PPT (A : RandFun) : Prop :=
  ∃ (g : List Bool → List Bool), PolyTimeComputable g ∧
    ∀ x r : List Bool, r.length = A.coinLen x.length → A.run x r = g (pairEncode x r)

/-- [PS10, Definition 26.8], advice formulation: a PPT that also receives an advice string
`α |x|` of explicit polynomial length. -/
def NUPPT (A : RandFun) : Prop :=
  ∃ (g : List Bool → List Bool) (α : ℕ → List Bool) (a : PolyExpr), PolyTimeComputable g ∧
    (∀ n, (α n).length = a.eval n) ∧
    ∀ x r : List Bool, r.length = A.coinLen x.length →
      A.run x r = g (pairEncode (pairEncode x (α x.length)) r)

/-! ### The abstract interface -/

/-- Closure properties of a class of efficient deterministic string functions, exactly the
`Complexity.PolyTimeComputable` closure lemmas the chapter 2-4 reductions use. -/
structure EffClass where
  Eff : (List Bool → List Bool) → Prop
  comp : ∀ {g h}, Eff g → Eff h → Eff (g ∘ h)
  id : Eff id
  const : ∀ w, Eff (fun _ => w)
  pair : ∀ {g h}, Eff g → Eff h → Eff (fun x => Turing.pairEncode (g x) (h x))
  fst : Eff pairFstD
  snd : Eff pairSndD
  ite : ∀ {p : List Bool → Bool} {g h}, Eff (fun x => [p x]) → Eff g → Eff h →
    Eff (fun x => if p x then g x else h x)
  append : ∀ {g h}, Eff g → Eff h → Eff (fun x => g x ++ h x)
  unary : ∀ p : PolyExpr, Eff (fun x => List.replicate (p.eval x.length) true)
  lenEq : Eff (fun z => [decide ((pairFstD z).length = (pairSndD z).length)])
  splitUnary : Eff (fun z => Turing.pairEncode ((pairSndD z).take (pairFstD z).length)
    ((pairSndD z).drop (pairFstD z).length))
  iterate : ∀ {step emit : List Bool → List Bool} (R : PolyExpr), Eff step → Eff emit →
    Eff (fun x => (List.range (R.eval x.length + 1)).flatMap fun i => emit (step^[i] x))

/-- An adversary class: a membership predicate on randomized string functions, closed under
the operations the proofs of [PS10, Chapters 2-4] perform on adversaries. -/
structure AdversaryClass extends EffClass where
  Mem : RandFun → Prop
  mem_ofFun : ∀ {g}, Eff g → Mem (RandFun.ofFun g)
  mem_seq : ∀ {A B} (q : PolyExpr), Mem A → Mem B → Mem (A.seq B q)
  mem_iter : ∀ {A step} (q R : PolyExpr), Mem A → Eff step → Mem (A.iter step q R)
  mem_union : ∀ {A B}, Mem A → Mem B → Mem (A.union B)

/-- The non-uniform mixin: advice strings of explicit polynomial length may be hard-wired. -/
structure AdversaryClass.HasAdvice (𝒞 : AdversaryClass) : Prop where
  mem_withAdvice : ∀ {A} (β : ℕ → List Bool) (a : PolyExpr), 𝒞.Mem A →
    (∀ n, (β n).length = a.eval n) → 𝒞.Mem (A.withAdvice β a)


/-! ### Bridges to the concrete layer -/

/-- Decode a string as an `n`-bit string (missing bits read `false`; extra bits ignored). -/
def decodeFin (n : ℕ) (l : List Bool) : Fin n → Bool := fun i => l.getD i false

/-- The adversary input `(1^n, y)` for an `m`-bit challenge `y`. -/
def challengeInput (n m : ℕ) (y : Fin m → Bool) : List Bool :=
  pairEncode (List.replicate n true) (List.ofFn y)

/-- Its length, a function of `n` and `m` only. -/
def challengeLen (n m : ℕ) : ℕ := 2 * n + 2 + m

theorem challengeInput_length (n m : ℕ) (y : Fin m → Bool) :
    (challengeInput n m y).length = challengeLen n m := by
  simp [challengeInput, challengeLen, pairEncode, List.length_flatMap, List.length_ofFn]
  omega

/-- A member as an inverter at parameter `n` of an `m`-bit challenge: decode its output as
an `N`-bit string. -/
def RandFun.inverter (A : RandFun) (n N m : ℕ) :
    (Fin m → Bool) → (Fin (A.coinLen (challengeLen n m)) → Bool) → (Fin N → Bool) :=
  fun y r => decodeFin N (A.run (challengeInput n m y) (List.ofFn r))

/-- A member as a Boolean distinguisher at parameter `n` of `m`-bit samples. -/
def RandFun.distinguisher (A : RandFun) (n m : ℕ) :
    (Fin m → Bool) → (Fin (A.coinLen (challengeLen n m)) → Bool) → Bool :=
  fun t r => (A.run (challengeInput n m t) (List.ofFn r)).headD false

/-! ### One-way functions [PS10, §2.2] -/

/-- A family of string functions indexed by the parameter `n`, with explicit input length
`N n` and output length `m n`; `F n` is evaluated on `N n`-bit strings. -/
structure Family where
  N : PolyExpr
  m : PolyExpr
  F : ℕ → List Bool → List Bool

namespace Family

/-- The concrete-layer view at parameter `n`. -/
def at_ (f : Family) (n : ℕ) : (Fin (f.N.eval n) → Bool) → (Fin (f.m.eval n) → Bool) :=
  fun x => decodeFin (f.m.eval n) (f.F n (List.ofFn x))

/-- The direct product of `q n` copies, [PS10, Theorem 35.1]. -/
def prod (f : Family) (q : PolyExpr) : Family where
  N := .mul f.N q
  m := .mul f.m q
  F n z := (List.range (q.eval n)).flatMap fun i =>
    f.F n ((z.drop (i * f.N.eval n)).take (f.N.eval n))

end Family

variable (𝒞 : AdversaryClass)

/-- [PS10, Definition 24.6]: `A` computes `g` with probability one. -/
def ComputesProb1 (A : RandFun) (g : List Bool → List Bool) : Prop :=
  ∀ x r, r.length = A.coinLen x.length → A.run x r = g x

/-- Easy to compute [PS10, Definition 26.1(1)]: some PPT computes `(1^n, x) ↦ F n x` with
probability one. -/
def EasyToCompute (f : Family) : Prop :=
  ∃ A : RandFun, PPT A ∧ ComputesProb1 A (fun z => f.F (pairFstD z).length (pairSndD z))

/-- [PS10, Definition 26.1]. -/
def WorstCaseOWF (f : Family) : Prop :=
  EasyToCompute f ∧ ¬ ∃ A, 𝒞.Mem A ∧ ∀ n (x : Fin (f.N.eval n) → Bool),
    uprob (fun r => f.at_ n (A.inverter n (f.N.eval n) (f.m.eval n) (f.at_ n x) r) =
      f.at_ n x) = 1

/-- [PS10, Definition 27.3]. -/
def StrongOWF (f : Family) : Prop :=
  EasyToCompute f ∧ ∀ A, 𝒞.Mem A →
    Negligible (fun n => invProb (f.at_ n) (A.inverter n (f.N.eval n) (f.m.eval n)))

/-- [PS10, Definition 28.4]: the polynomial `q` is uniform over all adversaries. -/
def WeakOWF (f : Family) : Prop :=
  EasyToCompute f ∧ ∃ q : PolyExpr, ∀ A, 𝒞.Mem A → ∃ n₀, ∀ n ≥ n₀,
    invProb (f.at_ n) (A.inverter n (f.N.eval n) (f.m.eval n)) ≤ 1 - 1 / (q.eval n : ℝ)

/-- [PS10, Theorem 35.1] (statement). -/
theorem weak_to_strong (f : Family) (hf : WeakOWF 𝒞 f) :
    ∃ q : PolyExpr, StrongOWF 𝒞 (f.prod q) := by
  sorry

/-! ### Ensembles and indistinguishability [PS10, §3.1] -/

/-- [PS10, Definition 69.3], D6: a family of samplers from explicit-length uniform seeds
with outputs of explicit length `ℓ n`. -/
structure Ensemble where
  gen : RandFun
  ℓ : PolyExpr

namespace Ensemble

/-- The typed sampler at parameter `n`. -/
def at_ (X : Ensemble) (n : ℕ) : (Fin (X.gen.coinLen n) → Bool) → (Fin (X.ℓ.eval n) → Bool) :=
  fun r => decodeFin (X.ℓ.eval n) (X.gen.run (List.replicate n true) (List.ofFn r))

/-- Post-processing an ensemble by a member `M`, [PS10, Lemma 71.5]. -/
def map (M : RandFun) (X : Ensemble) (ℓ' : PolyExpr) : Ensemble where
  gen := X.gen.seq M X.ℓ
  ℓ := ℓ'

end Ensemble

/-- [PS10, Definition 69.4]. Both ensembles are decoded at `X`'s output length. -/
def Indist (X Y : Ensemble) : Prop :=
  ∀ D, 𝒞.Mem D → Negligible (fun n =>
    distAdv (X.at_ n) (fun r => decodeFin (X.ℓ.eval n) (List.ofFn (Y.at_ n r)))
      (D.distinguisher n (X.ℓ.eval n)))

/-- [PS10, Lemma 71.5] (statement). -/
theorem indist_map (X Y : Ensemble) (M : RandFun) (ℓ' : PolyExpr) (hM : 𝒞.Mem M)
    (h : Indist 𝒞 X Y) : Indist 𝒞 (X.map M ℓ') (Y.map M ℓ') := by
  sorry

/-- [PS10, Lemma 73.8] (statement): a non-negligible distinguishing advantage yields a
member predicting the sample bit with non-negligible advantage. -/
theorem prediction (X₀ X₁ : Ensemble) (D : RandFun) (hD : 𝒞.Mem D)
    (h : ¬ Negligible (fun n => distAdv (X₀.at_ n)
      (fun r => decodeFin (X₀.ℓ.eval n) (List.ofFn (X₁.at_ n r))) (D.distinguisher n (X₀.ℓ.eval n)))) :
    ∃ A, 𝒞.Mem A ∧ ¬ Negligible (fun n =>
      uprob (fun z : Bool × ((Fin (X₀.gen.coinLen n) → Bool) × (Fin (X₁.gen.coinLen n) → Bool))
          × (Fin (A.coinLen (challengeLen n (X₀.ℓ.eval n))) → Bool) =>
        A.distinguisher n (X₀.ℓ.eval n)
          (if z.1 then decodeFin (X₀.ℓ.eval n) (List.ofFn (X₁.at_ n z.2.1.2)) else X₀.at_ n z.2.1.1)
          z.2.2 = z.1) - 1 / 2) := by
  sorry

/-! ### Oracle adversaries and PRFs [PS10, §3.8] -/

/-- An oracle adversary as a next-query strategy: on `pairEncode (1^n) (pairEncode st ans)`
it outputs `pairEncode [true] (pairEncode st' query)` to ask `query`, or
`pairEncode [false] [b]` to stop with output `b`. Coins are fixed for the whole run. -/
abbrev OracleStrategy := RandFun

/-- Unfold a strategy with fixed coins into a query tree of depth at most `q`
(`ret false` when the budget is exhausted). -/
def unfoldTree (S : OracleStrategy) (n ℓ₁ ℓ₂ : ℕ) (r : List Bool) :
    ℕ → List Bool → List Bool → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
  | 0, _, _ => .ret false
  | q + 1, st, ans =>
    let out := S.run (pairEncode (List.replicate n true) (pairEncode st ans)) r
    if (pairFstD out).headD false then
      .query (decodeFin ℓ₁ (pairSndD (pairSndD out)))
        (fun o => unfoldTree S n ℓ₁ ℓ₂ r q (pairFstD (pairSndD out)) (List.ofFn o))
    else .ret ((pairSndD out).headD false)

/-- The concrete oracle adversary induced at parameter `n` with query budget `q`. -/
def RandFun.oracleAdv (S : OracleStrategy) (n ℓ₁ ℓ₂ q : ℕ) :
    OracleAdversary (Fin (S.coinLen (2 * n + 2 + (2 * 0 + 2 + ℓ₂))) → Bool)
      (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) :=
  fun r => unfoldTree S n ℓ₁ ℓ₂ (List.ofFn r) q [] (List.replicate ℓ₂ false)

/-- An ensemble of function distributions [PS10, Definition 96.1], with arbitrary finite
seed types (the random-function ensemble has exponential seeds). -/
structure OracleEnsemble where
  ℓ₁ : PolyExpr
  ℓ₂ : PolyExpr
  σ : ℕ → Type
  [fin : ∀ n, Fintype (σ n)]
  at_ : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)

attribute [instance] OracleEnsemble.fin

/-- [PS10, Definition 96.1]: oracle indistinguishability against every member strategy with
every explicit polynomial query budget. -/
def OracleIndist (O O' : OracleEnsemble) (h₁ : O.ℓ₁ = O'.ℓ₁) (h₂ : O.ℓ₂ = O'.ℓ₂) : Prop :=
  ∀ S, 𝒞.Mem S → ∀ q : PolyExpr, Negligible (fun n =>
    distAdv (O.at_ n) (h₁ ▸ h₂ ▸ O'.at_ n)
      (oracleDist (S.oracleAdv n (O.ℓ₁.eval n) (O.ℓ₂.eval n) (q.eval n))))

/-- The random-function ensemble `RF_n` on `ℓ`-bit inputs and outputs. -/
def randomOracle (ℓ : PolyExpr) : OracleEnsemble where
  ℓ₁ := ℓ
  ℓ₂ := ℓ
  σ n := (Fin (ℓ.eval n) → Bool) → (Fin (ℓ.eval n) → Bool)
  at_ _ := id

/-- A keyed family `f_s` with `|s| = n` as an oracle ensemble. -/
def keyedOracle (ℓ : PolyExpr) (f : ℕ → List Bool → List Bool → List Bool) : OracleEnsemble where
  ℓ₁ := ℓ
  ℓ₂ := ℓ
  σ n := Fin n → Bool
  at_ n s x := decodeFin (ℓ.eval n) (f n (List.ofFn s) (List.ofFn x))

/-- [PS10, Definition 96.2]. -/
def PRF (ℓ : PolyExpr) (f : ℕ → List Bool → List Bool → List Bool) : Prop :=
  (∃ A : RandFun, PPT A ∧ ComputesProb1 A
      (fun z => f (pairFstD z).length (pairFstD (pairSndD z)) (pairSndD (pairSndD z)))) ∧
  OracleIndist 𝒞 (keyedOracle ℓ f) (randomOracle ℓ) rfl rfl

/-! ### Interactive protocols [PS10, §4.4-4.7] -/

/-- A next-message strategy: on `pairEncode x (pairEncode z (pairEncode st msg))` with its
coins (fixed for the whole interaction) it outputs `pairEncode st' msg'`. -/
abbrev Strategy := RandFun

/-- A protocol: two strategies, an explicit round bound, message and state lengths. -/
structure Protocol where
  prover : Strategy
  verifier : Strategy
  rounds : PolyExpr
  msgLen : PolyExpr
  stLen : PolyExpr

namespace Protocol

/-- The strategy input at common input `x`, auxiliary `z`, state `st` and incoming message `m`,
with all fields padded to their declared lengths. -/
def strategyInput (P : Protocol) (x z st m : List Bool) : List Bool :=
  pairEncode x (pairEncode z (pairEncode (RandFun.padTo (P.stLen.eval x.length) st)
    (RandFun.padTo (P.msgLen.eval x.length) m)))

/-- One round: the active party `S` moves. Returns `(new state, message sent)`. -/
def move (P : Protocol) (S : Strategy) (x z st m r : List Bool) : List Bool × List Bool :=
  let o := S.run (P.strategyInput x z st m) (r.take (S.coinLen (P.strategyInput x z st m).length))
  (pairFstD o, pairSndD o)

/-- `k` rounds of execution (verifier moves first in even rounds); returns prover state,
verifier state, last message, and the list of messages the verifier received. -/
def exec (P : Protocol) (x zP zV rP rV : List Bool) : ℕ → List Bool × List Bool × List Bool × List (List Bool)
  | 0 => ([], [], [], [])
  | k + 1 =>
    let (sP, sV, m, recv) := P.exec x zP zV rP rV k
    if k % 2 = 0 then
      let (sV', m') := P.move P.verifier x zV sV m rV
      (sP, sV', m', recv)
    else
      let (sP', m') := P.move P.prover x zP sP m rP
      (sP', sV, m', recv ++ [m'])

/-- The verifier's output: the first bit of its final state. -/
def outV (P : Protocol) (x zP zV rP rV : List Bool) : Bool :=
  ((P.exec x zP zV rP rV (P.rounds.eval x.length)).2.1).headD false

/-- The verifier's view: common input, auxiliary input, coins, received messages. -/
def viewV (P : Protocol) (x zP zV rP rV : List Bool) : List Bool :=
  pairEncode x (pairEncode zV (pairEncode rV
    ((P.exec x zP zV rP rV (P.rounds.eval x.length)).2.2.2.flatMap fun m => pairEncode m [])))

/-- The prover's coin length and the verifier's coin length are functions of `|x|` only. -/
def coinsP (P : Protocol) (n : ℕ) : ℕ := P.prover.coinLen (P.strategyInput (List.replicate n true) [] [] []).length
def coinsV (P : Protocol) (n : ℕ) : ℕ := P.verifier.coinLen (P.strategyInput (List.replicate n true) [] [] []).length

end Protocol

/-- A witness relation with an explicit witness length. -/
structure WitnessRel where
  R : List Bool → List Bool → Prop
  wLen : PolyExpr

/-- [PS10, Definition 116.1]. The malicious prover is any deterministic next-message function
(unbounded; randomized unbounded provers are no stronger). -/
def InteractiveProof (P : Protocol) (L : Set (List Bool)) : Prop :=
  PPT P.verifier ∧
  (∀ x ∈ L, ∃ y, ∀ z, uprob (fun c : (Fin (P.coinsP x.length) → Bool) × (Fin (P.coinsV x.length) → Bool) =>
      P.outV x y z (List.ofFn c.1) (List.ofFn c.2) = true) = 1) ∧
  (∃ ε, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : List Bool → List Bool) z,
    uprob (fun c : Fin (P.coinsV x.length) → Bool =>
      ({ P with prover := RandFun.ofFun P' } : Protocol).outV x [] z [] (List.ofFn c) = true) ≤ ε x.length)

/-- [PS10, Definition 119.5]. -/
def EfficientProver (P : Protocol) (RL : WitnessRel) : Prop :=
  PPT P.prover ∧ ∀ x y, RL.R x y → ∀ z,
    uprob (fun c : (Fin (P.coinsP x.length) → Bool) × (Fin (P.coinsV x.length) → Bool) =>
      P.outV x y z (List.ofFn c.1) (List.ofFn c.2) = true) = 1

/-- A simulator's output at `(x, z)` as a sampler, and the real view as a sampler. -/
def simSampler (S : RandFun) (x z : List Bool) :
    (Fin (S.coinLen (pairEncode x z).length) → Bool) → List Bool :=
  fun r => S.run (pairEncode x z) (List.ofFn r)

def viewSampler (P : Protocol) (x y z : List Bool) :
    (Fin (P.coinsP x.length) → Bool) × (Fin (P.coinsV x.length) → Bool) → List Bool :=
  fun c => P.viewV x y z (List.ofFn c.1) (List.ofFn c.2)

/-- [PS10, Definition 121.1], with the view padded to the explicit length `Lv` for the distinguisher. -/
def HVZK (P : Protocol) (RL : WitnessRel) (Lv : PolyExpr) : Prop :=
  ∃ S : RandFun, PPT S ∧ ∀ D, 𝒞.Mem D → ∃ ε, Negligible ε ∧ ∀ x y z, RL.R x y →
    distAdv (fun c => decodeFin (Lv.eval x.length) (viewSampler P x y z c))
      (fun r => decodeFin (Lv.eval x.length) (simSampler S x z r))
      (D.distinguisher x.length (Lv.eval x.length)) ≤ ε x.length

/-- [PS10, Definition 121.2] with strict-PPT simulators (Deviation, D8). -/
def ZK (P : Protocol) (RL : WitnessRel) (Lv : PolyExpr) : Prop :=
  ∀ V' : Strategy, PPT V' → ∃ S : RandFun, PPT S ∧ ∀ D, 𝒞.Mem D → ∃ ε, Negligible ε ∧
    ∀ x y z, RL.R x y →
      distAdv (fun c => decodeFin (Lv.eval x.length) (viewSampler { P with verifier := V' } x y z c))
        (fun r => decodeFin (Lv.eval x.length) (simSampler S x z r))
        (D.distinguisher x.length (Lv.eval x.length)) ≤ ε x.length

/-- [PS10, Definition 126.3]; binding corrected to `v₀ ≠ v₁` (source error). -/
def Commitment (Com : List Bool → List Bool → List Bool) (ℓ Lc : PolyExpr) : Prop :=
  PolyTimeComputable (fun z => Com (pairFstD z) (pairSndD z)) ∧
  (∀ n (v₀ v₁ : Fin n → Bool) (r₀ r₁ : Fin (ℓ.eval n) → Bool), v₀ ≠ v₁ →
    Com (List.ofFn v₀) (List.ofFn r₀) ≠ Com (List.ofFn v₁) (List.ofFn r₁)) ∧
  (∀ D, 𝒞.Mem D → ∃ ε, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => decodeFin (Lc.eval n) (Com (List.ofFn v₀) (List.ofFn r)))
      (fun r : Fin (ℓ.eval n) → Bool => decodeFin (Lc.eval n) (Com (List.ofFn v₁) (List.ofFn r)))
      (D.distinguisher n (Lc.eval n)) ≤ ε n)

end TCSlib.Cryptography.Asymptotic

/-! ## Judge's refutations (appended to the design's own compiled scratch) -/

namespace TCSlib.Cryptography.Asymptotic

open Turing Complexity

/-- REFUTATION 1: `WeakOWF` as compiled is vacuous — with `q := .const 0` the bound reads
`1 - 1/0 = 1`, which every probability satisfies. -/
theorem weakOWF_of_easyToCompute (𝒞 : AdversaryClass) (f : Family) (h : EasyToCompute f) :
    WeakOWF 𝒞 f := by
  refine ⟨h, .const 0, fun A _ => ⟨0, fun n _ => ?_⟩⟩
  simp only [PolyExpr.eval, Nat.cast_zero, div_zero, sub_zero]
  exact uprob_le_one _

/-- The family with empty outputs (output length `0`): every inverter succeeds. -/
def zeroFamily : Family := ⟨.var, .const 0, fun _ _ => []⟩

theorem easyToCompute_zeroFamily : EasyToCompute zeroFamily :=
  ⟨RandFun.ofFun (fun _ => []), ⟨fun _ => [], polyTimeComputable_const [], fun _ _ _ => rfl⟩,
    fun _ _ _ => rfl⟩

theorem invProb_zeroFamily_prod (q : PolyExpr) (A : RandFun) (n : ℕ) :
    invProb ((zeroFamily.prod q).at_ n)
      (A.inverter n ((zeroFamily.prod q).N.eval n) ((zeroFamily.prod q).m.eval n)) = 1 := by
  have hsub : ∀ a b : Fin ((zeroFamily.prod q).m.eval n) → Bool, a = b := by
    intro a b
    funext i
    exact absurd i.isLt (by simp [zeroFamily, Family.prod, PolyExpr.eval])
  unfold invProb
  exact TCSlib.Cryptography.HardcoreBit.uprob_eq_one_of_forall fun _ => hsub _ _

/-- REFUTATION 2: the compiled statement of `weak_to_strong` is false for every class that
has at least one member (e.g. `nupptClass`, which must contain `ofFun pairSndD`). -/
theorem not_weak_to_strong (𝒞 : AdversaryClass) (A : RandFun) (hA : 𝒞.Mem A) :
    ¬ ∀ f : Family, WeakOWF 𝒞 f → ∃ q : PolyExpr, StrongOWF 𝒞 (f.prod q) := by
  intro h
  obtain ⟨q, -, hstrong⟩ :=
    h zeroFamily (weakOWF_of_easyToCompute 𝒞 zeroFamily easyToCompute_zeroFamily)
  have hneg := hstrong A hA
  simp only [invProb_zeroFamily_prod] at hneg
  obtain ⟨n₀, hn⟩ := hneg 0
  have := hn n₀ le_rfl
  simp at this

/-- REFUTATION 3: the `iterate` field of `EffClass` (no bound on the iterates) cannot be
instantiated with `Eff := PolyTimeComputable`: `step s := s ++ s`, `emit := id`, `R := var`
produce an output of length `≥ 2^|x| |x|`, contradicting `PolyTimeComputable.output_length_le`. -/
theorem not_polyTimeComputable_iterate_doubling :
    ¬ PolyTimeComputable (fun x : List Bool =>
      (List.range (PolyExpr.var.eval x.length + 1)).flatMap fun i =>
        id ((fun s : List Bool => s ++ s)^[i] x)) := by
  intro h
  obtain ⟨C, c, hC⟩ := h.output_length_le
  have hiter : ∀ (x : List Bool) (i : ℕ),
      ((fun s : List Bool => s ++ s)^[i] x).length = 2 ^ i * x.length := by
    intro x i
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', List.length_append, ih]; ring
  have hlow : ∀ m : ℕ, 2 ^ m * m ≤
      ((List.range (PolyExpr.var.eval m + 1)).flatMap fun i =>
        id ((fun s : List Bool => s ++ s)^[i] (List.replicate m true))).length := by
    intro m
    simp only [PolyExpr.eval, List.length_flatMap, List.range_succ, List.map_append,
      List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, id,
      hiter, List.length_replicate]
    omega
  have ht := tendsto_pow_const_div_const_pow_of_one_lt (c + 2) (r := (2 : ℝ)) one_lt_two
  obtain ⟨n₀, h₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds zero_lt_one))
  set m := max n₀ (C * 2 ^ c + 1) with hm
  have hmC : C * 2 ^ c + 1 ≤ m := le_max_right _ _
  have hmn : n₀ ≤ m := le_max_left _ _
  have hm1 : 1 ≤ m := by omega
  have hreal : (m : ℝ) ^ (c + 2) / 2 ^ m < 1 := h₀ m hmn
  have hpow : m ^ (c + 2) < 2 ^ m := by
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    rw [div_lt_one h2] at hreal
    exact_mod_cast hreal
  have hbound := hC (List.replicate m true)
  simp only [List.length_replicate] at hbound
  have key : C * (m + 1) ^ c < 2 ^ m * m := by
    calc C * (m + 1) ^ c ≤ C * (2 * m) ^ c :=
          Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) c)
      _ = C * 2 ^ c * m ^ c := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ m * m ^ c := Nat.mul_le_mul_right _ (by omega)
      _ = m ^ (c + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      _ ≤ m ^ (c + 2) := Nat.pow_le_pow_right hm1 (by omega)
      _ < 2 ^ m := hpow
      _ ≤ 2 ^ m * m := Nat.le_mul_of_pos_right _ hm1
  exact absurd ((hlow m).trans hbound) (not_le.mpr key)

end TCSlib.Cryptography.Asymptotic

#print axioms TCSlib.Cryptography.Asymptotic.weakOWF_of_easyToCompute
#print axioms TCSlib.Cryptography.Asymptotic.not_weak_to_strong
#print axioms TCSlib.Cryptography.Asymptotic.not_polyTimeComputable_iterate_doubling
