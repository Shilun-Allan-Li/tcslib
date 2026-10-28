# Design (run 1, angle ABSTRACT-INTERFACE): the computational-model layer for Pass–shelat ch. 2–4

Status: design proposal for the run-1 panel. All Lean signatures below were compiled with
`lake env lean` against the current worktree (scratch files `/tmp/psdesign/core1.lean`,
`/tmp/psdesign/core2.lean`; the only diagnostics are `declaration uses 'sorry'` on the
statement stubs). Nothing under `TCSlib/` was touched.

## 0. The angle and the verdict in one page

**Angle.** Define an *adversary class* `𝒞 : AdversaryClass`: a membership predicate on
randomized string functions together with the closure properties that the proofs of
[PS10, Chapters 2–4] actually perform on adversaries — composition with efficient string
functions (pre/post-processing), pairing, extra uniform coins, sequential composition of two
members, polynomially many adaptive calls with fresh coins, tagged choice, and (as a mixin)
hard-wiring of advice. State and prove every chapter 2–4 theorem for an arbitrary `𝒞`
satisfying the interface, then instantiate once with non-uniform PPT machines (`NUPPT`),
plus a second, free instantiation with uniform PPT machines (`PPT`), which Chapter 4 needs
anyway (its malicious verifiers and simulators are uniform PPT in [PS10, Def 121.2]).

**What the interface is designed around.** Under the frozen decisions D3/D4 a PPT is a
*deterministic* machine run on `pairEncode x r`; a non-uniform PPT additionally reads
`pairEncode (pairEncode x (α |x|)) r`. So every "randomized adversary" is a deterministic
polynomial-time string function of its input, its coins and its advice, and every closure
property of the adversary class is a closure property of `Complexity.PolyTimeComputable`
plus bookkeeping of coin layouts and advice. The interface therefore has two tiers:

* `EffClass` — a predicate `Eff` on deterministic string functions with the thirteen
  closure fields that the reductions use; eleven of them are **verbatim existing lemmas**
  of `TCSlib/Complexity/ClassNP/{PolyTime,PolyTimePairing}.lean`, one (`splitUnary`) is a
  new linear-time primitive, one (`iterate`) is the new derived loop lemma that the plan
  already names as load-bearing.
* `AdversaryClass extends EffClass` — a predicate `Mem` on `RandFun` (coin length as an
  explicit syntactic polynomial + run function) with four closure fields
  (`ofFun`, `seq`, `iter`, `union`) and the mixin `HasAdvice` (`withAdvice`). Their
  instantiation for `NUPPT` is *pure closure algebra* over `Eff` (no new machines): each is
  a composition of existing `PolyTimeComputable` closure lemmas with the two new `Eff`
  fields.

**Verdict on "does it reduce work or move it".** The machine-level work is the same under
any design: one new primitive (`splitUnary`), one derived loop lemma (`iterate`,
built from `exists_emitLoopTM` and two new call/startup modules), and a handful of derived
polynomial-time string operations (block map, equality, majority, XOR). The interface does
not remove any of it. What it does:

1. isolates the machine obligations into a *closed list* that an auditor checks once
   (§7), and lets the machine agent and the theorem agents work in parallel on disjoint
   files from run 2 on;
2. makes the uniform-PPT instance free, which Chapter 4 needs for simulators (otherwise the
   closure lemmas are proved twice or the ZK definition is changed);
3. costs about 400 lines of structure and instance glue, plus one corollary per headline
   theorem at `𝒞 := nupptClass` (the audit reads those corollaries, not the generic forms);
4. carries one genuine risk: the field list is frozen with the statements (run 2), and a
   closure property missed in §7 forces an interface change under the statement freeze.
   §7 is therefore an exhaustive inventory, slightly over-approximated.

**Audit faithfulness.** The generic theorems are *stronger* than [PS10] (they hold for every
class with the laws); the textbook theorem is the `nupptClass` corollary, which has exactly
the quantifier shape of the source (§8 lists the shapes). The indirection is acceptable to
an audit provided (i) the `NUPPT` instance is closed (not sorried) before any generic
theorem is relied on — otherwise every corollary is conditional on an unproved law — and
(ii) each definition is stated with the class as an explicit argument, never through
typeclass resolution (two instances on the same carrier type would be ambiguous). Both are
build-order and style rules, recorded in §9.

**Recommendation.** Adopt the interface as a *bundled structure passed explicitly* (not a
typeclass), with `PolyExpr` for every length, fixed-length (padded) queries in `seq`/`iter`,
and close `nupptClass` first in run 2 with `iterate` as the single permitted admission.

## 1. The model (D3/D4) restated at the level of string functions

* A randomized string function is `A : RandFun` = (`coins : PolyExpr`, `run : x ↦ r ↦ output`).
  At input `x` the coins are a uniform string of length `A.coinLen |x| = coins.eval |x|`.
  The run on coin strings of other lengths is a don't-care.
* `PPT A` : some total polynomial-time computable `g` (a `Turing.FinTM Bool` with the
  explicit budget `C * (n+1)^c` on **every** input) has `A.run x r = g (pairEncode x r)`
  whenever `|r| = A.coinLen |x|`. Worst case over the random tape [PS10, Def 23.5] is
  automatic: the budget holds on every `pairEncode x r`.
* `NUPPT A` : same with an advice string, `A.run x r = g (pairEncode (pairEncode x (α |x|)) r)`,
  `|α n| = a.eval n` for an explicit `a : PolyExpr`. This is the advice formulation of
  [PS10, Def 26.8] that D4 fixes; `Turing.FinTM.DecidesWithAdviceInTime` is its decision-
  problem relative.
* "Computes `f` with probability 1" [PS10, Def 24.6]: `∀ x r, |r| = coinLen |x| → A.run x r = f x`.

Two deviations are built in and recorded once in the docstrings of `PPT`/`NUPPT`:

* The time bound is measured in the length of the *whole* input string
  `pairEncode (pairEncode x α) r` rather than in `|x|` [PS10, Def 23.5 measures in `|x|`].
  Since that length is an explicit polynomial in `|x|` (`2|x| + 2 + 2 a(|x|) + 2 + coins(|x|)`),
  the two readings give the same class; `nuppt_time_in_input_iff` (≈ 40 lines, pure
  arithmetic on `C (n+1)^c`) records the equivalence. Measuring in the whole input is what
  makes `PolyTimeComputable g` usable verbatim.
* The budget must hold on malformed inputs too (strings that are not well-formed pairs).
  This is a restriction on *which machines* witness membership, not on the class: a machine
  that is polynomial-time on well-formed inputs only can be clocked with
  `Turing.timed_universal` (compute the budget in binary with
  `computesFunInTime_polyBits`, pair with the fixed code by `computesFunInTime_pairEncodeFixed`,
  run `U`, strip the leading `true`). This clocking lemma is optional and not on the
  critical path; the definitions never need it.

## 2. Core signatures (verbatim; compiled)

### 2.1 Lengths are syntax: `PolyExpr`

Every length that depends on the security parameter — coin, advice, output and message
lengths, round and query bounds — is a *syntactic* polynomial expression, never an abstract
`ℕ → ℕ`. This keeps the audit lesson of `TCSlib/Complexity/ClassNP/NP.lean` (an abstract
length function can smuggle undecidable information through the length of a tape — here the
machine can measure `|r|`, so an uncomputable coin-length function would let a "PPT" decide
undecidable unary languages). The campaign normal form `C * (n+1)^c` is `PolyExpr.normal C c`;
the extra constructors are needed because coin budgets of composed adversaries are sums,
products and substitutions of polynomials, and because Yao's inverter needs a power of two
(§3.4): `pow2log` evaluates to `2 ^ Nat.clog 2 (n+1)`, which lies in `[n+1, 2(n+1)]`.

```lean
inductive PolyExpr : Type
  | const : ℕ → PolyExpr
  | var : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  | pow2log : PolyExpr            -- 2 ^ Nat.clog 2 (n + 1); proposed, not in the compiled scratch
  deriving DecidableEq

def PolyExpr.eval : PolyExpr → ℕ → ℕ      -- structural
def PolyExpr.subst : PolyExpr → PolyExpr → PolyExpr   -- p[q/n], eval_subst : (p.subst q).eval n = p.eval (q.eval n)
def PolyExpr.normal (C c : ℕ) : PolyExpr := .mul (.const C) (.pow (.add .var (.const 1)) c)
```

Two lemmas are proved once, by induction on the syntax, and used everywhere:

* `PolyExpr.eval_le : ∃ C c, ∀ n, p.eval n ≤ C * (n+1)^c` (polynomial boundedness);
* `eff_unary (p) : Eff (fun x => List.replicate (p.eval x.length) true)` — unary
  computability; `const`/`var`/`add`/`pow` are `polyTimeComputable_const`, `_unary`,
  `.append`, `_polyUnary`-style compositions, `mul` and `pow2log` are block concatenation /
  doubling loops through `iterate` (§7). This is the *only* place the campaign reasons about
  computing lengths.

### 2.2 Randomized string functions and their sampler view

```lean
structure RandFun where
  coins : PolyExpr
  run : List Bool → List Bool → List Bool

def RandFun.coinLen (A : RandFun) (n : ℕ) : ℕ := A.coins.eval n

/-- The sampler view at a fixed input: uniform coins in, output string out. -/
def RandFun.sample (A : RandFun) (x : List Bool) : (Fin (A.coinLen x.length) → Bool) → List Bool :=
  fun r => A.run x (List.ofFn r)
```

`RandFun.sample A x` is literally a sampler `σ → γ` of the concrete layer with
`σ = Fin ℓ → Bool`; `uprob`, `acceptProb`, `distAdv` apply to it unchanged.

### 2.3 The operations (class-independent definitions)

The operations are plain definitions on `RandFun`; the class only asserts closure. Coin
*layouts* are prefixes of the coin string (`take`/`drop` at explicit lengths); a callee
always receives a block of exactly its own coin length at a *fixed* input length, obtained
by padding the query to an explicit length `q.eval |x|` with `padTo`. Fixing the query
length is what makes a single advice string suffice for the callee (its advice is read at
the fixed length) and what makes every coin type a `Fin ℓ → Bool`.

```lean
def RandFun.ofFun (g : List Bool → List Bool) : RandFun := ⟨.const 0, fun x _ => g x⟩

def RandFun.padTo (L : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate L false).take L

/-- Sequential composition with fresh coins and input pass-through: run `A` on `x` with
`r₁`, pad its answer to `q.eval |x|` bits, run `B` on `pairEncode x answer` with `r₂`. -/
def RandFun.seq (A B : RandFun) (q : PolyExpr) : RandFun where
  coins := .add A.coins (B.coins.subst (.add (.mul (.const 2) .var) (.add (.const 2) q)))
  run x r :=
    let r₁ := r.take (A.coinLen x.length)
    let r₂ := r.drop (A.coinLen x.length)
    let y := pairEncode x (padTo (q.eval x.length) (A.run x r₁))
    B.run y (r₂.take (B.coinLen y.length))

/-- `R.eval |x|` adaptive calls with fresh coin blocks; the deterministic `step` updates the
state `s` from `pairEncode s answer`; the query is `pairSndD s` padded to `q.eval |x|`. -/
def RandFun.iter (A : RandFun) (step : List Bool → List Bool) (q R : PolyExpr) : RandFun where
  coins := .mul R (A.coins.subst q)
  run x r :=
    let L := q.eval x.length
    let ℓ := A.coinLen L
    (Nat.rec (motive := fun _ => List Bool × List Bool) (pairEncode x [], r)
      (fun _ st => (step (pairEncode st.1 (A.run (padTo L (pairSndD st.1)) (st.2.take ℓ))),
        st.2.drop ℓ)) (R.eval x.length)).1

/-- Tagged union: the first input bit selects the member that runs on the rest. -/
def RandFun.union (A B : RandFun) : RandFun where
  coins := .add A.coins B.coins
  run x r := match x with
    | [] => []
    | b :: x' => if b then A.run x' (r.take (A.coinLen x'.length))
        else B.run x' (r.take (B.coinLen x'.length))

/-- Hard-wiring an advice string of explicit length `a.eval n`. -/
def RandFun.withAdvice (A : RandFun) (β : ℕ → List Bool) (a : PolyExpr) : RandFun where
  coins := A.coins.subst (.add (.mul (.const 2) .var) (.add (.const 2) a))
  run x r := A.run (pairEncode x (β x.length)) r
```

Derived operations (definitions + one-line membership lemmas, no new fields):

* `wrap A pre post q := (ofFun pre).seq A q |>.seq (ofFun post) q'` — sandwich with
  deterministic pre/post-processing; extra uniform coins are the `ofFun pre` member's
  pass-through of `x` plus a leading `seq` with `ofFun id` consuming a coin block, i.e. coins
  are obtained by `seq` with the "coin reader" `⟨p, fun _ r => r⟩` (a member by `mem_ofFun`
  applied after `seq` — see `mem_coins` in §7).
* `A.iterCalls` for several distinct callees: `iter (A.union B)` with the tag chosen by `step`.

### 2.4 The machine instance

```lean
def PPT (A : RandFun) : Prop :=
  ∃ (g : List Bool → List Bool), PolyTimeComputable g ∧
    ∀ x r : List Bool, r.length = A.coinLen x.length → A.run x r = g (pairEncode x r)

def NUPPT (A : RandFun) : Prop :=
  ∃ (g : List Bool → List Bool) (α : ℕ → List Bool) (a : PolyExpr), PolyTimeComputable g ∧
    (∀ n, (α n).length = a.eval n) ∧
    ∀ x r : List Bool, r.length = A.coinLen x.length →
      A.run x r = g (pairEncode (pairEncode x (α x.length)) r)

def ComputesProb1 (A : RandFun) (g : List Bool → List Bool) : Prop :=
  ∀ x r, r.length = A.coinLen x.length → A.run x r = g x
```

`PPT A → NUPPT A` (empty advice, `a = .const 0`, re-pair the input: `pairMapSnd`/`pairFstD`
closure). `NUPPT` with `α` fixed is a `P/poly`-style function class; the relation to
`Complexity.PAdvicePoly` (decision problems) is `nuppt_decides_iff_PAdvicePoly` — a
sanity lemma, not on the critical path.

### 2.5 The interface

```lean
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

structure AdversaryClass extends EffClass where
  Mem : RandFun → Prop
  mem_ofFun : ∀ {g}, Eff g → Mem (RandFun.ofFun g)
  mem_seq : ∀ {A B} (q : PolyExpr), Mem A → Mem B → Mem (A.seq B q)
  mem_iter : ∀ {A step} (q R : PolyExpr), Mem A → Eff step → Mem (A.iter step q R)
  mem_union : ∀ {A B}, Mem A → Mem B → Mem (A.union B)

structure AdversaryClass.HasAdvice (𝒞 : AdversaryClass) : Prop where
  mem_withAdvice : ∀ {A} (β : ℕ → List Bool) (a : PolyExpr), 𝒞.Mem A →
    (∀ n, (β n).length = a.eval n) → 𝒞.Mem (A.withAdvice β a)
```

The instances to be provided (run 2, machine layer):

```lean
def effPoly : EffClass := { Eff := PolyTimeComputable, comp := fun hg hh => hg.comp hh, … }
def nupptClass : AdversaryClass := { effPoly with Mem := NUPPT, … }
def pptClass   : AdversaryClass := { effPoly with Mem := PPT, … }
theorem nupptClass_hasAdvice : nupptClass.HasAdvice
theorem ppt_mem_nuppt {A} : pptClass.Mem A → nupptClass.Mem A
```

Why a bundled structure and not a typeclass: `pptClass` and `nupptClass` share the carrier
`RandFun`; as instances they would be ambiguous, and the audit wants the class visible in
every statement (`StrongOWF nupptClass f`), not resolved silently.

Why `Eff` is a separate tier rather than "members with no coins": `mem_iter` and `wrap`
take a *deterministic* step; the instance obligation is then exactly `PolyTimeComputable`
closure, verbatim. (`ofFun`/`Mem` with `coins = const 0` is provably the same predicate as
`Eff` for the two instances; `eff_iff_mem_ofFun` is a sanity lemma.)

### 2.6 Bridges into the concrete layer: `1^n`, decoding, coin spaces

```lean
def decodeFin (n : ℕ) (l : List Bool) : Fin n → Bool := fun i => l.getD i false
def challengeInput (n m : ℕ) (y : Fin m → Bool) : List Bool :=
  pairEncode (List.replicate n true) (List.ofFn y)
def challengeLen (n m : ℕ) : ℕ := 2 * n + 2 + m          -- (challengeInput n m y).length
def RandFun.inverter (A : RandFun) (n N m : ℕ) :
    (Fin m → Bool) → (Fin (A.coinLen (challengeLen n m)) → Bool) → (Fin N → Bool) :=
  fun y r => decodeFin N (A.run (challengeInput n m y) (List.ofFn r))
def RandFun.distinguisher (A : RandFun) (n m : ℕ) :
    (Fin m → Bool) → (Fin (A.coinLen (challengeLen n m)) → Bool) → Bool :=
  fun t r => (A.run (challengeInput n m t) (List.ofFn r)).headD false
```

* **`1^n` is supplied explicitly** as the first component of the adversary's input, as
  [PS10, Def 27.3] prescribes; the coin length is `A.coinLen (challengeLen n m)`, a function
  of `n` and `m` only (`challengeInput_length`), so the coin type is fixed at each parameter.
* **Outputs are decoded** by `decodeFin`: a short output is padded with `false`, a long one
  truncated. D5 says "a wrong-length output counts as failure"; the two readings define the
  same security notions: an adversary that profits from the decoding can be post-processed
  (`wrap` with `padTo`) into one that outputs the decoded string itself, so
  `StrongOWF`/`Indist` are the same predicates under either decoding (remark in the
  docstring; no theorem needed because the campaign commits to `decodeFin`).
* **`invProb (f.at n) (A.inverter n N m)`**, `predProb`, `acceptProb X (D.distinguisher n m)`,
  `distAdv X Y (D.distinguisher n m)` are then the concrete layer's quantities verbatim.
* **Coin-space transport.** Concrete reductions carry structured coin types
  (`Fin T → Fin q × (Fin q → α) × ρ`, `GuessCoins n k ρ`, …). The asymptotic member's coin
  type is `Fin ℓ → Bool`. The two are related by an explicit `Equiv` assembled from
  `Fin.appendEquiv`, `Equiv.arrowCongr`, `Equiv.curry`, `finProdFinEquiv`,
  `Equiv.boolArrowEquivProd`, and `finFunctionFinEquiv : (Fin k → Fin 2) ≃ Fin (2^k)` for
  index types `Fin (2^k)`; probabilities are transported by `uprob_comp_equiv`,
  `acceptProb_comp_equiv`, and unused coordinates are discarded by `acceptProb_fst/snd`,
  `uprob_fst`. Consequence: **every uniform index drawn by a concrete reduction must range
  over a power-of-two type**; `pow2log` in `PolyExpr` exists for this (§3.4, §4.3).

## 3. (b) One-way functions and Theorem 35.1

### 3.1 Families and the typed view

[PS10] writes `f : {0,1}* → {0,1}*`; the amplified function `f'` of Theorem 35.1 is a
*family* `f' : ({0,1}^n)^{m(n)} → …` indexed by `n`, whose input length `n·m(n)` is not
`n`. The uniform device is a family indexed by the parameter with explicit input and output
lengths; a plain string function is the family with `N = var`.

```lean
structure Family where
  N : PolyExpr                       -- input length N n
  m : PolyExpr                       -- output length m n
  F : ℕ → List Bool → List Bool      -- F n, evaluated on N n-bit strings

def Family.at_ (f : Family) (n : ℕ) : (Fin (f.N.eval n) → Bool) → (Fin (f.m.eval n) → Bool) :=
  fun x => decodeFin (f.m.eval n) (f.F n (List.ofFn x))

/-- The direct product of `q n` copies, [PS10, Theorem 35.1]. -/
def Family.prod (f : Family) (q : PolyExpr) : Family where
  N := .mul f.N q
  m := .mul f.m q
  F n z := (List.range (q.eval n)).flatMap fun i =>
    f.F n ((z.drop (i * f.N.eval n)).take (f.N.eval n))
```

Deviations (docstring of `Family`): the parameter `n` is supplied to `F` in unary together
with the input (`pairEncode 1^n x` in `EasyToCompute`), so that non-length-regular
candidates need no index recovery from the input length; for `N = var` the index is the
input length and the convention is invisible. Output length-regularity (`|F n x| = m n`)
is *not* assumed; `decodeFin` makes the typed view total, and for the functions of the
campaign the length equation is proved where it matters (`prod` preserves it).

### 3.2 Definitions 26.1, 27.3, 28.4 (compiled)

```lean
def EasyToCompute (f : Family) : Prop :=
  ∃ A : RandFun, PPT A ∧ ComputesProb1 A (fun z => f.F (pairFstD z).length (pairSndD z))

def WorstCaseOWF (𝒞 : AdversaryClass) (f : Family) : Prop :=
  EasyToCompute f ∧ ¬ ∃ A, 𝒞.Mem A ∧ ∀ n (x : Fin (f.N.eval n) → Bool),
    uprob (fun r => f.at_ n (A.inverter n (f.N.eval n) (f.m.eval n) (f.at_ n x) r) = f.at_ n x) = 1

def StrongOWF (𝒞 : AdversaryClass) (f : Family) : Prop :=
  EasyToCompute f ∧ ∀ A, 𝒞.Mem A →
    Negligible (fun n => invProb (f.at_ n) (A.inverter n (f.N.eval n) (f.m.eval n)))

def WeakOWF (𝒞 : AdversaryClass) (f : Family) : Prop :=
  EasyToCompute f ∧ ∃ q : PolyExpr, ∀ A, 𝒞.Mem A → ∃ n₀, ∀ n ≥ n₀,
    invProb (f.at_ n) (A.inverter n (f.N.eval n) (f.m.eval n)) ≤ 1 - 1 / (q.eval n : ℝ)
```

Notes for the audit:

* `EasyToCompute` is [PS10, Def 24.6] literally (a PPT computing `f` with probability one).
  `easyToCompute_iff_polyTime : EasyToCompute f ↔ PolyTimeComputable (fun z => f.F … )`
  is a 30-line lemma (fix the coins to `0^{coins}`: `polyUnary`-style prefix of `false`s;
  conversely a deterministic machine ignores the coin block via `pairFstD`).
* `StrongOWF`: "for any `A` there is a negligible `ε` with `Pr ≤ ε(n)` for all `n`" is
  `Negligible (fun n => invProb …)` because `invProb ≥ 0` (`Negligible.mono`, `uprob_nonneg`).
* `WeakOWF`: the polynomial `q` is quantified **before** the adversary, as in the source;
  `∀ A, ∃ q` would be a weaker notion for which Theorem 35.1 is not provable as stated.
* `WorstCaseOWF`: the source's adversary gets no `1^n`; here it does (harmless: it can be
  dropped by `pairSndD`). The inner `∀ x` over all strings becomes `∀ n x` over typed inputs.
* Non-vacuity test (cheap, recommended for `audits/pass-shelat/Checks.lean`):
  `not_strongOWF_id : ¬ StrongOWF nupptClass idFamily` — the inverter `ofFun pairSndD` is a
  member (`mem_ofFun`, `fst`/`snd`) and inverts with probability `1`. If the class were
  accidentally empty, this theorem would be unprovable; its proof is the audit's evidence
  that `nupptClass.Mem` is inhabited.

### 3.3 Theorem 35.2 (warm-up: `g(x,y) = (f x, f y)`)

`strong_pair (hf : StrongOWF 𝒞 f) : StrongOWF 𝒞 (f.prod (.const 2))`. Given `B ∈ 𝒞` against
the pair, the inverter of `f` is

`A := (ofFun sampleSecond).seq B q |>.seq (ofFun projectFirst) q'`,

where the coin reader for the fresh `x₂` is a leading `seq` with the coin-reading member
`⟨f.N, fun _ r => r⟩` (membership: `mem_coins`, §7). Membership: `mem_seq` ×3,
`mem_ofFun`, `Eff` of `sampleSecond` (`pair`, `unary`, `splitUnary`, and `EasyToCompute f`
through `easyToCompute_iff_polyTime` and `comp`). Probability: the planted challenge sits
at position `0` of a uniform pair, `uprob_update` (`OneWay`), and the product's `invProb`
restricted to the first coordinate — exactly the concrete computation of
[Gar26, Thm 2.1 for q = 2]; no new concrete lemma. Negligibility: equal probabilities,
`Negligible.mono`.

### 3.4 Theorem 35.1 — statement and proof plan

```lean
theorem weak_to_strong (𝒞 : AdversaryClass) (f : Family) (hf : WeakOWF 𝒞 f) :
    ∃ q : PolyExpr, StrongOWF 𝒞 (f.prod q)
```

The witness is `q := .mul (.const 2) (.mul .pow2log (.subst qw …))`, i.e. a power of two
`m(n) = 2^k(n)` with `2 n q_w(n) ≤ m(n) ≤ 4 (n+1) q_w(n) · const`, where `q_w` is the
polynomial of `hf`. Deviation (docstring): the source takes `m = 2 n q(n)`; a power of two
`≥ 2 n q(n)` is taken instead because the concrete inverter `yaoInverter` draws a
**uniform position** `i ∈ Fin m`, and a uniform element of `Fin m` is a bijective image of
uniform bits only for `m` a power of two (§2.6). The amplification bound only uses
`2n ≤ α m` (`yao_amplification_exp`'s `hq`), so any larger `m` works.

Proof plan (every step names its lemma):

1. **Easy to compute.** `EasyToCompute (f.prod q)` from `EasyToCompute f`:
   `easyToCompute_iff_polyTime` both ways, then `eff_blockMap` (§7, derived from
   `iterate` + `splitUnary` + `unary`): the block-wise application of `F n` to the
   `q.eval n` blocks of `N n` bits is `Eff`.
2. **Contrapositive.** Assume `B ∈ 𝒞` with `¬ Negligible (fun n => invProb ((f.prod q).at_ n) (B.inverter …))`.
   `not_negligible_iff` gives `c` with `1/n^c ≤ invProb_n` for infinitely many `n`.
3. **The reduction as a member.** `A := (B-caller).iter yaoStep (q_query) (T)` with
   `T := .mul (.mul (.const 2) (.mul .var q)) (.pow .var c)` (`T(n) = 2 n m(n) n^c`, the
   source's `2nm²p(n)` with `m` for the extra factor absorbed), where one round of
   `yaoStep` (deterministic, `Eff`) does: read the round's fresh coins `(i, x_j's)` from the
   state's coin block (`splitUnary`, `unary`), build `(f(x_1), …, y at i, …, f(x_m))`
   (`eff_blockMap`, `eff_update`), hand the query to `B` (the `iter` call), and after the
   call project the `i`-th block of the answer (`eff_block`), test `f(z_i) = y` (`eff_eq`),
   and store the first success in the state (`ite`). Membership: `mem_iter` once, plus the
   `Eff` closure of the step (`comp`, `pair`, `fst`, `snd`, `ite`, `append`, `unary`,
   `splitUnary`, `lenEq`, `eff_blockMap`, `eff_update`, `eff_eq`, `eff_block`). The
   fresh coins for sampling `i` and the `x_j` are part of `B`-caller's coin block: the
   callee of `iter` is `coinsThen B := ⟨p, …⟩.seq B …` so that each round draws
   `k(n) + m(n)·N(n)` sampling bits before `B`'s own `B.coinLen` bits (`mem_seq`, `mem_coins`).
4. **Matching lemma** (pure, the fiddly part, ≈ 150–250 lines):
   `inverter_iter_eq_yaoInverter : ∃ e : (Fin ℓ_A → Bool) ≃ Fin T → Fin m × (Fin m → (Fin N → Bool)) × (Fin ℓ_B → Bool),
     ∀ y c, A.inverter n (N·m) (m_f·m) y (e.symm c) = yaoInverter (f.at_ n) (B.inverter' n) T y c`,
   by induction on `T` relating `Nat.rec` on the state (first success kept) with the
   `List.foldr` of `yaoInverter` over `List.finRange T` (`yaoInverter_spec` gives the
   "first success" property; a small lemma `foldr_finRange_first_success` closes the gap).
   Here `B.inverter'` is `B.inverter` conjugated by `finProdFinEquiv`-based equivalences
   `(Fin m → Fin N → Bool) ≃ (Fin (N·m) → Bool)` (`Equiv.curry`, `finProdFinEquiv`,
   `Equiv.arrowCongr`), and `(f.prod q).at_ n = prodFun (f.at_ n) m` up to the same
   equivalences (`prod_at_eq_prodFun`, by `List.flatMap`/`List.take`/`List.drop` arithmetic).
5. **Transport.** `invProb (f.at_ n) (A.inverter …) = invProb (f.at_ n) (yaoInverter …)`
   by `uprob_comp_equiv (Equiv.refl _ |>.prodCongr e)` and step 4.
6. **Concrete bound.** For each `n` in the infinite set of step 2 with `n ≥ n₁`:
   `yao_amplification_exp (f.at_ n) (B.inverter' n) (T n)` with `α' := 1/q_w(n)`,
   `μ₀ := 1/n^c`, hypotheses: `hα₁ : 1/q_w(n) ≤ 1` (`q_w(n) ≥ 1`), `hq : 2n ≤ (1/q_w) m`
   (choice of `m`), `hT : 2 n m ≤ μ₀ T` (choice of `T`), `hμ₀ : 2 e^{-n} < 1/n^c`
   (`Real.exp` vs polynomial: `tendsto_pow_const_div_const_pow_of_one_lt`, as in
   `negligible_two_pow_neg`), `hμ : μ₀ ≤ invProb (prodFun …) …` (step 2 + step 4's
   transport for `B`). Conclusion: `1 - 1/(2 q_w(n)) - e^{-n} ≤ invProb (f.at_ n) (A.inverter …)`.
7. **Contradiction with weakness.** `hf.2` for `A ∈ 𝒞` gives `n₀` with
   `invProb ≤ 1 - 1/q_w(n)` for `n ≥ n₀`; for the infinitely many `n ≥ max n₀ n₁ n₂` with
   `e^{-n} < 1/(2 q_w(n))` (`n₂` from the same exponential-vs-polynomial lemma) the two
   bounds contradict. `linarith`.

Closure fields used by Theorem 35.1: `mem_iter`, `mem_seq`, `mem_ofFun`, `mem_coins`
(derived), and the `Eff` fields `comp`, `pair`, `fst`, `snd`, `ite`, `append`, `unary`,
`splitUnary`, `lenEq`, `iterate` (through `eff_blockMap`, `eff_update`, `eff_eq`,
`eff_block`). No advice is needed (`T`, `m` are uniform in `n`; the "infinitely many `n`"
is handled by `not_negligible_iff`, not by advice).

### 3.5 What Theorem 36.3 / 33.5 and the collections need (scope note)

The same `Family` + `𝒞` vocabulary carries §2.5 (collections `(Gen, Samp, f_i)`: three
members/`Eff` functions with the index ensemble as an `Ensemble` of §4), §2.10–2.11
(one-way/trapdoor permutations: `f.at_ n` bijective plus a trapdoor `Eff` inverter), and
Levin's universal function (§2.13: the code `α` of the candidate is a `withAdvice`-free
uniform enumeration via `Turing.timed_universal`; `EffectiveMachineCode.decode` and the
quadratic clock give the `n^3`-time truncation). None of these need closure fields beyond
§7's list.

## 4. (c) Ensembles and computational indistinguishability [PS10, §3.1]

### 4.1 Ensembles (D6) and the definition (compiled)

```lean
structure Ensemble where
  gen : RandFun          -- run on 1^n with gen.coinLen n uniform seed bits
  ℓ : PolyExpr           -- output length ℓ n

def Ensemble.at_ (X : Ensemble) (n : ℕ) : (Fin (X.gen.coinLen n) → Bool) → (Fin (X.ℓ.eval n) → Bool) :=
  fun r => decodeFin (X.ℓ.eval n) (X.gen.run (List.replicate n true) (List.ofFn r))

/-- Post-processing by a member `M`, [PS10, Lemma 71.5]: sample `X_n`, run `M (1^n, t)`. -/
def Ensemble.map (M : RandFun) (X : Ensemble) (ℓ' : PolyExpr) : Ensemble where
  gen := X.gen.seq M X.ℓ
  ℓ := ℓ'

def Indist (𝒞 : AdversaryClass) (X Y : Ensemble) : Prop :=
  ∀ D, 𝒞.Mem D → Negligible (fun n =>
    distAdv (X.at_ n) (fun r => decodeFin (X.ℓ.eval n) (List.ofFn (Y.at_ n r)))
      (D.distinguisher n (X.ℓ.eval n)))
```

* An ensemble *is* a member evaluated on `1^n` (so its seed length is `gen.coinLen n`, an
  explicit polynomial — D6); "efficiently samplable" is `pptClass.Mem X.gen`; an arbitrary
  ensemble of [PS10, Def 69.3] over `{0,1}^{ℓ(n)}` that is a pushforward of uniform bits is
  representable; dyadic distributions only (Deviation, D6). The random-function ensemble of
  §5 is *not* of this form and gets its own structure.
* [PS10, Def 69.4] gives the distinguisher only `t`; `D.distinguisher` gives it
  `pairEncode 1^n t`. Since `|t| = ℓ(n)` reveals `n` only for injective `ℓ`, supplying `1^n`
  is the standard reading (Deviation note).
* Both samples are decoded at `X`'s length; the theorems are stated for pairs with
  `X.ℓ = Y.ℓ` (hypothesis `hℓ`), so `decodeFin` is the identity on `Y`'s samples.

### 4.2 Lemma 71.5 (closure under efficient operations)

```lean
theorem indist_map (𝒞) (X Y : Ensemble) (M : RandFun) (ℓ' : PolyExpr) (hM : 𝒞.Mem M)
    (h : Indist 𝒞 X Y) : Indist 𝒞 (X.map M ℓ') (Y.map M ℓ')
```

Proof: for `D ∈ 𝒞` against the mapped ensembles, the member `D' := M.seq D ℓ'` is in `𝒞`
(`mem_seq`). The concrete identity is the randomized sunglass lemma `distAdv_sunglassRed`
with `P := fun t c => M.run (pairEncode 1^n t) c` (coins `κ = Fin (M.coinLen …) → Bool`) and
`D` as the distinguisher of the pushed samples — `pushSampler P X` is `(X.map M ℓ').at_ n`
up to `decodeFin`/`padTo` and the coin layout of `seq` (`acceptProb_bind` moves `M`'s
coins into the sampler; `acceptProb_comp_equiv` with `Fin.appendEquiv` splits the member's
coin string into `M`'s and `D`'s blocks). Matching lemma `distinguisher_seq_eq_sunglassRed`
(≈ 60 lines). Then `h D' hD'` is the negligible advantage of `D'` against `X, Y`, which
*equals* `D`'s advantage against the maps: `Negligible.mono` with equality.

### 4.3 Lemma 71.6 (hybrid lemma) and the multicopy corollary

The hybrid lemma as stated in [PS10] is the concrete `exists_hybrid_gap`
(`Foundations/Probability.lean`), with `abs_sub_le_sum_hybrids` for the telescoping form;
it is re-exported with the `[PS10, Lemma 71.6]` citation, not re-proved. Its asymptotic
consequences are:

* `indist_trans : Indist 𝒞 X Y → Indist 𝒞 Y Z → Indist 𝒞 X Z` — triangle inequality on
  `distAdv` with the *same* `D`, `Negligible.add`. No closure field is used (a frequent
  audit question: transitivity of `≈` needs no reduction).
* The multicopy lemma (`t(n)` independent copies, [PS10] uses it in §3.6 for multi-message
  security): `indist_copies (hX : 𝒞.Mem X.gen) (hY : 𝒞.Mem Y.gen) (t : PolyExpr) :
  Indist 𝒞 X Y → Indist 𝒞 (X.copies t) (Y.copies t)`. Two routes, both expressible:
  (i) non-uniform (`HasAdvice`): `exists_multicopyRed_ge` gives, for each `n`, a hybrid
  index `k(n) < t(n)` with advantage `≥ ε(n)/t(n)`; `k` becomes advice (`mem_withAdvice`,
  with `k(n)` chosen by `Classical.choose` and written as `Nat.bits`), and the reduction
  `multicopyRed X Y t k D` is `wrap`/`iter` over `X.gen.union Y.gen` (sampling `t-1` copies)
  followed by one call to `D` (`mem_seq`); (ii) uniform: `distAdv_multicopyAvgRed` with
  `mixDist` drawing `k` uniformly in `Fin t` — requires `t` a power of two (`pow2log`), and
  then no advice is needed. The design recommends (ii) for `pptClass` compatibility and
  keeps (i) as the literal rendering of [PS10]'s footnote-style argument. Negligible
  arithmetic: `Negligible.mul_pow` (`t(n)` is polynomial).
* The pointwise matching lemma (`multicopyRed`'s coin type
  `((Fin t → σ) × (Fin t → τ)) × ρ` vs. the member's coin string) is again an `Equiv` of
  `Fin.appendEquiv`/`Equiv.arrowCongr` plus `acceptProb_comp_equiv`.

### 4.4 Lemma 73.8 (prediction lemma)

Statement (compiled, in `core2.lean`): from `D ∈ 𝒞` with non-negligible advantage between
`X₀` and `X₁`, a member `A ∈ 𝒞` whose success at guessing `b` from `t ← X_n^b` is
non-negligibly above `1/2`. The source states it "for infinitely many `n`"; `¬ Negligible`
is that statement through `not_negligible_iff`.

Proof: the concrete step is new but tiny (`predProb_flip`, ≈ 20 lines, the computation
displayed in the source): with `p_b := acceptProb (X^b) D`,
`Pr[A_flip(t) = b] = 1/2 + (p_1 - p_0)/2` for `flip = false` and `1/2 - (p_1 - p_0)/2` for
`flip = true` (`uprob_bool_prod` from `GeneratorFromPermutation.lean` does the `b ← {0,1}`
split; the shape is `predProb_owpPredictor_false/true`). Asymptotics: if
`|p_1 - p_0| ≥ 1/n^c` infinitely often then one of the two signs occurs infinitely often
(infinite pigeonhole on the two subsets of an infinite set — `Set.infinite_of_not_bddAbove`
style, 10 lines), so one `flip ∈ Bool` works uniformly in `n`: **no advice**, exactly as in
the source ("one of these distinguishers works for infinitely many `n`"). Membership:
`A := D.seq (ofFun (xorLast flip))` — `mem_seq`, `mem_ofFun`, `Eff` of a one-bit XOR
(`ite`/`const`).

### 4.5 What the rest of Chapter 3 needs from this section

Pseudorandom ensembles (Def 74.1: `Indist 𝒞 X (uniform ℓ)` with `uniform ℓ := ⟨⟨ℓ, fun _ r => r⟩, ℓ⟩`),
the next-bit test (Thm 75.4: hybrids over prefixes + the prediction lemma; the predictor's
"majority of several runs" is `iter` + `eff_majority`), PRGs (Def 77.1), expansion
(`exists_prgExtBitsRed_ge`, hybrid index by advice or `prgAdv_prgExtAvgRed` with a
power-of-two `l`), hard-core predicates and Goldreich–Levin
(`invProb_guessInverter_cubic`; the inverter `guessInverter A k` has coin type
`GuessCoins n k ρ = (Fin k → Fin n → Bool) × (Fin k → Bool) × (Fin n → NESubset k → ρ)`; its
member form is `iter` over `A` with `n (2^k - 1)` rounds, the round index decoded into
`(i, L)` by `Nat.bits`-style enumeration of the nonempty subsets, so a concrete
`NESubset k ≃ Fin (2^k - 1)` must be *definable*, e.g. `L i := (Finset.univ.filter fun j => (i+1).testBit j)`,
not obtained from `Fintype.equivFinOfCardEq`). All of this uses only §7's fields.

## 5. (d) Oracle indistinguishability and pseudorandom functions [PS10, §3.8]

### 5.1 Oracle adversaries as next-query strategies (D7)

The concrete layer's oracle adversary is a bounded query tree
`OracleAdversary ρ I O = ρ → QueryTree I O Bool`. The asymptotic layer needs an
*efficiency* notion for the tree. Machine-level oracle tapes are not formalized (D7;
`Turing.OracleTM` has language oracles only), so an oracle machine is a **next-query
strategy**: a member that is re-invoked with its state and the last answer and either asks
the next query or stops. This is the same device as Chapter 4's next-message strategies
(one mechanism for both), and it is how [PS10] itself describes ITMs (idle state, resumption).

```lean
abbrev OracleStrategy := RandFun
-- input  pairEncode (1^n) (pairEncode st ans)
-- output pairEncode [true] (pairEncode st' query)   -- ask `query`, continue with st'
--     or pairEncode [false] [b]                     -- stop, output b

def unfoldTree (S : OracleStrategy) (n ℓ₁ ℓ₂ : ℕ) (r : List Bool) :
    ℕ → List Bool → List Bool → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
  | 0, _, _ => .ret false
  | q + 1, st, ans =>
    let out := S.run (pairEncode (List.replicate n true) (pairEncode st ans)) r
    if (pairFstD out).headD false then
      .query (decodeFin ℓ₁ (pairSndD (pairSndD out)))
        (fun o => unfoldTree S n ℓ₁ ℓ₂ r q (pairFstD (pairSndD out)) (List.ofFn o))
    else .ret ((pairSndD out).headD false)

def RandFun.oracleAdv (S : OracleStrategy) (n ℓ₁ ℓ₂ q : ℕ) :
    OracleAdversary (Fin (S.coinLen (2 * n + 2 + (2 * 0 + 2 + ℓ₂))) → Bool) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) :=
  fun r => unfoldTree S n ℓ₁ ℓ₂ (List.ofFn r) q [] (List.replicate ℓ₂ false)
```

The coin string is fixed for the whole run (the strategy is deterministic given `r`; it may
copy whatever it needs into its state). The state is **not** padded in `unfoldTree`
(the tree is a semantic object); the input length to `S` therefore varies with the state,
and `S.coinLen` must be read at a fixed length — the scratch signature reads it at the
empty-state length and the design fixes this by padding the state to an explicit
`stLen : PolyExpr` as in Chapter 4 (`strategyInput`); the compiled form is the simplest
one that typechecks and is to be replaced by the padded one in run 2.

**Efficiency condition imposed by the asymptotic layer** ([PS10, Def 96.1]'s "n.u. p.p.t.
oracle machine"): `𝒞.Mem S` together with an explicit query budget `q : PolyExpr`; the
unfolding is cut off after `q.eval n` queries with output `false` (Deviation: a polynomial-
time oracle machine makes polynomially many queries automatically; here the bound is a
parameter and the cutoff is the clock). `unfoldTree_boundedBy : (S.oracleAdv n ℓ₁ ℓ₂ q).BoundedBy q`
holds by construction (induction on `q`), which is exactly the hypothesis `hA : A.BoundedBy q`
of `ggm_prfAdv_le`/`exists_ggmBits_dist`.

### 5.2 Oracle ensembles and the definitions (compiled)

```lean
structure OracleEnsemble where
  ℓ₁ ℓ₂ : PolyExpr
  σ : ℕ → Type
  [fin : ∀ n, Fintype (σ n)]
  at_ : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)

def OracleIndist (𝒞) (O O' : OracleEnsemble) (h₁ : O.ℓ₁ = O'.ℓ₁) (h₂ : O.ℓ₂ = O'.ℓ₂) : Prop :=
  ∀ S, 𝒞.Mem S → ∀ q : PolyExpr, Negligible (fun n =>
    distAdv (O.at_ n) (h₁ ▸ h₂ ▸ O'.at_ n) (oracleDist (S.oracleAdv n (O.ℓ₁.eval n) (O.ℓ₂.eval n) (q.eval n))))

def randomOracle (ℓ : PolyExpr) : OracleEnsemble :=        -- RF_n: the seed is the table
  { ℓ₁ := ℓ, ℓ₂ := ℓ, σ := fun n => (Fin (ℓ.eval n) → Bool) → (Fin (ℓ.eval n) → Bool), at_ := fun _ => id }
def keyedOracle (ℓ : PolyExpr) (f : ℕ → List Bool → List Bool → List Bool) : OracleEnsemble :=
  { ℓ₁ := ℓ, ℓ₂ := ℓ, σ := fun n => Fin n → Bool, at_ := fun n s x => decodeFin (ℓ.eval n) (f n (List.ofFn s) (List.ofFn x)) }

def PRF (𝒞) (ℓ : PolyExpr) (f : ℕ → List Bool → List Bool → List Bool) : Prop :=
  (∃ A : RandFun, PPT A ∧ ComputesProb1 A (fun z => f (pairFstD z).length (pairFstD (pairSndD z)) (pairSndD (pairSndD z)))) ∧
  OracleIndist 𝒞 (keyedOracle ℓ f) (randomOracle ℓ) rfl rfl
```

The random-function ensemble has an exponential seed (the whole table), so
`OracleEnsemble` allows an arbitrary finite seed type per `n` — this is why oracle
ensembles are not `Ensemble`s. `distAdv` only needs `[Fintype (σ n)]`. The `h₁ ▸ h₂ ▸`
transport is ugly; run 2 should instead parametrize `OracleIndist` by `ℓ₁ ℓ₂` and take two
samplers at those lengths (the compiled form proves the typing works either way).

### 5.3 Theorem 97.3 (GGM) in this model and the reuse of the concrete layer

`ggm_prf (hG : PRG 𝒞 G length-doubling) : PRF 𝒞 var (ggmString G)` where `ggmString G n s x`
walks the tree with the string-level `G` (`Eff` through `eff_blockMap`/`iterate`: `n`
rounds, each applying `G` and selecting a half by `splitUnary`). Given a member strategy
`S` with budget `q`, the PRG distinguisher is the member

`R := (hybrid-index reader).seq ((S.union (ofFun G-eval)).iter simStep (q_query) (q))`

whose `simStep` answers each query of `S` by the lazily sampled table of level `i`
(`levelAdv`/`tableDist` of `GGM.lean`): the state carries the `q` fresh labels (from the
member's own coins — `uprob_evalLazy` from `LazySampling.lean` is the bridge that replaces
the random table `(Fin i → Bool) → S` by a stream of `q` fresh labels consumed lazily, which
is precisely what a machine can sample) and the challenge at position `j`. The hybrid
indices `(i, j)` come from `exists_ggmBits_dist` (non-uniform: `mem_withAdvice`) or from a
uniform average (`mixDist` over `Fin n × Fin q`, both powers of two via `pow2log`,
`distAdv_mixDist_eq`). Concrete bound: `exists_ggmBits_dist` gives
`prfAdv (ggmBits G) A / (n q) ≤ distAdv G id (ggmBitsDist G A q i j)`; the matching lemma
`oracleDist_simStep_eq_ggmBitsDist` relates the `iter` member to `ggmBitsDist` pointwise
(the longest matching lemma of Chapter 3, ≈ 200 lines: induction on the query tree
`unfoldTree`, with `QueryTree.eval_simulate` on the `levelAdv` side). Negligibility:
`Negligible.mul_pow` twice.

The remark after [PS10, Def 96.1] ("oracle indistinguishability satisfies closure, the
hybrid lemma and the prediction lemma") becomes three lemmas with the same proofs as §4,
with `oracleDist` in place of `distinguisher`; they are stated, and only the closure one is
needed later (§3.9 multi-message encryption).

## 6. (e) Chapter 4: interaction, interactive proofs, zero knowledge, commitments

### 6.1 Strategies, protocols, executions, views (compiled; D8)

An interactive machine [PS10, §4.4] is a next-message strategy: a member run on the
common input, its auxiliary input, its current state and the incoming message, with a coin
string fixed for the whole interaction (the ITM's random tape). All fields are padded to
explicit lengths so that the strategy's input length — hence its coin length — is a
function of `|x|` only.

```lean
abbrev Strategy := RandFun
-- input  pairEncode x (pairEncode z (pairEncode st msg)), output pairEncode st' msg'

structure Protocol where
  prover : Strategy
  verifier : Strategy
  rounds : PolyExpr        -- number of moves
  msgLen : PolyExpr        -- every message padded to msgLen |x|
  stLen : PolyExpr         -- every state padded to stLen |x|
  -- proposed addition (not in the scratch): verifierFirst : Bool

def Protocol.strategyInput (P : Protocol) (x z st m : List Bool) : List Bool :=
  pairEncode x (pairEncode z (pairEncode (RandFun.padTo (P.stLen.eval x.length) st)
    (RandFun.padTo (P.msgLen.eval x.length) m)))

def Protocol.move (P : Protocol) (S : Strategy) (x z st m r : List Bool) : List Bool × List Bool :=
  let o := S.run (P.strategyInput x z st m) (r.take (S.coinLen (P.strategyInput x z st m).length))
  (pairFstD o, pairSndD o)

/-- `k` moves; returns prover state, verifier state, last message, messages received by V. -/
def Protocol.exec (P : Protocol) (x zP zV rP rV : List Bool) :
    ℕ → List Bool × List Bool × List Bool × List (List Bool)
  | 0 => ([], [], [], [])
  | k + 1 =>
    let (sP, sV, m, recv) := P.exec x zP zV rP rV k
    if k % 2 = 0 then                                   -- with verifierFirst: (k + offset) % 2
      let (sV', m') := P.move P.verifier x zV sV m rV
      (sP, sV', m', recv)
    else
      let (sP', m') := P.move P.prover x zP sP m rP
      (sP', sV, m', recv ++ [m'])

def Protocol.outV (P : Protocol) (x zP zV rP rV : List Bool) : Bool :=
  ((P.exec x zP zV rP rV (P.rounds.eval x.length)).2.1).headD false
def Protocol.viewV (P : Protocol) (x zP zV rP rV : List Bool) : List Bool :=
  pairEncode x (pairEncode zV (pairEncode rV
    ((P.exec x zP zV rP rV (P.rounds.eval x.length)).2.2.2.flatMap fun m => pairEncode m [])))
def Protocol.coinsP (P : Protocol) (n : ℕ) : ℕ := P.prover.coinLen (P.strategyInput (List.replicate n true) [] [] []).length
def Protocol.coinsV (P : Protocol) (n : ℕ) : ℕ := P.verifier.coinLen (P.strategyInput (List.replicate n true) [] [] []).length
```

* `exec` iterates the two strategies (D8); who moves first is a protocol field (GNI: verifier
  first; GI and 3-colouring: prover first). The verifier's output is the first bit of its
  final state; its view is `(x, z_V, r_V, messages received)` [PS10, "Executions, transcripts
  and views"], as a self-delimiting chunk list (`pairEncode m []` chunks parse with
  `pairFstD/pairSndD`).
* Random executions: `uprob` over `(Fin (coinsP |x|) → Bool) × (Fin (coinsV |x|) → Bool)`.
* Time complexity of an ITM [PS10, p. 116] is the strategy's membership in `pptClass`:
  the worst-case bound over all incoming messages is automatic (the budget holds on every
  input string).
* The auxiliary input `z` is unbounded in length in the source; here `z` is any string, and
  `strategyInput`'s length grows with `|z|`, so the strategy's coin length depends on `|z|`
  as well. The compiled `coinsP/coinsV` read it at `z = []`; run 2 should either pad `z` to
  an explicit `auxLen` or make `coinsP/coinsV` functions of `(|x|, |z|)`. The second is
  faithful and costs nothing (the definitions below quantify over `z` and only need the
  coin type to be determined by `(x, z)`).

### 6.2 Interactive proofs [116.1], efficient provers [119.5] (compiled)

```lean
structure WitnessRel where
  R : List Bool → List Bool → Prop
  wLen : PolyExpr

def InteractiveProof (P : Protocol) (L : Set (List Bool)) : Prop :=
  PPT P.verifier ∧
  (∀ x ∈ L, ∃ y, ∀ z, uprob (fun c : (Fin (P.coinsP x.length) → Bool) × (Fin (P.coinsV x.length) → Bool) =>
      P.outV x y z (List.ofFn c.1) (List.ofFn c.2) = true) = 1) ∧
  (∃ ε, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : List Bool → List Bool) z,
    uprob (fun c : Fin (P.coinsV x.length) → Bool =>
      ({ P with prover := RandFun.ofFun P' } : Protocol).outV x [] z [] (List.ofFn c) = true) ≤ ε x.length)

def EfficientProver (P : Protocol) (RL : WitnessRel) : Prop :=
  PPT P.prover ∧ ∀ x y, RL.R x y → ∀ z,
    uprob (fun c : (Fin (P.coinsP x.length) → Bool) × (Fin (P.coinsV x.length) → Bool) =>
      P.outV x y z (List.ofFn c.1) (List.ofFn c.2) = true) = 1
```

* Soundness quantifies `∃ ε` **before** `x`, `P*` and `z`, as the source does; the
  malicious prover `P*` is an arbitrary *deterministic* next-message function
  (Deviation note: an unbounded randomized prover is no stronger, by averaging over its
  coins — not formalized, a one-line remark; this avoids quantifying over coin lengths of
  unbounded machines). `P*` gets no auxiliary input, as in the source.
* `L ∈ NP` of Def 121.1 is rendered through a `WitnessRel` with explicit witness length
  (`Complexity.NP`'s certificate shape `C (|x|+1)^c`), with `L = {x | ∃ y, RL.R x y}` when
  needed; `NP`-membership of `L` is a separate hypothesis where a theorem needs it.

### 6.3 HVZK [121.1], ZK [121.2] with strict-PPT simulators, commitments [126.3] (compiled)

```lean
def simSampler (S : RandFun) (x z : List Bool) : (Fin (S.coinLen (pairEncode x z).length) → Bool) → List Bool :=
  fun r => S.run (pairEncode x z) (List.ofFn r)
def viewSampler (P : Protocol) (x y z : List Bool) :
    (Fin (P.coinsP x.length) → Bool) × (Fin (P.coinsV x.length) → Bool) → List Bool :=
  fun c => P.viewV x y z (List.ofFn c.1) (List.ofFn c.2)

def HVZK (𝒞) (P : Protocol) (RL : WitnessRel) (Lv : PolyExpr) : Prop :=
  ∃ S : RandFun, PPT S ∧ ∀ D, 𝒞.Mem D → ∃ ε, Negligible ε ∧ ∀ x y z, RL.R x y →
    distAdv (fun c => decodeFin (Lv.eval x.length) (viewSampler P x y z c))
      (fun r => decodeFin (Lv.eval x.length) (simSampler S x z r))
      (D.distinguisher x.length (Lv.eval x.length)) ≤ ε x.length

def ZK (𝒞) (P : Protocol) (RL : WitnessRel) (Lv : PolyExpr) : Prop :=
  ∀ V' : Strategy, PPT V' → ∃ S : RandFun, PPT S ∧ ∀ D, 𝒞.Mem D → ∃ ε, Negligible ε ∧
    ∀ x y z, RL.R x y →
      distAdv (fun c => decodeFin (Lv.eval x.length) (viewSampler { P with verifier := V' } x y z c))
        (fun r => decodeFin (Lv.eval x.length) (simSampler S x z r))
        (D.distinguisher x.length (Lv.eval x.length)) ≤ ε x.length

def Commitment (𝒞) (Com : List Bool → List Bool → List Bool) (ℓ Lc : PolyExpr) : Prop :=
  PolyTimeComputable (fun z => Com (pairFstD z) (pairSndD z)) ∧
  (∀ n (v₀ v₁ : Fin n → Bool) (r₀ r₁ : Fin (ℓ.eval n) → Bool), v₀ ≠ v₁ →
    Com (List.ofFn v₀) (List.ofFn r₀) ≠ Com (List.ofFn v₁) (List.ofFn r₁)) ∧
  (∀ D, 𝒞.Mem D → ∃ ε, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => decodeFin (Lc.eval n) (Com (List.ofFn v₀) (List.ofFn r)))
      (fun r : Fin (ℓ.eval n) → Bool => decodeFin (Lc.eval n) (Com (List.ofFn v₁) (List.ofFn r)))
      (D.distinguisher n (Lc.eval n)) ≤ ε n)
```

* The quantifier order of ZK is the source's: `∀ V*, ∃ S, ∀ D, ∃ ε, ∀ x y z`. `V*` and `S`
  are **uniform** PPT (`pptClass`), `D` ranges over `𝒞` (= `nupptClass` in the corollary):
  this is where the second instance earns its keep — the simulator's efficiency proofs are
  the `pptClass` closure fields.
* Strict polynomial time for `S` (Deviation, D8); the GI simulator is truncated (§6.4).
* The view is padded to an explicit `Lv` for the distinguisher; for the protocols of the
  campaign `Lv` is computed from `rounds`, `msgLen`, `coinsV`.
* `Commitment`'s binding clause is corrected to `v₀ ≠ v₁ → …`; the source's text omits the
  hypothesis (error to be added to the plan's list). Hiding quantifies `∃ ε` before
  `v₀ v₁` — uniform over the committed values, as the source. Theorem 126.4 (commitments
  from one-way permutations with a hard-core bit, `Com(b, r) = (f r, b ⊕ h r)`) is the PRG
  from OWP + hard-core argument `exists_owpPredictorBits` reused one bit at a time, with
  `n`-bit values by the hybrid over bits (`exists_hybrid_gap`).

### 6.4 The graph-isomorphism protocol, its simulator, Lemma 123.5, Theorem 122.3

**Data.** Graphs on `n` vertices are adjacency strings of `n·n` bits (`Fin n → Fin n → Bool`
with `Equiv.curry`/`finProdFinEquiv` for the typed view), permutations are lists of `n`
unary tokens (`unaryTokenSplit` parses them), a common input `x = pairEncode G₀ G₁`, witness
`σ` with `σ • G₀ = G₁`, `giRel : WitnessRel`.

**Protocol 120.6** (one iteration; `rounds = 3`, prover first): `giProver` state `pairEncode π σ`;
move 1 sends `H = π • G₀`; move 3 sends `π` if `b = 0` else `π ∘ σ⁻¹`. `giVerifier` sends a
coin bit `b` and finally checks `γ • G_b = H`. Sequential repetition `|G₁|` times is the
same strategies with the round counter in the state (`rounds = 3n`), or the generic
`Protocol.repeat` (Deviation note of [PS10, Thm 122.3]'s "we only provide a simulator for
a single iteration"). Proposition 120.7 (completeness and soundness `1/2` per iteration,
`2^{-n}` after `n`) is a concrete probability statement about `giVerifier`'s coins:
soundness is "`H` is isomorphic to at most one of `G₀, G₁`, and `b` is chosen after `H`"
(`uprob_prod` with the prover's message fixed in the first coordinate, then
`uprob_eq_one_div_card` for the bit). (The source says "interactive proof for `L_niso`";
it is `L_iso` — already in the plan's error list.)

**Permutations from coins.** The honest prover draws `π ← S_n`. `|S_n| = n!` is not a power
of two, so no bijective image of uniform bits is uniform on `S_n`. Two layers:

* the **typed concrete protocol** `giTyped n` uses the coin type `Equiv.Perm (Fin n) × …`
  directly (the concrete layer accepts any `Fintype`), and Lemma 123.5 is proved there
  **exactly as stated**: `uprob (fun c => H c = h) = uprob (fun π : Perm (Fin n) => π • G₀ = h)`
  for every `h` (translation invariance: `pushesUniform_equiv (Equiv.mulRight σ)` — the
  multiplicative sibling of `pushesUniform_add_right`, applied to `π ↦ π * σ⁻¹`), and
  `uprob (fun c => b' c = b c) = 1/2` (independence of `b'` from `H`: `uprob_prod_and`
  after the translation; `V*`'s response depends only on `H`, `z`, `r_V*`);
* the **string-level honest prover** samples `π` by Fisher–Yates from `k(n) = 2n + 2⌈log n⌉`
  bits per index (`eff_samplePerm`, an `iterate`), whose distribution is within
  `n²/2^{k}` ≤ `2^{-n}` statistical distance of uniform (`statDist_samplePerm`, new,
  ≈ 150 lines of counting), transported through `distAdv_le_statDist`.

Deviation to record in D8: the honest prover's permutation is only `2^{-n}`-close to
uniform; completeness and soundness are unaffected (soundness is for all provers,
completeness does not need uniformity), and zero knowledge acquires an additive `2^{-n}`.

**Simulator 123.4** (strict PPT, truncated at `n` attempts): `giSim V' := (attempt).iter
… (R := var)` where one attempt draws `b'`, a permutation `π` (Fisher–Yates), fresh coins
`r_V'` for `V'`, computes `H = π • G_{b'}`, runs `V'` once on `H` (the `iter` call), and
keeps the view `(x, z, r_V', H, π)` if `V'`'s answer equals `b'`; after `n` failures the
output is a fixed failure string. Membership: `pptClass.mem_iter`, `mem_seq`, `Eff` of
graph permutation application (`eff_permApply`, an `iterate` over the `n·n` cells with
`unaryTokenSplit` lookups), `eff_samplePerm`, `eff_eq`.

**Theorem 122.3** in the model:

```lean
theorem gi_zk (𝒞 : AdversaryClass) : ZK 𝒞 (giProtocol) giRel giView
-- proved via the statistical statement, for every distinguisher, not only members:
theorem gi_sim_statDist (V' : Strategy) (x y z) (h : giRel.R x y) :
    statDist (pushforward (viewSampler {giProtocol with verifier := V'} x y z))
             (pushforward (simSampler (giSim V') x z)) ≤ 2 * (2 : ℝ)⁻¹ ^ x.length
```

Proof of `gi_sim_statDist`: by Lemma 123.5 each attempt succeeds with probability exactly
`1/2` independently of its output (`uprob_pi_forall` for the `n` fresh attempts gives
failure `2^{-n}`), and **conditioned on success the attempt's view is distributed exactly
as the real view** (the perfect-simulation half of the source's proof: "since `H` is
independent from `b'`, this does not change the output distribution" — formally, the map
`(b', π, r) ↦ (π * σ^{-b'}, r)` is a bijection of the success set onto the real coin space,
`uprob_comp_equiv`); plus the `2^{-n}` from the honest prover's permutation sampling. Then
`gi_zk` is `distAdv_le_statDist` + `negligible_two_pow_neg` (`Negligible.const_mul`), for
every `𝒞` and every `D`. The matching between `giSim`'s `iter` and the typed attempt
sampler is the Chapter-4 matching lemma (≈ 200 lines: `Nat.rec` on attempts vs. "first
success among `n` independent trials").

### 6.5 Scope note on §4.7

`Commitment` (above), Protocol 127.5 and Propositions 127.6/128.8 (3-colouring) use the
same `Protocol`/`ZK` vocabulary with `rounds = 3`, messages of length `|E| · Lc`, and the
hybrid over commitments (`exists_hybrid_gap`). Theorem 124.1 needs a polynomial-time
*string* reduction from an NP-complete language to 3-colouring, which the repository has
only at graph level (`SATtoColorReduction`); it is stated with that reduction as an
explicit `Eff` hypothesis (plan, risks).

## 7. (f) The complete list of closure lemmas and their suppliers

### 7.1 Interface fields of `effPoly` (instantiation obligations for `Eff := PolyTimeComputable`)

| Field | Statement (over `List Bool`) | Supplier | Status |
| --- | --- | --- | --- |
| `comp` | `Eff g → Eff h → Eff (g ∘ h)` | `Complexity.PolyTimeComputable.comp` | exists |
| `id` | `Eff id` | `Complexity.polyTimeComputable_id` | exists |
| `const` | `Eff (fun _ => w)` | `Complexity.polyTimeComputable_const` | exists |
| `pair` | `Eff g → Eff h → Eff (fun x => pairEncode (g x) (h x))` | `PolyTimeComputable.pairEncode` | exists |
| `fst`, `snd` | `Eff pairFstD`, `Eff pairSndD` | `polyTimeComputable_pairFstD/_pairSndD` | exist |
| `ite` | one-bit test and two branches | `polyTimeComputable_ite` (`Build/Wrappers.computesFunInTime_cond`) | exists |
| `append` | `Eff (fun x => g x ++ h x)` | `PolyTimeComputable.append` | exists |
| `unary p` | `Eff (fun x => replicate (p.eval |x|) true)` | `polyTimeComputable_unary`, `_polyUnary` (`const`, `var`, `pow`/normal form), `.append` (`add`); `mul`, `pow2log` via `iterate` (block concatenation / doubling) | 4 of 6 constructors exist; `mul`, `pow2log` derived from `iterate` |
| `lenEq` | `[decide (|fst z| = |snd z|)]` | `polyTimeComputable_lenEq` (and `_lenLe`) | exists |
| `splitUnary` | `pairEncode u r ↦ pairEncode (r.take |u|) (r.drop |u|)` | **new primitive** `Turing.FinTM.computesFunInTime_splitUnary`, linear time | new (§7.3) |
| `iterate R` | `Eff step → Eff emit → Eff (x ↦ concat_{i ≤ R|x|} emit (step^[i] x))` | **new derived** `Complexity.polyTimeComputable_iterate` from `exists_emitLoopTM` + new call/startup modules | new (§7.3) |

Also used by the instance proofs but not fields: `polyTimeComputable_of_linear`,
`PolyTimeComputable.output_length_le` (length bounds for the loop invariant),
`polyTimeComputable_prepend`, `computesFunInTime_appendBit`, `computesFunInTime_lengthBits`,
`computesFunInTime_polyBits` (fuel `Nat.bits (R n)` for the loop combinators),
`computesFunInTime_incFixed` (binary counters), `computesFunInTime_pairValid`,
`computesFunInTime_stripLast`, `unaryTokenSplit`/`computesFunInTime_unaryToken` (Chapter-4
permutation tokens).

### 7.2 Fields of `nupptClass` / `pptClass` (pure closure algebra over `Eff`)

| Field | Instantiation | Ingredients |
| --- | --- | --- |
| `mem_ofFun` | `g` is the member's function after `pairFstD` (drop the empty coin block; drop the advice) | `comp`, `fst`, `snd` |
| `mem_seq` | `g' z := g_B (pairEncode (pairEncode (pairEncode x (padTo q (g_A (pairEncode (pairEncode x α_A) r₁)))) α_B) (r₂.take ℓ_B))` with `r₁, r₂` from `splitUnary` at `unary A.coins` | `comp`, `pair`, `fst`, `snd`, `unary`, `splitUnary`, `append`, `ite` (`padTo` = append `false`s then `take` via `splitUnary`); advice `α' n := pairEncode (α_A n) (α_B (fixed length))` |
| `mem_iter` | `polyTimeComputable_iterate` with `step' s := step (pairEncode s (g_A (pairEncode (pairEncode (padTo q (pairSndD s)) α_A) block)))`, coin blocks peeled by `splitUnary`; `emit` emits `[]` except at the last round (`lenEq` on a unary counter) | `iterate`, `splitUnary`, `unary`, `pair`, `fst`, `snd`, `ite`, `comp` |
| `mem_union` | `polyTimeComputable_ite` on the first input bit, each branch re-pairs its advice | `ite`, `fst`, `snd`, `pair`, `comp` |
| `mem_withAdvice` | advice `pairEncode (α n) (β n)`; the machine re-pairs `pairEncode (pairEncode x (β |x|)) (α (2|x|+2+|β|x||))` | `pair`, `fst`, `snd`, `comp`; `PolyExpr.eval_subst` for the length bookkeeping |
| `mem_coins` (derived) | the coin reader `⟨p, fun _ r => r⟩` is a member | `snd` (it is `pairSndD` of `pairEncode x r`) |

Each row is 30–80 lines; the `pptClass` rows are the `nupptClass` rows with `α := fun _ => []`.

### 7.3 The two new machine-level pieces (exact statements and construction plan)

**N1. `computesFunInTime_splitUnary`** (new primitive, `Build/Primitives.lean` style):

```lean
theorem Turing.FinTM.computesFunInTime_splitUnary :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, r) => pairEncode (r.take u.length) (r.drop u.length)
        | none => [])
      fun n => c * (n + 1)
```

Construction: parse the doubled prefix `u` (as `computesFunInTime_pairFst` does), then copy
`r` to the output while consuming one cell of the copied `u` per bit, emitting the doubled
form; on exhaustion emit the separator and the rest verbatim. Linear, two work tapes.
Everything the reductions do with coin strings ("the next `ℓ` bits") goes through this one
primitive composed with `unary`; without it coin blocks cannot be addressed at all (no
existing primitive takes a prefix of a length given at run time).

**N2. `polyTimeComputable_iterate`** (new derived lemma; the plan's load-bearing item):

```lean
theorem Complexity.polyTimeComputable_iterate {step emit : List Bool → List Bool}
    (R : PolyExpr) (hs : PolyTimeComputable step) (he : PolyTimeComputable emit)
    (hlen : ∃ C c, ∀ x i, i ≤ R.eval x.length → (step^[i] x).length ≤ C * (x.length + 1) ^ c) :
    PolyTimeComputable (fun x => (List.range (R.eval x.length + 1)).flatMap fun i => emit (step^[i] x))
```

(The interface field quantifies the length bound away by requiring it as a hypothesis of
`iterate`; the compiled scratch omits `hlen` — run 2 adds it, since without a bound on the
iterates the per-round budget of `exists_emitLoopTM` cannot be a function of `|x|`.)

Construction plan, from the audited combinators:

1. Fuel: `F` computing `Nat.bits (R.eval |x|)` from `computesFunInTime_polyBits` (for the
   normal form) — for general `PolyExpr` compose `eff_unary` with `computesFunInTime_lengthBits`.
2. Startup: the loop body must reach `Cfg.ofWords anchor (stateWord k (s0 x))` with
   `s0 x = x` (the state word must contain the input, because a call module computes a
   function of its *argument word* only — `exists_installCallTM`'s `f arg` cannot read the
   input tape). **New module `exists_loadInputTM`**: from `initCfg x`, copy the input onto
   work tape 0 and enter `anchor` within `c (|x| + 1)` steps with no earlier anchor visit.
   (≈ 300 lines; the `idTM` of `Composition.lean` is the template, writing to a work tape
   and rewinding instead of emitting.)
3. Round: from `Cfg.ofWords anchor (stateWord k s)` reach
   `{Cfg.ofWords anchor (stateWord k (step s)) with output := emit s}`. **New call variant
   `exists_stepCallTM`** — the "split" finishing mode of the existing `emCallTM`: evaluate
   the machine for `s ↦ pairEncode (emit s) (step s)` (one `PolyTimeComputable` machine by
   `pair`), then replay the first component onto the physical output and install the second
   as the new argument word, erase the capture, restore heads. Same seam discipline and
   coefficient shape as `exists_installCallTM`/`exists_emitCallTM` (`24 + 13 * M.k`), and a
   one-transition return from `exit` to `entry`, so that the round contract's "no
   intermediate anchor visit" is the module's "first positive visit to `exit`" (≈ 400–800
   lines following the two existing modes).
4. Assembly: `exists_emitLoopTM body F anchor Inv step emit s0 R T` with
   `Inv x s := |s| ≤ C (|x|+1)^c` (from `hlen` and `output_length_le`), `T n` the round
   budget `c (T_step(L) + L + L' + 1)` at `L = C (n+1)^c`; the conclusion is the concatenation
   of the `R + 1` chunks — exactly the statement's `flatMap`. Budget arithmetic as in
   `e3_loop_bound` (`Nondeterminism.lean`).

Fallback (plan, risks): if N2's step 3 stalls, `polyTimeComputable_iterate` is the *single*
named admission of the campaign; every theorem that repeats an adversary depends on it and
nothing else is blocked (all other fields are existing lemmas plus N1).

### 7.4 Derived `Eff` lemmas (pure closure algebra, no machines; each 40–120 lines)

| Lemma | Function | From |
| --- | --- | --- |
| `eff_take_unary p`, `eff_drop_unary p` | `x ↦ x.take (p.eval |x|)` / `drop` | `splitUnary`, `unary`, `pair`, `fst`/`snd` |
| `eff_padTo p` | `padTo (p.eval |x|)` | `append`, `unary` (as `false`s via `const`+`iterate` or `polyUnary` with `false`: add `unaryFalse` to §7.1 or map), `eff_take_unary` |
| `eff_eq` | `pairEncode a b ↦ [decide (a = b)]` | `iterate` over bit pairs + `ite`, or `lenEq` + a bitwise `iterate` |
| `eff_xor` | bitwise XOR of two equal-length strings | `iterate`, `splitUnary`, `ite` |
| `eff_majority` | majority bit of a string | `iterate` with a unary counter, `lenEq`/`lenLe` on `1^{2c}` vs `1^n` |
| `eff_blockMap p g` | apply `g` to consecutive `p.eval |x|`-bit blocks, concatenate | `iterate` (emit = `g` of the current block, step = drop a block) |
| `eff_block p i`, `eff_update p` | select / overwrite block `i` (index in unary) | `eff_take/drop`, `append` |
| `eff_unaryMul`, `eff_pow2log` | `1^{a·b}`, `1^{2^{clog(n+1)}}` | `iterate` (concatenate `b` copies; double until `≥ n+1`) |
| `eff_samplePerm`, `eff_permApply` | Chapter 4 permutations | `iterate`, `unaryTokenSplit`, `eff_block` |
| `eff_chunkFind` | first self-delimiting chunk with tag `1` | `iterate` + `ite` (used by view/transcript parsing) |

### 7.5 Probability-side toolkit (no closure; all existing)

`uprob_comp_equiv`, `acceptProb_comp_equiv`, `uprob_fst`, `acceptProb_fst/snd`,
`acceptProb_bind`, `acceptProb_update`, `uprob_update`, `uprob_pi_forall`, `uprob_prod`,
`uprob_prod_and`, `pushesUniform_*`, `half_le_uprob_good`, `exists_hybrid_gap`,
`abs_sub_le_sum_hybrids`, `distAdv_le_statDist`, `uprob_bool_prod`, `uprob_evalLazy`;
`Negligible.{add,mul,mul_pow,const_mul,mono}`, `negligible_two_pow_neg`, `not_negligible_iff`,
`not_negligible_sub`. Equivalences: `Fin.appendEquiv`, `Equiv.arrowCongr`, `Equiv.curry`,
`finProdFinEquiv`, `finFunctionFinEquiv`, `Equiv.boolArrowEquivProd`, `Fin.consEquiv`,
`Equiv.prodAssoc/prodComm`.

## 8. (g) Risks, audit sensitivity, effort

### 8.1 Quantifier shapes to audit (what would make a definition vacuous or too strong)

| Definition | Shape | Trap |
| --- | --- | --- |
| `NUPPT`/`PPT` | `∃ g α a, PolyTimeComputable g ∧ …` with the budget on **all** inputs | if the budget were required only on well-formed inputs, `PolyTimeComputable` could not be used verbatim; if `coins` were an abstract `ℕ → ℕ`, the class would contain machines deciding undecidable unary languages (vacuity of hardness: everything would be "easy"). `PolyExpr` closes this. |
| `StrongOWF 𝒞 f` | `∀ A ∈ 𝒞, Negligible (…)` | **vacuous if `𝒞.Mem` is empty** — guard with `not_strongOWF_id` (§3.2) and `nuppt_ofFun_id`. Too strong if the adversary were denied `1^n` (length-shrinking `f`): it is supplied. |
| `WeakOWF 𝒞 f` | `∃ q, ∀ A ∈ 𝒞, ∃ n₀, ∀ n ≥ n₀` | `∀ A, ∃ q` is a different (weaker) notion; Theorem 35.1 is then unprovable. |
| `Indist 𝒞 X Y` | `∀ D ∈ 𝒞, Negligible` | decoding `Y` at `X.ℓ` silently truncates: state theorems with `X.ℓ = Y.ℓ`. |
| `OracleIndist` | `∀ S ∈ 𝒞, ∀ q, Negligible` | with the budget cut-off, an adversary exceeding `q(n)` queries outputs `false`; since `q` is universally quantified this loses nothing, but a definition quantifying `∃ q` would be too weak. |
| `InteractiveProof` | soundness `∃ ε, ∀ x ∉ L, ∀ P* z` | `∀ x, ∃ ε` would be vacuous (ε could depend on x). Deterministic `P*`: faithful by averaging; randomized `P*` would need a coin-length quantifier. |
| `ZK` | `∀ V* PPT, ∃ S PPT, ∀ D ∈ 𝒞, ∃ ε, ∀ x y z` | `∃ S` after `D` is a weaker ("distinguisher-dependent") notion; strict PPT `S` is a *stronger* requirement than the source's expected PPT (fine: GI is proved with the truncated strict simulator at the cost of `2^{-n}`). |
| `Commitment` | binding `∀ v₀ ≠ v₁ …` | the source's literal text (no `v₀ ≠ v₁`) is unsatisfiable; corrected. |
| generic `∀ 𝒞` | every headline theorem | the instance must be **closed**; otherwise every corollary at `nupptClass` depends on an unproved law. Check with `#print axioms` on the corollaries, not on the generic theorems. |

### 8.2 Deviations introduced by this design (each to be recorded in a docstring)

1. Time measured in the total input length (§1); 2. budget on all inputs (§1); 3. lengths
as `PolyExpr` (§2.1); 4. queries padded to explicit lengths in `seq`/`iter` (§2.3);
5. `decodeFin` padding of outputs (§2.6); 6. the family parameter `n` supplied in unary with
the input (§3.1); 7. `m(n)` rounded to a power of two in Theorem 35.1 (§3.4); 8. ensembles
dyadic (D6) and `D` receives `1^n` (§4.1); 9. oracle machines as next-query strategies with
an explicit query budget and cut-off (§5.1); 10. deterministic unbounded provers (§6.2);
11. strict-PPT simulators and the truncated GI simulator (§6.3–6.4); 12. the honest GI
prover's permutation is `2^{-n}`-close to uniform (§6.4); 13. commitment binding corrected
(§6.3); 14. Lemma 71.6 is the concrete `exists_hybrid_gap` (§4.3).

### 8.3 Risks

* **R1 (highest): `polyTimeComputable_iterate`.** Everything that repeats an adversary
  (35.1, GL, next-bit predictor, GGM simulation, the GI simulator, Fisher–Yates) and even
  `PolyExpr.mul`'s unary computability depends on it. Mitigation: the fallback admission;
  and `PolyExpr` can be restricted to `normal C c` sums if `mul` must be avoided.
* **R2: `splitUnary`.** Small but a genuine machine; without it coin blocks are
  unaddressable. No fallback other than admission.
* **R3: matching lemmas.** Each reuse of a concrete reduction needs a pointwise identity
  between a `seq`/`iter` member and the concrete reduction's structured-coin function
  (`yaoInverter`, `guessInverter`, `multicopyRed`, `ggmBitsDist`, the GI attempt). These are
  pure but fiddly (`Nat.rec` vs `List.foldr`/`finRange`), 100–250 lines each; they are the
  main place where the generic layer "moves" rather than removes work.
* **R4: interface freeze.** A closure use not in §7 (e.g. a reduction needing a callee
  with *variable* query length) would require a new field after the freeze. §7 is
  over-approximated (`union`, `withAdvice`, `pow2log` are included although some routes avoid
  them); the padded-query convention covers every chapter 2–4 use found in the inventory.
* **R5: Chapter 4 efficiency of honest parties** (`eff_permApply`, `eff_samplePerm`,
  commitment-based 3-colouring messages): the largest pure closure-algebra cost; keep these
  as separate named lemmas so that the ZK theorems can close modulo them.
* **R6: uniform indices need powers of two** (Yao's `i`, `mixDist`'s `k`); handled by
  `pow2log` or by advice; an audit may ask why `m(n) ≠ 2 n q(n)` — the docstring explains.
* **R7: two instances.** `pptClass` and `nupptClass` must not be registered as typeclass
  instances; always pass the class explicitly.

### 8.4 Effort (lines, this library's style; machine work in bold)

| Component | Estimate |
| --- | --- |
| `PolyExpr` + `eval_le` + `eff_unary` (given `iterate`) | 250–350 |
| `RandFun`, operations, samplers, bridges, `PPT`/`NUPPT`, sanity lemmas | 450–650 |
| `EffClass`/`AdversaryClass`/`HasAdvice`, `effPoly`, `nupptClass`, `pptClass` (§7.2 rows) | 500–800 |
| **N1 `splitUnary`** | **300–600** |
| **N2 `iterate`: `loadInput` + `stepCall` + assembly** | **1 500–3 000** |
| Derived `Eff` lemmas (§7.4) | 700–1 100 |
| Ch. 2: definitions, 35.2, 35.1 (+ matching), `not_strongOWF_id`, collections/OWP/TDP defs | 900–1 300 |
| Ch. 3: ensembles, 71.5/71.6/73.8, pseudorandomness, PRG expansion, GL asymptotic, oracles, GGM | 1 400–2 200 |
| Ch. 4: model, IP, GI protocol + permutation sampling, Lemma 123.5, Thm 122.3, commitments | 2 000–3 500 |
| Corollaries at `nupptClass`, `Checks.lean`, facades | 200–300 |
| **Total** | **8 200–13 800** |

The interface-specific share (structures, instances, corollaries) is ≈ 1 200–1 750 of
these lines; the same machine and matching work appears in every design.

## 9. Evaluation and recommendations for the plan

**Does the interface reduce work?** Not the machine work and not the matching lemmas;
it removes the duplication of closure proofs for the uniform class that Chapter 4 needs,
and it turns "which machine facts does the campaign depend on" into a closed, auditable
list (§7.1–7.2) instead of a property of each proof. It adds ≈ 1 500 lines of structure and
glue and one more argument to every statement.

**Would an audit accept it?** Yes under three rules: (1) every headline theorem has a
corollary at `nupptClass` whose statement is compared with [PS10] (the generic form is not
the audited artefact); (2) `nupptClass` is closed before the fill of any generic theorem
begins, with `polyTimeComputable_iterate` as the only admission allowed, so that
`#print axioms` on the corollaries exposes exactly that dependency; (3) classes are
explicit arguments (no typeclass), and the non-vacuity theorems `nuppt_ofFun_id`,
`not_strongOWF_id` are in `audits/pass-shelat/Checks.lean`.

**If the panel prefers the direct design**, this document degrades gracefully: §7.2's rows
become lemmas `NUPPT.seq`, `NUPPT.iter`, … about `NUPPT` itself, §7.1 and §7.3 are unchanged,
and the Chapter-4 simulator-efficiency proofs are repeated for `PPT` (≈ 400 extra lines).

**Decisions proposed for the decision log.**
D3/D4 (refined): `RandFun` with `PolyExpr` coins; `PPT`/`NUPPT` as in §2.4 with the time
measured in the whole input and the budget on all inputs. D6 (refined): `Ensemble = (gen, ℓ)`.
D7 (refined): next-query strategies with explicit budgets. D8 (refined): padded
`strategyInput`, `verifierFirst` field, coin lengths as functions of `(|x|, |z|)`, the
`2^{-n}` permutation-sampling deviation. New: D9 — the adversary-class interface with the
field list of §2.5 frozen at skeleton time; D10 — `polyTimeComputable_iterate` is the single
permitted admission of the machine layer.

**File layout (interface variant).**

```
TCSlib/Complexity/Randomized/PolyExpr.lean      PolyExpr, eval, subst, eval_le, eff_unary
TCSlib/Complexity/Randomized/RandFun.lean       RandFun, ofFun/seq/iter/union/withAdvice, PPT, NUPPT, ComputesProb1
TCSlib/Complexity/Randomized/Iterate.lean       splitUnary, loadInput, stepCall, polyTimeComputable_iterate
TCSlib/Complexity/Randomized/EffClosure.lean    derived Eff lemmas of §7.4
TCSlib/Complexity/Randomized/Classes.lean       EffClass, AdversaryClass, HasAdvice, effPoly, pptClass, nupptClass
TCSlib/Cryptography/Asymptotic/Bridges.lean     decodeFin, challengeInput, inverter, distinguisher, coin equivalences
TCSlib/Cryptography/Asymptotic/OneWay.lean      Family, EasyToCompute, OWF definitions, 35.2, 35.1, Checks
TCSlib/Cryptography/Asymptotic/Ensembles.lean   Ensemble, Indist, 71.5, 71.6, 73.8, multicopy
TCSlib/Cryptography/Asymptotic/PRF.lean         OracleStrategy, unfoldTree, OracleEnsemble, OracleIndist, PRF, GGM
TCSlib/Cryptography/ZeroKnowledge/*.lean        as in the plan, over Protocol/Strategy of §6
```

Run-2 order: `PolyExpr` → `RandFun` → `Classes` (with `iterate`, `splitUnary` sorried) →
statements of all chapters in parallel → `Iterate.lean` (machine agent, serial) →
`EffClosure` → fills.

## Appendix: the compiled scratch file (`lake env lean`, only `sorry` warnings)

```lean
import TCSlib.Cryptography.Foundations
import TCSlib.Cryptography.Pseudorandom
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.CircuitComplexity.Advice

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
```
