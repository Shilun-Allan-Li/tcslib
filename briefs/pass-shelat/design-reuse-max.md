# Design (angle REUSE-MAXIMAL): the computational-model layer for Pass–shelat ch. 2–4

Status: run-1 design proposal (2026-10-27). Independent of the other panel designs.
Every signature below was compiled against the current worktree with
`lake env lean /tmp/ps_design.lean` (the full scratch file is reproduced verbatim in
Appendix A; it elaborates with zero errors, the only diagnostics being
`declaration uses 'sorry'` on the theorem stubs). Nothing under `TCSlib/` was touched.

## 0. The angle in one paragraph

Take D3/D4/D6/D7/D8 literally and then push every obligation onto what the library already
proves. A (non-uniform) PPT is **one structure** `Complexity.NUPPT`: a `FinTM Bool` that halts
within `Ct (|z|+1)^ct` on *every* input, plus three explicit polynomials (time, coins, advice)
and the advice function. Its only semantic primitive is `output z` (the output tape when the
budget expires). Everything else — the adversary layout `⟨⟨⟨1^n, y⟩, α_n⟩, r⟩`, the oracle
layout, the interactive layout — is a *pairing convention on top of `output`*. Because `output`
is `PolyTimeComputable` and, conversely, every `PolyTimeComputable` function yields an `NUPPT`
(`NUPPT.ofPolyTime`), **every closure fact for machines is a closure fact for the function class
FP**, i.e. it is discharged by `PolyTimeComputable.comp/.pairEncode/.append`,
`polyTimeComputable_ite/_polyUnary/_pairFstD/_pairSndD/…` (PolyTimePairing.lean) with
`A.polyTimeComputable_output` as a black box. Non-uniform choices (hybrid indices, `1^{m n}`,
unary coin-segment lengths, the good `N`) go into the **advice**, which removes almost all
"compute a polynomial of `n` at run time" machine work. What the library does **not** have —
and what this design isolates as the only genuinely new machine constructions — is
(i) a coin-string splitter (`pairSplitAt`, a small catalog primitive) and (ii) **polynomially
many rounds of a polynomial-time step** (`polyTimeComputable_iterateFind`), which is
`exists_loopFindTM` applied to a loop body assembled from `exists_installCallTM` /
`exists_emitCallTM` modules. Item (ii) is the hardest obligation of the campaign; §7.3 sketches
its machine. With (i)+(ii)+FP-calculus, every reduction of chapters 2–4 (Yao's inverter,
Goldreich–Levin's majority, multicopy/PRG hybrids, GGM's lazy table, the GI simulator loop) is an
instance of a single pattern: *`NUPPT.ofPolyTime` of an FP-derived function*.

Deviations introduced by this design are collected in §8.2; each is recorded where it bites.

## 1. What is reused, by role

| Role in the campaign | Existing declaration (file) | How it is used |
| --- | --- | --- |
| machine, timed run, uniqueness of output | `Turing.FinTM`, `ComputesInTime`, `computesInTime_iff`, `ComputesInTime.output_unique`, `.mono` (TuringMachine/Finite.lean) | `NUPPT.output`, `output_spec`, `output_eq_of_computesInTime` |
| polynomial-time functions, composition | `Complexity.PolyTimeComputable`, `.comp`, `.output_length_le`, `polyTimeComputable_id` (ClassNP/PolyTime.lean) | `NUPPT.polyTimeComputable_output`, `NUPPT.ofPolyTime`; all post/pre-processing |
| pairing calculus | `PolyTimeComputable.pairEncode/.pairMapSnd/.append`, `polyTimeComputable_const/_prepend/_unary/_polyUnary/_pairFstD/_pairSndD/_iterate_pairFstD/_pairConcat/_pairSwap/_ite/_and/_lenLe/_lenEq` (ClassNP/PolyTimePairing.lean) | parsing the layouts `⟨⟨⟨1^n,y⟩,α⟩,r⟩`, re-pairing for sub-adversaries, unary lengths of coin segments |
| timed combinators | `computesFunInTime_comp/_const/_id/_ifEq`, `exists_comp_on_image` (Composition.lean); `computesFunInTime_cond` (Build/Wrappers.lean) | negation of a distinguisher (`ifEq`), branching inside reductions |
| machine catalog | `computesFunInTime_{polyUnary,polyBits,lengthBits,pairEncodeFixed,pairFst,pairSnd,pairValid,pairConcat,pairDup,pairMapSnd,pairLenCheck,stripLast,splitSolve,incFixed,unaryToken,appendBit}` (Build/Primitives.lean) | unary coin-segment lengths (`polyUnary`), loop fuel (`polyBits`), counters (`incFixed`, `appendBit`), parsers |
| bounded loops and clean calls | `exists_loopFindTM`, `exists_loopTM`, `exists_emitLoopTM`, `exists_installCallTM`, `exists_emitCallTM`, `Turing.loop_run`, `stateWord`, `Cfg.ofWords` (Build/Loop.lean, Build/Convention.lean); `capture_run`, `emit_run`, `leftAction/leftCfg_run` (Build/Wrappers.lean, Simulation.lean) | the single new engine `polyTimeComputable_iterateFind` (§7.3) |
| advice pattern | `Turing.FinTM.DecidesWithAdviceInTime`, `Complexity.DTIMEAdvice` (CircuitComplexity/Advice.lean) | the shape `pairEncode x (α |x|)`, "time measured in the parameter", explicit advice length `Ca (n+1)^ca` |
| clocked universal machine (optional) | `Turing.timed_universal`, `exists_codeTM` (Universal.lean, Encoding.lean), `one_work_tape_binary` (Robustness/SingleTape.lean) | only for the optional `NUPPT.ofPartial` (§8.1, R4) |
| uniform probability | `uprob`, `uprob_comp_equiv`, `uprob_prod`, `uprob_mono`, `half_le_uprob_good`, `exists_hybrid_gap`, `abs_sub_le_sum_hybrids` (Foundations/Probability.lean) | all experiments; hybrid lemma; coin re-indexing |
| experiments | `invProb`, `predProb`, `acceptProb`, `distAdv`, `acceptProb_comp_equiv`, `distAdv_le_statDist` (Foundations/Experiments.lean) | the typed adversary views feed these directly |
| negligible functions | `Negligible`, `.add/.mul/.mul_pow/.const_mul/.mono`, `not_negligible_iff`, `negligible_two_pow_neg` (Foundations/Negligible.lean) | every asymptotic definition and every contrapositive |
| reseeding toolkit | `acceptProb_fst/_snd/_bind/_update`, `uprob_eq_of_equiv`, `mixDist`, `distAdv_mixDist_eq` (Pseudorandom/Indistinguishability.lean) | flat-coin ↔ structured-coin transport |
| sunglass / multicopy | `sunglassRed`, `distAdv_sunglassRed`, `distAdv_comp`, `pushSampler`, `copies`, `multicopyRed`, `exists_multicopyRed_ge` | Lemma 71.5, multicopy corollary of Lemma 71.6 |
| amplification | `OneWay.prodFun`, `yaoTry`, `yaoInverter`, `yao_amplification_exp` (OneWayFunctions/Amplification.lean) | Theorem 35.1 |
| Goldreich–Levin | `glPad`, `glBit`, `guessInverter`, `invProb_guessInverter_cubic`, `majority`, `subsetSum` (HardcoreBit/) | Theorem 87.3 (ch. 3.4; same pattern as 35.1) |
| PRG | `prgAdv`, `prgExtBits`, `exists_prgExtBitsRed_ge`, `owpGenBits`, `exists_owpPredictorBits` (Pseudorandom/Generators.lean, GeneratorFromPermutation.lean) | Theorem 79.4, Lemma 80.5, Corollary 81.7 |
| oracle adversaries, PRF, GGM | `QueryTree`, `QueryTree.BoundedBy`, `OracleAdversary`, `oracleDist`, `randomFunction`, `prfAdv`, `evalLazy`, `noteQuery`, `tableDist`, `levelAdv`, `ggmBits`, `exists_ggmBits_dist` (Pseudorandom/Functions/) | Definitions 96.1, 96.2, Theorem 97.3 |
| statistical distance | `statDist`, `distAdv_le_statDist` (InformationTheory/StatisticalDistance.lean, Experiments.lean) | statistical ZK (§6), the GI simulator error |
| NP, P, languages | `Complexity.NP`, `Complexity.P`, `Language Bool`, `MultiTapeTM.indicator` (ClassNP/NP.lean, ClassP/) | witness relations of ch. 4; `L_iso ∈ NP` |

## 2. (a) Probabilistic machines

### 2.1 The structure

```lean
namespace Complexity
open Turing

/-- NUPPT [PS10, Def 26.8, advice formulation]; PPT [PS10, Def 23.4] = empty advice. -/
structure NUPPT where
  M : FinTM Bool
  Ct : ℕ
  ct : ℕ                      -- M halts within Ct (|z|+1)^ct on EVERY input z
  Cr : ℕ
  cr : ℕ                      -- Cr (n+1)^cr coins at parameter n
  Ca : ℕ
  ca : ℕ                      -- Ca (n+1)^ca advice bits at parameter n
  advice : ℕ → List Bool
  advice_length : ∀ n, (advice n).length = Ca * (n + 1) ^ ca
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT
variable (A : NUPPT)
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct
def coinLen (n : ℕ) : ℕ := A.Cr * (n + 1) ^ A.cr
def adviceLen (n : ℕ) : ℕ := A.Ca * (n + 1) ^ A.ca

/-- the output tape when the budget expires (the machine has halted by then) -/
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output
theorem output_spec (z) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length)      -- proved
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound                   -- proved
theorem polyTimeComputable_output : PolyTimeComputable A.output                          -- proved
theorem output_eq_of_computesInTime {z w t} (h : A.M.ComputesInTime z w t) : A.output z = w  -- proved

def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y  -- ⟨1^n, y⟩
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool
/-- the adversary layout: machine input ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩ -/
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=                                      -- untyped coins
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)
def Uniform : Prop := ∀ n, A.advice n = []
def Computes (f : List Bool → List Bool) : Prop := ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)

noncomputable def ofPolyTime {f} (hf : PolyTimeComputable f) (Cr cr Ca ca : ℕ)
    (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length = Ca * (n + 1) ^ ca) : NUPPT     -- Classical.choose on hf
theorem output_ofPolyTime … : (ofPolyTime hf Cr cr Ca ca advice hα).output = f                -- proved
noncomputable def ofPolyTimeUniform {f} (hf : PolyTimeComputable f) (Cr cr : ℕ) : NUPPT
end NUPPT

def PPT : Type 1 := {A : NUPPT // A.Uniform}
end Complexity
```

`runFrom`, `step`, `initCfg` are computable `def`s in `Deterministic.lean`, so `output` is a
plain `def`; only `ofPolyTime` is `noncomputable` (it picks the machine inside the existential).
The four theorems marked *proved* are proved in the scratch file (Appendix A) with
`computesInTime_iff` and `output_unique` only.

### 2.2 Why this shape (and how it maps to D3/D4)

* **The random tape is part of the input** (D3): `runAt` feeds `List.ofFn r`. Worst-case time
  over coins [PS10, Def 23.5] is literal: `halts` holds for every `z`, hence every `r`.
* **Totality on all inputs.** D3 only asks for halting on well-formed `⟨x, r⟩`. Requiring it on
  every `z` makes `output` a total function and `A.output` *literally* a `PolyTimeComputable`
  witness, which is what unlocks the whole FP calculus (`PolyTimeComputable.comp` and friends
  are stated for total functions). The class of adversary *behaviours* on well-formed inputs is
  unchanged: a machine halting within `T(|x|)` on well-formed inputs can be clocked by the
  universal machine (`timed_universal` after `one_work_tape_binary` + `exists_codeTM`) composed
  with `polyBits`/`pairEncodeFixed`, yielding a total machine with the same outputs on
  well-formed inputs and a quadratically larger polynomial. This is the optional lemma
  `NUPPT.ofPartial` (§8.1 R4); no chapter-2–4 theorem needs it. **Deviation to record.**
* **Time measured in the machine-input length**, not in `|x|`: `|⟨⟨⟨1^n,y⟩,α_n⟩,r⟩|` is a
  polynomial in `n + |y|`, so the time classes coincide; the brief's "time in `|x|`" (D4,
  `DecidesWithAdviceInTime`) is recovered up to the polynomial change of variable. Deviation.
* **Advice and coins indexed by the security parameter `n`** (given as `1^n`), not by the
  input length. Def 26.8 writes `A_{|x|}`; in every experiment of the text the input is
  `(1^n, y)` whose length is a strictly increasing function of `n`, so the two indexings are
  interdefinable there. Indexing by `n` is what makes the *interactive* and *oracle* layouts
  (§5, §6) well-typed: there one machine is activated many times on inputs of different
  lengths but must use **one** advice string and **one** random tape per `n`. Deviation.
* **PPT = NUPPT with empty advice** (`Uniform`). `advice n = []` is forced by `Ca = 0`. Honest
  parties, simulators and the verifier are stated with the conjunct `A.Uniform`; the abbreviation
  `PPT` is a subtype for readability only. One structure means one closure calculus.
* **"Computes `f` with probability 1"** [Def 24.6] is `Computes`: equality for *every* coin
  string. For honest algorithms we mostly bypass machines and state "easy to compute" as
  `PolyTimeComputable F` on the string layout (`FunFamily.Easy` below); the two are
  interchangeable via `ofPolyTimeUniform` / `polyTimeComputable_output`. Deviation (deterministic
  evaluator), recorded in the docstrings.

### 2.3 From machine to sampler: `1^n`, typed inputs, decoding

```lean
namespace TCSlib.Cryptography
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool) :=            -- wrong length = failure (D5)
  if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i false   -- pad/truncate (for samplers)

def Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt n (List.ofFn y) r)
def Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool :=
  fun t r => decide (A.runAt n (List.ofFn t) r = [true])
def Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool :=
  fun w r => decide (A.runAt n w r = [true])
def Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool := A.distinguisher n m

noncomputable def invProbOpt {α β ρ} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → Option α) : ℝ :=
  uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1
theorem invProbOpt_le_invProb [Inhabited α] (f) (A) :
    invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default)                       -- proved (uprob_mono)
theorem invProbOpt_some (f) (A : β → ρ → α) : invProbOpt f (fun y r => some (A y r)) = invProb f A  -- proved
end TCSlib.Cryptography
```

* `1^n` is supplied by the layout (`advInput n y = ⟨1^n, y⟩`), never by the experiment's
  caller: `A.inverter n ℓ m y r` *is* `A(1^n, y; r)`. The adversary's coin type is
  `A.Coins n = Fin (Cr (n+1)^cr) → Bool`, a `Fintype`, so `invProbOpt`, `predProb`,
  `acceptProb`, `distAdv` apply verbatim (`ρ := A.Coins n`).
* Inverters: output decoded as an `ℓ`-bit string, wrong length = failure (D5). This is the
  `Option` form; the bridge `invProbOpt_le_invProb` is what feeds hypotheses into the concrete
  theorems (`yao_amplification_exp` wants `invProb`), and `invProbOpt_some` is what reads their
  conclusions back when the machine always emits an exact-length word (every reduction machine
  does, by construction — Yao's `default` is emitted as `0^ℓ` so that the identity with
  `yaoInverter` is exact, see §3.3).
* Distinguishers/predictors: "`D(t) = 1`" is "output `= [true]`" (the library's `DecidesInTime`
  convention). Any machine can be normalised by `computesFunInTime_ifEq`; deviation noted.

## 3. (b) One-way functions and Theorem 35.1

### 3.1 Families indexed by the parameter

Theorem 35.1's `f' : ({0,1}^n)^{m(n)} → …` is *already* a family indexed by `n` with input
length `n·m(n)`, not a function `{0,1}* → {0,1}*` whose parameter is its input length. We take
that as the primitive notion and recover Definitions 26.1/27.3/28.4 as the instance
`inLen = id`:

```lean
structure FunFamily where
  inLen : ℕ → ℕ
  outLen : ℕ → ℕ
  f : ∀ n, (Fin (inLen n) → Bool) → (Fin (outLen n) → Bool)

namespace FunFamily
def Easy (𝓕 : FunFamily) : Prop :=                                 -- [26.1(1), 27.3(1)]
  ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
    ∀ n (x : Fin (𝓕.inLen n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)
def InLenPoly (𝓕 : FunFamily) : Prop := ∃ C c : ℕ, ∀ n, 𝓕.inLen n ≤ C * (n + 1) ^ c
noncomputable def invProbAt (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : ℝ :=
  invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen n) (𝓕.outLen n))

structure StrongOneWay (𝓕 : FunFamily) : Prop where                 -- [PS10, Def 27.3]
  inLenPoly : 𝓕.InLenPoly
  easy : 𝓕.Easy
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n
structure WeakOneWay (𝓕 : FunFamily) : Prop where                   -- [PS10, Def 28.4]
  inLenPoly : 𝓕.InLenPoly
  easy : 𝓕.Easy
  hard : ∃ Cq cq : ℕ, ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀,
    𝓕.invProbAt A n ≤ 1 - 1 / (((Cq : ℝ) + 1) * ((n : ℝ) + 1) ^ cq)
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where              -- [PS10, Def 26.1]
  inLenPoly : 𝓕.InLenPoly
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen n) → Bool),
    uprob (fun r : A.Coins n => ∃ x', A.inverter n (𝓕.inLen n) (𝓕.outLen n) (𝓕.f n x) r = some x' ∧
      𝓕.f n x' = 𝓕.f n x) = 1

def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ := (f (List.replicate n false)).length
def ofString (f : List Bool → List Bool) : FunFamily :=               -- the textbook f : {0,1}* → {0,1}*
  { inLen := id, outLen := strOutLen f, f := fun _ x i => (f (List.ofFn x)).getD i false }
def LengthRegular (f : List Bool → List Bool) : Prop := ∀ x, (f x).length = strOutLen f x.length
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)   -- finProdFinEquiv + Equiv.curry
def prod (𝓕 : FunFamily) (q : ℕ → ℕ) : FunFamily :=                     -- f'_n = (f_n)^{q n} on flat strings
  { inLen := fun n => q n * 𝓕.inLen n, outLen := fun n => q n * 𝓕.outLen n,
    f := fun n x => (blocks (q n) (𝓕.outLen n)).symm (OneWay.prodFun (𝓕.f n) (q n) (blocks (q n) (𝓕.inLen n) x)) }
end FunFamily
```

Quantifier shapes, checked against the text:

* 27.3: "for any adversary A there exists negligible ε such that for any n, Pr ≤ ε(n)" is
  `∀ A, Negligible (fun n => Pr n)` (`Negligible` bounds `|μ n|`, and `Pr ≥ 0`).
* 28.4: "there exists polynomial q such that for any A, for sufficiently large n,
  Pr ≤ 1 − 1/q(n)": `q` is quantified *before* `A`; written as `(Cq+1)(n+1)^cq` so that `q ≥ 1`.
  With a bare `Cq (n+1)^cq` and `Cq = 0`, Lean's `1/0 = 0` would make every family weakly
  one-way (audit-sensitive; see §8.1 R5).
* 26.1: the text gives `A` no `1^n`; we do (D5). Harmless (more power to `A`).
* `InLenPoly` is needed: without it a family with superpolynomial `inLen` is vacuously one-way
  (no NUPPT can even write an inverse). It is a *side condition in a theorem/definition*, not
  a class definition, so the library's rule against abstract bound functions is respected; for
  `ofString f` it is trivial (`inLen = id`).
* The textbook statement for strings is `LengthRegular f ∧ StrongOneWay (ofString f)`, and
  `(ofString f).Easy` follows from `PolyTimeComputable f` via `F := f ∘ pairSndD`
  (`PolyTimeComputable.comp`, `polyTimeComputable_pairSndD`).

### 3.2 Theorem 35.1, exact statement

```lean
/-- [PS10, Theorem 35.1]. `m n = 2^(a + b⌈log₂(n+1)⌉)` is a power of two ≥ 2 n q(n). -/
theorem weak_to_strong {𝓕 : FunFamily} (h : FunFamily.WeakOneWay 𝓕) :
    ∃ a b : ℕ, FunFamily.StrongOneWay (𝓕.prod fun n => 2 ^ (a + b * Nat.clog 2 (n + 1)))

/-- [PS10, Theorem 35.2] in family form (same parameter, two blocks). -/
theorem strong_prod_two {𝓕 : FunFamily} (h : FunFamily.StrongOneWay 𝓕) : FunFamily.StrongOneWay (𝓕.prod fun _ => 2)
```

Why a power of two: `yaoTry` draws the planting position uniformly from `Fin q`. A uniform
element of `Fin q` is a pushforward of uniform **bits** only if `q` is a power of two, and
`invProb_prodFun_le` uses exact uniformity (`sum_uprob_eq_card_mul`). Choosing
`a := 1 + Nat.clog 2 (Cq+1)`, `b := cq + 1` gives `2 n q(n) ≤ m n ≤ 2^{a+b}(n+1)^b`
(`Nat.le_pow_clog`, `2^{clog 2 (n+1)} ≤ 2(n+1)`), so `m` is polynomially bounded and
`inLenPoly` of the product follows. The text's "there exists a polynomial `m`" is satisfied
with an explicit formula; fallback if the auditors prefer a `C(n+1)^c` block count: keep the
position biased (`k+n` bits reduced mod `m n`) and add a `2^{-n}`-perturbation lemma on
`uprob` — more concrete-layer work, no machine work (§8.1 R2).

### 3.3 Proof plan of `weak_to_strong` (every closure lemma named)

Contrapositive, at the level of `not_negligible_iff`.

1. **Unpack.** From `h.hard` get `Cq cq`; set `q n := (Cq+1)(n+1)^cq`, `m n := 2^(a + b·clog…)`
   as above; from `h.easy` get `F` (evaluator of `𝓕`) and from `h.inLenPoly` the bound on
   `inLen`.
2. **`inLenPoly` of the product**: arithmetic (`Nat.le_pow_clog`, `pow_le_pow`).
3. **`easy` of the product.** `F'` on `⟨1^n, x'⟩` with `|x'| = m n · inLen n`: iterate
   "cut the next `inLen n` bits, apply `F ⟨1^n, block⟩`, append" until the remainder is empty.
   Needs: `polyTimeComputable_iterate` (§7.3) with step = FP-composition of
   `polyTimeComputable_pairTakePoly/_pairDropPoly` (derived from the new `pairSplitAt`, §7.2),
   `PolyTimeComputable.pairEncode`, `.append`, and the unary length `1^{inLen n}` computed from
   `1^n`. For `inLen = id` (the textbook case) that is `pairFstD`; in general `Easy` should be
   strengthened by a second machine `Lin 1^n = 1^{inLen n}` (recommended; it is what makes
   `prod` evaluable, and it is trivial for every family in the text). Blocks are then found
   without ever computing `m n`.
4. **Suppose the product is not strong**: `A' : NUPPT` with `¬ Negligible (invProbAt (𝓕.prod m) A')`;
   by `not_negligible_iff` get `c` and infinitely many `n` with `1/n^c ≤ invProbAt … n`.
5. **Concrete product inverter at each `n`.** `B n : (Fin (m n) → Fin (outLen n) → Bool) → A'.Coins n → (Fin (m n) → Fin (inLen n) → Bool)`,
   `B n ys r := blocks … ((A'.inverter n _ _ ((blocks …).symm ys) r).getD default)`.
   `invProbOpt_le_invProb` + `uprob_comp_equiv (blocks …)` give
   `1/n^c ≤ invProb (prodFun (𝓕.f n) (m n)) (B n)` at the good `n`.
6. **The reduction machine `A*` (one NUPPT for all `n`).** Advice at `n`:
   `⟨A'.advice n, ⟨1^{m n}, ⟨1^{T n}, ⟨1^{k n}, ⟨1^{inLen n}, 1^{A'.coinLen n}⟩⟩⟩⟩⟩` where
   `k n := a + b·clog 2 (n+1)` (position bits) and `T n := 2^{a+b+1}(n+1)^{c+b+2}` (iterations,
   `≥ 2 n^{c+1} m n`). Its raw function on `z = ⟨⟨⟨1^n, y⟩, advice⟩, r⟩`: parse (`pairFstD`,
   `pairSndD`, `polyTimeComputable_iterate_pairFstD`); then `polyTimeComputable_iterateFind`
   with state `⟨y, ⟨remaining coins, ⟨counter, result⟩⟩⟩`, `R := T` rounds, step =
   * cut the next segment of length `k n + m n·inLen n + A'.coinLen n` from the coins
     (`pairSplitAt` with the unary lengths from the advice — no polynomial evaluation at run time);
   * split it into position bits, `m n` blocks (`pairSplitAt` again, inner `iterate`), and
     `A'`'s coins;
   * `ys := F` on every block (inner `iterate`, as in step 3) then plant `y` at the position
     (`polyTimeComputable_blockSelect`-style loop with a unary counter compared by `lenEq`);
   * `A'.output ⟨⟨⟨1^n, ys'⟩, A'.advice n⟩, r_A⟩` (`A'.polyTimeComputable_output` composed with
     `PolyTimeComputable.pairEncode` and `polyTimeComputable_pairEncodeFixed`-style constants);
   * extract block `i` of the answer, test `F ⟨1^n, x'⟩ = y` (`polyTimeComputable_pairEq`), store;
   * `acc` = "result nonempty", `out` = result, and on exhaustion emit `0^{inLen n}`
     (so that the machine equals `yaoInverter` *including its `default`*).
   Assemble with `NUPPT.ofPolyTime`; all of this is FP calculus except the two new lemmas.
7. **Functional identity.** With `coinsEquiv n : A*.Coins n ≃ (Fin (T n) → Fin (m n) × (Fin (m n) → Fin (inLen n) → Bool) × A'.Coins n)`
   built from `Fin.appendEquiv`, `blocks`, and `Fin (2^k) ≃ (Fin k → Bool)`, prove
   `A*.inverter n _ _ y r = some (yaoInverter (𝓕.f n) (B n) (T n) y (coinsEquiv n r))`
   (`output_ofPolyTime`, `List.ofFn_fin_append`, `List.take_append`/`drop_append`, and an
   induction relating `iterateFind`'s orbit to `yaoInverter`'s `foldr`). Then
   `invProbAt 𝓕 A* n = invProb (𝓕.f n) (yaoInverter …)` by `invProbOpt_some` and
   `uprob_comp_equiv`.
8. **Apply `yao_amplification_exp`** with `n := (n:ℝ)`, `α' := 1/q(n)`, `q := m n`, `T := T n`,
   `μ₀ := 1/n^c`: `hα₁` (`q ≥ 1`), `hq` (`2 n q(n) ≤ m n`), `hT` (choice of `T`),
   `hμ₀ : 2e^{-n} < 1/n^c` for large `n` (`Real.add_one_le_exp` ⇒ `2^n ≤ e^n`, then
   `tendsto_pow_const_div_const_pow_of_one_lt` as in `negligible_two_pow_neg`), `hμ` from step 5.
   Conclusion: `1 − 1/(2q(n)) − e^{-n} ≤ invProbAt 𝓕 A* n` at infinitely many `n`.
9. **Contradiction** with `h.hard A*` (`∃ n₀, ∀ n ≥ n₀, invProbAt ≤ 1 − 1/q(n)`) at a good
   `n ≥ max n₀ n₁` where `e^{-n} < 1/(2 q(n))`.

Effort: steps 1–2, 8–9 ≈ 150 lines; step 3 ≈ 150 lines on top of `iterate`; steps 6–7 are the
bulk (≈ 500–800 lines) and are the template for every other reduction.

`strong_prod_two` is the same plan without the loop: `B` samples one block, plants `y` in
position 0 or 1 chosen by one coin (power of two, exact), calls `A'`, keeps the planted block;
the concrete part is `uprob_update`/`acceptProb_update` style reseeding (no new concrete
lemma: it is `invProb_prodFun_le`'s planting step, re-proved in 40 lines for `q = 2`).

## 4. (c) Ensembles and computational indistinguishability

```lean
structure Ensemble (ℓ : ℕ → ℕ) where                         -- [PS10, Def 69.3]
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  X : ∀ n, σ n → (Fin (ℓ n) → Bool)

namespace Ensemble
def uniform (ℓ : ℕ → ℕ) : Ensemble ℓ := { σ := fun n => Fin (ℓ n) → Bool, X := fun _ => id }
def Samplable (X : Ensemble ℓ) : Prop :=                      -- D6: dyadic, explicit seed polynomial
  ∃ (Cs cs : ℕ) (e : ∀ n, (Fin (Cs * (n + 1) ^ cs) → Bool) ≃ X.σ n) (S : List Bool → List Bool),
    PolyTimeComputable S ∧ ∀ n s, S (NUPPT.advInput n (List.ofFn s)) = List.ofFn (X.X n (e n s))
def Indist (X Y : Ensemble ℓ) : Prop :=                        -- [PS10, Def 69.4]
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ n))
def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)   -- [PS10, Def 74.1]
def push (M : NUPPT) (ℓ' : ℕ → ℕ) (X : Ensemble ℓ) : Ensemble ℓ' :=   -- {M(X_n)}
  { σ := fun n => X.σ n × M.Coins n, X := fun n z => padFin (ℓ' n) (M.runAt n (List.ofFn (X.X n z.1)) z.2) }
def copies (t : ℕ → ℕ) (X : Ensemble ℓ) : Ensemble (fun n => t n * ℓ n) :=
  { σ := fun n => Fin (t n) → X.σ n, X := fun n s => (FunFamily.blocks (t n) (ℓ n)).symm (TCSlib.Cryptography.copies (t n) (X.X n) s) }
end Ensemble
```

Design notes.

* Seeds are **arbitrary finite types**, exactly as in the concrete layer (`σ`, `τ` in
  `distAdv`). D6's "dyadic with explicit polynomial seeds" is the predicate `Samplable`, not
  part of the structure: the uniform ensemble `U_{ℓ(n)}` needs seeds of the *exact* length
  `ℓ n` (e.g. `2n`, `n+1`), which is not of the form `C(n+1)^c`, and random-function oracles
  (§5) need function-table seeds. Every ensemble the text calls efficiently samplable is
  `Samplable`; the theorems that need sampling (71.5, multicopy, next-bit) take `Samplable` as a
  hypothesis, as the text does ("assume further that we can efficiently sample").
* `ℓ` is a parameter of the type so that `distAdv (X.X n) (Y.X n)` typechecks without casts.
* The distinguisher receives `⟨1^n, t⟩` (Def 75.2's convention, also D5); Def 69.4 gives only
  `t`. Harmless: more information to `D` makes `Indist` stronger, and the n.u. advice already
  depends on `n`. Deviation.
* `push` reads `M`'s output as an `ℓ' n`-bit string by padding/truncation; for the lemma below
  `ℓ'` is required polynomially bounded so that `1^{ℓ' n}` fits in the reduction's advice.

```lean
theorem Ensemble.Indist.push {ℓ ℓ' : ℕ → ℕ} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT)
    (hℓ' : ∃ C c : ℕ, ∀ n, ℓ' n ≤ C * (n + 1) ^ c) : (X.push M ℓ').Indist (Y.push M ℓ')          -- [PS10, Lemma 71.5]
theorem hybrid_lemma {σ γ ρ} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m) (X : ℕ → σ → γ) (D : γ → ρ → Bool) :
    ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i + 1)) D                              -- [PS10, Lemma 71.6], proved
theorem Ensemble.Indist.trans {X Y Z : Ensemble ℓ} (h₁ : X.Indist Y) (h₂ : Y.Indist Z) : X.Indist Z
theorem Ensemble.Indist.copies {X Y : Ensemble ℓ} (h : X.Indist Y) (hX : X.Samplable) (hY : Y.Samplable) (Ct ct : ℕ) :
    (X.copies fun n => Ct * (n + 1) ^ ct).Indist (Y.copies fun n => Ct * (n + 1) ^ ct)
def mixEnsemble (X₀ X₁ : Ensemble ℓ) (n : ℕ) : Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ n) → Bool)
theorem prediction_lemma (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ : ℕ → ℝ)
    (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv (X₀.X n) (X₁.X n) (D.distinguisher n (ℓ n))) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1 / 2 + μ n / 2 <
      uprob fun z : (Bool × (X₀.σ n × X₁.σ n)) × A.Coins n =>
        A.predictor n (ℓ n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1   -- [PS10, Lemma 73.8]
```

(The scratch file states `Indist.push` without `hℓ'`; add it at skeleton time.)

Proof plans and reuse.

* **71.5 (closure).** Given `D` for the pushed pair, build `D'` = "run `M` then `D`" by
  `NUPPT.ofPolyTime` of the FP function `z ↦ D.output ⟨⟨⟨1^n, pad_{ℓ'}(M.output ⟨⟨⟨1^n,t⟩,α_M⟩,r_M⟩)⟩, α_D⟩, r_D⟩`
  with advice `⟨α_M n, ⟨α_D n, 1^{ℓ' n}⟩⟩` and coins `r_M ++ r_D` cut by `pairSplitAt` at
  `1^{M.coinLen n}` (`polyTimeComputable_polyUnary M.Cr M.cr` on `1^n`). Then
  `D'.distinguisher n (ℓ n) = sunglassRed (fun t c => padFin (ℓ' n) (M.runAt n (ofFn t) c)) (D.distinguisher n (ℓ' n))`
  up to the coin re-indexing `D'.Coins n ≃ M.Coins n × D.Coins n` (`Fin.appendEquiv`,
  `acceptProb_comp_equiv`), and `distAdv_sunglassRed` gives *equal* advantages since
  `pushSampler P X = (X.push M ℓ').X n` definitionally. `Negligible` transfers verbatim.
* **71.6 (hybrid).** The per-`n` statement is `exists_hybrid_gap` on
  `i ↦ acceptProb (X i) D` (3 lines, proved in the scratch). `Indist.trans` is
  `Negligible.add` (+ `abs_sub_le`). The polynomially-many-hybrids form is only ever used through
  concrete reductions (multicopy, PRG extension, GGM), each of which has its own
  `exists_…Red_ge` in Garg's layer.
* **Multicopy (`Indist.copies`).** From `D` on the `t n`-fold products: for every `n` choose
  `k_n < t n` maximising `distAdv (X.X n) (Y.X n) (multicopyRed … k (D.distinguisher n _))`
  (`Finset.exists_max_image`; `exists_multicopyRed_ge` shows the maximum is `≥ ε_n / t n`).
  `D'` has advice `⟨α_D n, ⟨bits k_n, ⟨1^{t n}, seed lengths⟩⟩⟩`, samples `k_n` copies of `Y` and
  `t n − k_n − 1` copies of `X` with the `Samplable` evaluators (`iterate` over `t n` positions,
  state = `⟨counter, tuple⟩`), places `z` at position `k_n`, runs `D`. Its sampler equals
  `multicopyRed (X.X n) (Y.X n) (t n) k_n (D.distinguisher n _)` after the coin equivalence
  (all `t n` seed segments are drawn, two ignored — exactly `multicopyRed`'s coin type).
  Then `distAdv_copies n ≤ t n · distAdv_D' n` **for all `n`**, so `Negligible.mul_pow`/`.mono`
  finish — no infinitely-often argument, because the maximising index lives in the advice.
  Garg's `multicopyAvgRed` (uniform index) is *not* used: a uniform `k ← Fin (t n)` is not
  samplable from bits unless `t n` is a power of two.
* **73.8 (prediction).** `A := D` or `D` negated (`computesFunInTime_ifEq [true] [false] [true]`
  post-processing via `NUPPT.exists_comp`). New concrete identity (≈ 40 lines, via
  `uprob_bool_prod` and `uprob_prod`):
  `uprob (A(mix) = b) = 1/2 + (acceptProb X₁ A − acceptProb X₀ A)/2`. Infinitely often one of
  the two signs exceeds `μ n`; pigeonhole on the infinite set gives the predictor.

## 5. (d) Oracle indistinguishability and PRFs

The concrete layer's oracle adversary is a query tree per coin string
(`OracleAdversary ρ I O = ρ → QueryTree I O Bool`). The asymptotic machine is a **next-query
machine**: an `NUPPT` activated once per query on the history of (query, answer) pairs, with
**one** random tape per `n` (hence the `runAt`-indexed-by-`n` layout of §2.2) and an explicit
polynomial query budget. The tree is *built* from the machine by recursion on the budget:

```lean
structure OracleEnsemble (ℓ₁ ℓ₂ : ℕ → ℕ) where                 -- [PS10, Def 96.1]
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  O : ∀ n, σ n → (Fin (ℓ₁ n) → Bool) → (Fin (ℓ₂ n) → Bool)
def OracleEnsemble.random (ℓ₁ ℓ₂) : OracleEnsemble ℓ₁ ℓ₂ := { σ := fun n => (Fin (ℓ₁ n) → Bool) → (Fin (ℓ₂ n) → Bool), O := fun _ => randomFunction _ _ }
def OracleEnsemble.keyed (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁ n) → Bool) → (Fin (ℓ₂ n) → Bool)) : OracleEnsemble ℓ₁ ℓ₂

inductive OracleMove (ℓ₁ : ℕ) | query (x : Fin ℓ₁ → Bool) | ret (b : Bool)
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁        -- ⟨[false], x⟩ = query, [true, b] = verdict
def encodeHist (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool
def buildTree (next : List (…) → OracleMove ℓ₁) : ℕ → List (…) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool

structure OracleNUPPT extends NUPPT where (Cq cq : ℕ)
def OracleNUPPT.queryBound (D) (n) : ℕ := D.Cq * (n + 1) ^ D.cq
def OracleNUPPT.toAdversary (D : OracleNUPPT) (n ℓ₁ ℓ₂ : ℕ) : OracleAdversary (D.toNUPPT.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) :=
  fun r => buildTree (fun hist => decodeOracleMove ℓ₁ (D.toNUPPT.runAt n (encodeHist hist) r)) (D.queryBound n) []
theorem OracleNUPPT.toAdversary_boundedBy (D) (n ℓ₁ ℓ₂) : (D.toAdversary n ℓ₁ ℓ₂).BoundedBy (D.queryBound n)

def OracleEnsemble.Indist (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=   -- [PS10, Def 96.1]
  ∀ D : OracleNUPPT, Negligible fun n => distAdv (O.O n) (O'.O n) (oracleDist (D.toAdversary n (ℓ₁ n) (ℓ₂ n)))
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where   -- [PS10, Def 96.2]
  easy : ∃ E, PolyTimeComputable E ∧ ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  pseudorandom : (OracleEnsemble.keyed F).Indist (OracleEnsemble.random id id)
theorem prfAdv_toAdversary … : distAdv ((keyed F).O n) ((random id id).O n) (oracleDist (D.toAdversary n n n)) = prfAdv (F n) (D.toAdversary n n n) := rfl
```

* The efficiency condition imposed on oracle adversaries is exactly: one NUPPT (polynomial
  time per activation, advice and random tape per `n`) **and** an explicit polynomial query
  budget (after `queryBound n` queries the verdict is forced to `false`). The budget is data
  because a total next-message function could otherwise query forever; in the text the budget
  is implied by the time bound. D7's "driven by an nuPPT with polynomially many queries" is met
  literally; `toAdversary_boundedBy` supplies `QueryTree.BoundedBy` for `ggm_prfAdv_le`.
  Deviation: no oracle tapes (the library's `OracleTM` is a *language* oracle, not a function
  oracle, and is not used).
* The seed type of the random-function ensemble is the function table, as in `randomFunction`;
  this is why `OracleEnsemble.σ` is an arbitrary finite type.
* **Theorem 97.3 (GGM) plan.** PRG `G` length-doubling ⇒ `PRF (ggmBits G)`. For
  `D : OracleNUPPT`, `A := D.toAdversary n n n`, `exists_ggmBits_dist` yields `(i, j)` with
  `distAdv G id (ggmDist …) ≥ prfAdv/(n·q)`; choose a maximising `(i_n, j_n)` for every `n`
  (into the advice). The PRG distinguisher `D'` evaluates `tableDist G (levelAdv G i A) q j` on
  the challenge: `iterate` over at most `q+1` activations of `D` with state
  `⟨history, distinct level-i prefixes with their table entries, remaining coins⟩`; a new
  prefix is answered by the next table entry (`j`-th distinct = challenge, earlier = uniform
  from coins, later = `G` of a fresh seed, i.e. `challengeStream`), then `ggmFrom` along the
  remaining bits (inner `iterate` of `G`, `G` being `PolyTimeComputable` by the PRG's `easy`
  clause). The functional identity with `evalLazy`/`noteQuery` is an induction on the tree
  (≈ 300 lines); machine side is FP + 2 `iterate` instances + a list-lookup loop
  (`polyTimeComputable_pairEq`). Then `Negligible.mul_pow` as for multicopy.

## 6. (e) Chapter 4: strategies, protocols, executions, views

```lean
inductive Move | send (m : List Bool) | halt (out : List Bool)
def decodeMove (w : List Bool) : Move          -- ⟨[true], m⟩ = send m, ⟨[false], o⟩ = halt o, else halt []
abbrev NextMsg := List Bool → List Bool → List Bool → List (List Bool) → Move   -- x z r received
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []

structure Strategy where (next : NextMsg) (Cr cr : ℕ)               -- random tape Cr (|x|+1)^cr
def Strategy.coinLen (S) (n) : ℕ := S.Cr * (n + 1) ^ S.cr
def Strategy.ofNUPPT (A : NUPPT) : Strategy :=                     -- one activation = runAt |x| on ⟨⟨x, z⟩, msgs⟩
  { next := fun x z r hist => decodeMove (A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r), Cr := A.Cr, cr := A.cr }
def Strategy.Efficient (S : Strategy) : Prop := ∃ A : NUPPT, A.Uniform ∧ S = ofNUPPT A

structure View where (x z r : List Bool) (received : List (List Bool))
def View.encode (v : View) : List Bool
structure Execution where (viewA viewB : View) (outA outB : Option (List Bool))
def execAux (nA nB : NextMsg) (x zA zB rA rB : List Bool) : ℕ → Bool → List (List Bool) → List (List Bool) → Execution
def exec (A B : Strategy) (R : ℕ) (x zA zB rA rB : List Bool) : Execution := execAux A.next B.next x zA zB rA rB R true [] []

structure Protocol where (P V : Strategy) (CR cR : ℕ)              -- activation bound CR (|x|+1)^cR
abbrev Protocol.ExecCoins (π) (P' : Strategy) (x) := (Fin (P'.coinLen x.length) → Bool) × (Fin (π.V.coinLen x.length) → Bool)
def Protocol.execWith (π) (P' : Strategy) (x y z) (r : π.ExecCoins P' x) : Execution
def Protocol.accepts (e : Execution) : Prop := e.outB = some [true]
def Protocol.viewV (π) (x y z) (r : π.ExecCoins π.P x) : View                 -- view_V[P(x,y) ↔ V(x,z)]
def Protocol.viewV' (π) (V' : Strategy) (x y z) (r) : View                   -- view_{V*}[P(x,y) ↔ V*(x,z)]

structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where   -- [PS10, Def 116.1]
  efficientV : π.V.Efficient
  complete : ∀ x ∈ L, ∃ y, ∀ z, uprob (fun r : π.ExecCoins π.P x => Protocol.accepts (π.execWith π.P x y z r)) = 1
  sound : ∃ ε, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) z,
    1 - ε x.length < uprob (fun r : π.ExecCoins P' x => ¬ Protocol.accepts (π.execWith P' x [] z r))
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  bounded : ∃ C c, ∀ x y, R x y → y.length ≤ C * (x.length + 1) ^ c
  decidable : ∃ T, PolyTimeComputable (fun z => [T z]) ∧ ∀ x y, T (pairEncode x y) = true ↔ R x y
structure EfficientProverProof (π) (L) (R) : Prop extends InteractiveProof π L where        -- [PS10, Def 119.5]
  efficientP : π.P.Efficient
  completeWitness : ∀ x y, R x y → ∀ z, uprob (fun r => Protocol.accepts (π.execWith π.P x y z r)) = 1

def Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) : List Bool := S.runAt x.length (pairEncode x z) r
def HVZK (π) (R) : Prop :=                                                                   -- [PS10, Def 121.1]
  ∃ S : NUPPT, S.Uniform ∧ ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ x y z, R x y →
    distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def ZK (π) (R) : Prop :=                                                                     -- [PS10, Def 121.2], strict PPT S
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ x y z, R x y →
    distAdv (fun r => (π.viewV' V' x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def StatClose (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop := ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ
theorem distAdv_le_of_statClose … (h : StatClose X Y δ) (D : γ → ρ → Bool) : distAdv X Y D ≤ δ
def StatZK (π) (R) (δ : ℕ → ℝ) : Prop := ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y → StatClose (fun r => (π.viewV' V' x y z r).encode) (S.simulate x z) (δ x.length)
def PerfectZK (π) (R) : Prop := StatZK π R (fun _ => 0)
theorem StatZK.zk (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R

structure Commitment (Com : List Bool → List Bool) (ℓ : ℕ → ℕ) : Prop where               -- [PS10, Def 126.3]
  easy : PolyTimeComputable Com
  ℓ_poly : ∃ C c, ∀ n, ℓ n ≤ C * (n + 1) ^ c
  binding : ∀ n v₀ v₁ r₀ r₁, v₀.length = n → v₁.length = n → r₀.length = ℓ n → r₁.length = ℓ n → v₀ ≠ v₁ →
    Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  hides : ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
            (fun r : Fin (ℓ n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r))) (D.distinguisherL n) ≤ ε n
```

Semantics and deviations.

* **Strategies are next-message functions** of `(x, z, r, received)` (D8). The random tape `r`
  is the *whole* tape, drawn once; `Efficient` means the function is one activation of a
  uniform NUPPT at parameter `|x|` on the layout `⟨⟨x, z⟩, messages⟩`. Time per activation is
  polynomial in `|x| + |z| + |messages|` (modern convention; the text bounds it in `|x|`).
  Malicious provers `P'` are arbitrary strategies (unbounded, any coin polynomial).
* **Executions** alternate activations, `A` first; the protocol ends when the active party
  halts (the text's "a round ends with the active machine halting"); the idle party's output is
  then `none`. The activation bound `rounds` is data of the `Protocol` (the text derives it
  from time complexity). "`out_V = 1`" is `outB = some [true]`; "`out_V = 0`" is read as
  "not accepting" (a never-halting or garbage-emitting verifier rejects). Deviation.
* **Views** are `(x, z, r, received)` exactly as in §4.4; `View.encode` is the distinguisher's
  input. Views live in `List Bool` (infinite type), so statistical closeness is stated in the
  sup-over-test-sets form `StatClose` rather than with `FinDist`; `distAdv_le_of_statClose` is
  the analogue of `distAdv_le_statDist` (average over the distinguisher's coins; each fixed coin
  string is a test set — the proof of `abs_sum_sub_le_statDist` transposed).
* **ZK with strict PPT simulators** (D8). `PerfectZK = StatZK 0`. The sequential repetition
  theorem (§7.2.1 of the text) is out of scope; GI is stated for one iteration (ZK) and for the
  `n`-fold repetition (soundness `2^{-n}`, `Protocol.seqRepeat`), as the text itself does.
* **Commitments.** Source error: Def 126.3's binding clause omits `v₀ ≠ v₁` (as printed it is
  unsatisfiable with `v₀ = v₁, r₀ = r₁`); the design adds it. Theorem 126.4 is
  `exists_owpPredictorBits` + the asymptotic hard-core-bit definition (`Com(b, r) = f(r)‖b⊕h(r)`),
  with hiding by the hybrid `f(r)‖h(r)` vs `f(r)‖¬h(r)`.

### 6.1 Graph isomorphism (expressibility check, compiled)

```lean
abbrev Graph (n : ℕ) := Fin n → Fin n → Bool
def permGraph (G : Graph n) (π : Equiv.Perm (Fin n)) : Graph n := fun u v => G (π.symm u) (π.symm v)
def permOfBits (n k : ℕ) (b : Fin n → Fin k → Bool) : Equiv.Perm (Fin n)     -- Fisher–Yates, index = bits mod (n−i)
theorem gi_sim_H_dist (G₀ G₁ : Graph n) (σ) (hσ : permGraph G₀ σ = G₁) (p : Graph n → Prop) :
    uprob (fun z : Equiv.Perm (Fin n) × Bool => p (permGraph (cond z.2 G₁ G₀) z.1)) =
      uprob (fun π : Equiv.Perm (Fin n) => p (permGraph G₀ π))                       -- [PS10, Lemma 123.5] (i)
theorem gi_sim_half (G₀ G₁ : Graph n) (σ) (hσ) (V : Graph n → ρ → Bool) :
    uprob (fun z : (Equiv.Perm (Fin n) × Bool) × ρ => V (permGraph (cond z.1.2 G₁ G₀) z.1.1) z.2 = z.1.2) = 1 / 2   -- (ii)
```

* `L_iso` is the language of encoded pairs `⟨G₀, G₁⟩` (adjacency matrices, `n²` bits each) with
  `∃ σ, permGraph G₀ σ = G₁`; `R_iso x y := y` encodes such a `σ`; `WitnessRelation` holds
  (`σ` has `n ⌈log n⌉` bits; the check is a polynomial-time loop over edges).
* `giProtocol : Protocol`: `P.next`: on `[]` send `H = permGraph G₀ π`, on `[b]` send `π` or
  `π ∘ σ⁻¹`; `V.next`: on `[H]` send the coin bit `b`, on `[H, γ]` halt with
  `[decide (permGraph G_b γ = H)]`; `rounds = 3`. `giProtocol.seqRepeat vertexCount` is the
  text's "repeat `|G₁|` times". (Source inconsistency: Protocol 120.6 checks `γ(G_b) = H` while
  Prop 120.7's proof writes `π(H) = G₁`; we use the protocol's direction.)
* **Lemma 123.5** is the pair of concrete lemmas above — exact, over the finite type
  `Equiv.Perm (Fin n)` (uniform permutation), proved with `uprob_comp_equiv` for the bijection
  `π ↦ π ∘ σ` and `uprob_prod`.
* **Theorem 122.3** becomes:
  `EfficientProverProofErr giProtocol L_iso R_iso (fun _ => 1/2)` (soundness error `1/2`, one
  iteration), `InteractiveProof (giProtocol.seqRepeat vertexCount) L_iso` (error `2^{-n}`, by a
  round-by-round conditioning on the fresh `b`), and
  `StatZK giProtocol R_iso (fun n => (2⁻¹)^n + 2 δ n)` **for every bit-sampler of permutations
  within statistical distance `δ n` of uniform** used by the honest prover and the simulator.
  The simulator is the text's Algorithm 123.4 truncated at `n` attempts (`iterate` with
  `acc := "b = b'"`): fresh `(b', π)` per attempt, `H := permGraph G_{b'} π`, run `V'`'s
  next-message function (`V'.Efficient` ⇒ `PolyTimeComputable`), output
  `(x, z, r_{V'}, [H, π])` on success, `[]` after `n` failures. Error budget: `2^{-n}` for
  truncation (Lemma 123.5 (ii)), `2 δ n` because Lemma 123.5 (i) only holds for the ideal
  sampler. **Why `δ`:** a uniform permutation of `n ≥ 3` points is not a pushforward of
  finitely many uniform bits, so a PPT prover cannot sample it exactly; `permOfBits n (3n)`
  is `n²/2^{3n}`-close (product of `n` biased marginals, `Equiv.Perm.decomposeFin`), a
  self-contained probability lemma deferred to the fill phase. Hence *statistical* rather than
  perfect ZK — consistent with D8, for an additional reason. Deviation recorded.

## 7. (f) The closure-lemma catalogue

### 7.1 Supplied by the existing library (no new machine)

| Need | Lemma (this design) | Supplier |
| --- | --- | --- |
| machine ⇒ FP | `NUPPT.polyTimeComputable_output` | `ComputesInTime` + `computesInTime_iff` (proved in scratch) |
| FP ⇒ machine | `NUPPT.ofPolyTime`, `output_ofPolyTime` | `Classical.choose` on `PolyTimeComputable`, `output_unique` (proved) |
| post-processing `h ∘ A` | `NUPPT.exists_comp` (post part) | `PolyTimeComputable.comp` |
| pre-processing `A ∘ g`, incl. `1^n ↦ 1^{n'}` for `n' = C(n+1)^c` | `NUPPT.exists_comp` (pre part), `NUPPT.exists_reparam` | `PolyTimeComputable.comp/.pairEncode`, `polyTimeComputable_polyUnary`, `_pairFstD/_pairSndD/_iterate_pairFstD`; coins: `polyUnary Cr cr ∘ polyUnary C c` yields exactly `1^{A.coinLen (n' n)}` |
| pairing two machines' advice, hard-wiring per-`n` constants (`1^{m n}`, hybrid indices, segment lengths) | `NUPPT.exists_withAdvice` | advice is a free function; length arithmetic as `comp_time_bound` (PolyTime.lean) |
| extra coins passed as data; sequential composition `B ∘ A` with split coins (sunglass) | `NUPPT.exists_split`, `NUPPT.exists_seq` | FP calculus + `pairSplitAt` (7.2) + `polyTimeComputable_polyUnary` for the cut length |
| negating a distinguisher, forcing `[true]/[false]` outputs | `NUPPT.exists_comp` with `computesFunInTime_ifEq` | Composition.lean |
| branching on a test | — | `polyTimeComputable_ite`, `computesFunInTime_cond` |
| length tests on pairs (`lenEq`, `lenLe`) — used for unary counters | — | PolyTimePairing.lean |
| loop fuel `Nat.bits (C(n+1)^e)` | — | `computesFunInTime_polyBits` (the `hF` of every loop combinator) |
| binary counters inside loops | — | `computesFunInTime_incFixed`, `computesFunInTime_appendBit` |
| flat coins ↔ structured coins | pure Mathlib | `Fin.appendEquiv`, `finProdFinEquiv`/`Equiv.curry` (`blocks`), `finFunctionFinEquiv`, `List.ofFn_fin_append`, `uprob_comp_equiv`, `acceptProb_comp_equiv/_fst/_snd/_bind/_update` |
| exact statistics of the reductions | — | `yao_amplification_exp`, `invProb_guessInverter_cubic`, `exists_multicopyRed_ge`, `exists_prgExtBitsRed_ge`, `exists_owpPredictorBits`, `exists_ggmBits_dist` |

### 7.2 New small primitive (Build/Primitives style, ≈ 300–500 lines)

```lean
theorem Turing.FinTM.computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
        | none => []) fun n => c * (n + 1)
theorem polyTimeComputable_pairTakePoly (C e) : PolyTimeComputable fun z => (pairSndD z).take (C * ((pairFstD z).length + 1) ^ e)
theorem polyTimeComputable_pairDropPoly (C e) : PolyTimeComputable fun z => (pairSndD z).drop (C * ((pairFstD z).length + 1) ^ e)
```

Construction: the buffered aligned parser of `pairExtractTM` (reads `u` onto a work tape
without emitting), then a copy scan of `b` emitting the doubled prefix bits while the work
head walks across `u`, then the separator `01`, then the remainder verbatim. The derived
`take/dropPoly` are `pairSplitAt ∘ pairEncode (polyUnary C e ∘ pairFstD) pairSndD` then a
projection (`PolyTimeComputable.pairEncode`, `.comp`, `polyTimeComputable_pairFstD/_pairSndD`).
This is the only place where a coin string is cut; every reduction cuts with unary lengths
taken from the advice or from `polyUnary`.

(Head/tail of a word is the instance `u = [true]`; word equality, XOR, majority, block
selection are then derivable through `iterate`, §7.4.)

### 7.3 The hardest obligation: `polyTimeComputable_iterateFind`

```lean
theorem polyTimeComputable_iterateFind {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out) (CR cR Cs cs : ℕ)
    (horbit : ∀ x i, i ≤ CR * (x.length + 1) ^ cR → (g^[i] x).length ≤ Cs * (x.length + 1) ^ cs) :
    PolyTimeComputable fun x =>
      match (List.range (CR * (x.length + 1) ^ cR + 1)).find? (fun i => acc (g^[i] x)) with
      | some i => out (g^[i] x) | none => []
theorem polyTimeComputable_iterate (hg) (CR cR Cs cs) (horbit) : PolyTimeComputable fun x => g^[CR * (x.length + 1) ^ cR] x
```

Why it is the load-bearing lemma: `T` repetitions with fresh coins (Yao), `n(2^k−1)` calls and
`n` majorities (GL), `t n` samples (multicopy), `l` iterations of `G` (PRG extension), `q`
activations of `A` (GGM), `n` attempts (GI simulator), block-wise evaluation of `prod`, and
every "obvious" string function (XOR, equality, majority, counting) are instances. Nothing in
the library iterates a *function-level* contract polynomially many times; the loop combinators
iterate a *body machine* with a seam contract. The lemma is the bridge.

**Machine construction sketch** (instance of `exists_loopFindTM`):

* *Loop data.* `s0 x := x`; `Inv x s := ∃ i ≤ R |x|, s = g^[i] x` (orbit membership —
  trivially preserved by `stepF x s := g s`, and `horbit` bounds `|s|` on it);
  `acceptF x s := acc s`; `out x s := out s`; `R n := CR (n+1)^cR`, fuel machine
  `computesFunInTime_polyBits CR cR` (`hF`); `T n := c·(poly)` from the module budgets below.
* *Modules.* From `hg`, `hacc`, `hout` take machines `Mg`, `Macc`, `Mout` and build
  (i) `C₁ := exists_installCallTM` for `s ↦ pairEncode [acc s] s` (threaded test:
  `PolyTimeComputable.pairEncode (hacc) polyTimeComputable_id`; the verdict is the *first* cell
  of the installed word, `pairEncode [b] s = [b, b, false, true] ++ s`, so no scan is needed to
  read it); (ii) `C₂ := exists_installCallTM` for `w ↦ g (pairSndD w)`; (iii)
  `C₃ := exists_emitCallTM` for `w ↦ out (pairSndD w)`. Each has `entry/exit` with the
  first-visit clean-seam contract and `0 < C.k`.
* *Tape layout.* Pad the three modules to a common tape count `K = max k_i` with idle tapes
  (`leftAction`/`leftCfg_run`, Simulation.lean) so that all share **tape 0** (the loop's
  state word) and restore their scratch at exit (the install/emit contracts promise exactly
  the clean seam `Cfg.ofWords exit (stateWord K ·)`).
* *Body.* `State := C₁.State ⊕ C₂.State ⊕ C₃.State ⊕ Fin 3`; `anchor := inl C₁.entry`.
  Transition table: the three modules' tables on their summands; `C₁.exit` reads tape-0 cell
  0: on `true` go to `C₃.entry`, on `false` go to `C₂.entry`; `C₂.exit` goes to `anchor`
  (one stationary step); `C₃.exit` halts. The first-visit contracts make these re-wirings
  sound (the module's own transition at `exit` is never used before the first visit).
* *`hstart`.* From `initCfg x` copy the input onto tape 0 and rewind (a one-state scan plus
  `rewind_from_any`/`timed_rewind`-style lemma for the work head; ≈ 100 lines), reaching
  `Cfg.ofWords anchor (stateWord K x)` within `2|x| + 3` steps with no earlier anchor visit.
* *`hround`.* From `Cfg.ofWords anchor (stateWord K s)` with `Inv x s`: `C₁` runs to its first
  exit in `t₁ ≤ c₁(T_acc(|s|) + |s| + |s| + 5)` steps and leaves `⟨[acc s], s⟩`; one step
  reads the verdict; if `acc s`: `C₃` runs to its first exit emitting `out s` (the capture
  mode of the loop host records it) and the body halts — the accepting clause; else `C₂` runs
  to its first exit installing `g s`, one step to `anchor` — the advancing clause
  `Cfg.ofWords anchor (stateWord K (g s))`. Anchor exclusion strictly inside the round: the
  only state mapped to `anchor` is `inl C₁.entry`, reached only via the `C₂.exit` step; the
  modules' first-visit clauses exclude earlier visits of their exits, and `C₁`'s run never
  revisits its entry (if `entry = exit` were possible the contract's `0 < t` first-visit clause
  still gives a positive round). Budget: `T n := c (T_g(P n) + T_acc(P n) + T_out(P n) + P n + 8)`
  with `P n := Cs (n+1)^cs` — monotone majorants of the three polynomials, hence of the form
  `c'(n+1)^{c''}`.
* *Conclusion.* `exists_loopFindTM` yields `E` computing the `find?` form within
  `c (T n + 1)(R n + 2)`, which is `C''(n+1)^{c''}`; package as `PolyTimeComputable`.
  `polyTimeComputable_iterate` is the instance with a unary counter threaded in the state
  (`g' ⟨cnt, s⟩ := ⟨cnt ++ [true], g s⟩`, `acc := lenEq cnt 1^{R|x|}` — the counter is
  compared against `polyUnary` of the retained input).

Estimated size 1 000–1 500 lines; difficulty: hard but mechanical, all seam machinery proved
(`loopHost_contracts`, `emCall_first`, `capture_run`). Risk and fallback in §8.1 R1.

### 7.4 Derived string functions (each ≈ 80–200 lines of FP + one `iterate`)

`polyTimeComputable_majority` (unary counters of trues/falses + `lenLe`),
`polyTimeComputable_pairXor` (pop heads via `pairSplitAt [true]`, xor by `ifEq` on two-bit
words, append via `pairConcat`), `polyTimeComputable_pairEq`, `polyTimeComputable_blockSelect`
(walk blocks with a unary counter compared to the binary index by `incFixed`), inner product
mod 2 (`pairXor` + parity = XOR-fold), unary multiplication and `2^{clog}` (for `Lin'` of
`prod` when `m` is a power of two). None needs a new machine.

## 8. (g) Risks, audit sensitivity, effort

### 8.1 Risks

* **R1 (iterate bridge).** If re-wiring the install/emit modules' `exit` states proves awkward
  (e.g. the host-level embedding lemmas for a custom tape injection are missing — only the
  standard `leftCfg/rightCfg` splits are public), the fallback is the route `splitSolve` took:
  a bespoke body built with `capture_run` directly on the three source machines (≈ +500 lines).
  If the lemma cannot be closed in run 4, it is the *single* named admission on which Yao, GL,
  multicopy, GGM and the GI simulator depend — exactly the plan's risk statement; all consumers
  go through it, nothing else is admitted.
* **R2 (power-of-two block count).** `m n = 2^(a+b·clog)` forces the honest evaluator of
  `prod` to be stated with `Lin` (unary input length) and costs two small `iterate` instances;
  fallback: biased position sampling + a `uprob` perturbation lemma (concrete layer, ≈ 150
  lines) with `m n = C(n+1)^c`.
* **R3 (advice/coins indexed by `n`).** Auditors comparing with Def 26.8 (`A_{|x|}`) must accept
  the `1^n`-in-the-input convention; the docstring will show the interdefinability for the
  chapter-2/3 experiments and the necessity for chapter-4/oracle layouts.
* **R4 (totality).** `halts` on all inputs; equivalence of behaviour classes is a
  meta-argument unless `NUPPT.ofPartial` is proved (`timed_universal` + `one_work_tape_binary`
  + `exists_codeTM` + `polyBits` + `pairEncodeFixed`; ≈ 400 lines, optional).
* **R5 (vacuity / over-strength).** Checked shapes: `(Cq+1)` in weak OWF (else vacuous);
  `InLenPoly` (else vacuous for exotic families); `Negligible` on `|μ|` with `∃ n₀` (so
  `1/0^c` at `n = 0` is harmless); `hℓ'` in `Indist.push` (else the reduction cannot pad);
  query budget as data (else trees are infinite); `Commitment.binding` with `v₀ ≠ v₁`
  (else unsatisfiable); soundness quantifies over *all* strategies `P'` (unbounded provers)
  and all `z`; completeness fixes `y` before `z` as in the text. Distinguisher verdict
  `= [true]` is a restriction on *machines*, not on *behaviours* (normalise with `ifEq`).
* **R6 (strict simulators, no sequential-repetition theorem).** GI's ZK is stated for one
  iteration; the repeated protocol only gets soundness. Recorded deviation (D8).
* **R7 (permutation sampling).** Statistical, not perfect, ZK for GI; the closeness lemma for
  `permOfBits` is deferrable (the theorem is parametrised by any `δ`-close sampler).
* **R8 (universes/instances).** `NUPPT : Type 1`, `Ensemble ℓ : Type 1`; `σ n : Type` must stay
  in `Type` (function tables are); `Fintype (Equiv.Perm (Fin n))` and `Fintype (A.Coins n)` are
  found by instance search (compiled).
* **R9 (compile cost).** Asymptotic files import both hierarchies; `lake env lean` on the
  scratch took well under a minute, acceptable.

### 8.2 Deviations to record (docstrings)

totality on all inputs; time in machine-input length; advice/coins indexed by `n`;
deterministic evaluator for "easy"; `1^n` to every adversary (incl. Def 26.1, 69.4);
wrong-length inverter output = failure (D5); verdict `= [true]`; families indexed by `n` with
`inLen`; power-of-two `m` in 35.1; `Samplable` as a hypothesis where the text assumes sampling;
query budget as data, no oracle tapes (D7); activation bound as protocol data; `out_V = 0`
read as "not accepting"; time per activation in total input length; strict PPT simulators,
`StatClose` instead of `FinDist`; statistical ZK for GI with sampler parameter `δ`; Def 126.3
binding repaired; one-iteration ZK for GI.

### 8.3 Effort (lines of Lean, honest)

| Component | Lines | Difficulty |
| --- | --- | --- |
| `Randomized/PPT.lean` (structure, `output`, `runAt`, `ofPolyTime`, `Uniform`, `Computes`) | 250 | easy (half proved already) |
| `Randomized/Closure.lean` (`exists_comp/_reparam/_withAdvice/_split/_seq`) | 400–600 | medium; needs `pairSplitAt` |
| `Build/Primitives` addition `pairSplitAt` (or `Randomized/Primitives.lean`) | 300–500 | medium-hard (machine) |
| `Randomized/Repetition.lean` (`iterateFind`, `iterate`, derived string functions) | 1 200–2 000 | hard (critical path) |
| `Asymptotic/Adversary.lean` (`decodeFin`, `inverter`, `distinguisher`, `invProbOpt`) | 150 | easy (proved) |
| `Asymptotic/OneWay.lean` (defs, 35.2, 35.1) | 900–1 200 | medium-hard (35.1 assembly) |
| `Asymptotic/Ensembles.lean` (defs, 71.5, 71.6, prediction, copies) | 700–900 | medium |
| `Asymptotic/PRF.lean` (defs, GGM) | 800–1 100 | hard (lazy-table identity) |
| `ZeroKnowledge/Interaction.lean`, `InteractiveProofs.lean`, `Defs.lean` | 500–700 | easy-medium |
| `ZeroKnowledge/GraphIsomorphism.lean` (+ZK, Lemma 123.5, simulator) | 1 200–1 600 | hard (encodings, repetition soundness, simulator) |
| `permOfBits` closeness lemma | 300–500 | medium, deferrable |
| `ZeroKnowledge/Commitment.lean` (defs, 126.4) | 300–400 | medium (given asymptotic hard-core bit) |

Critical path: `pairSplitAt` → `iterateFind` → (OneWay 35.1, Ensembles.copies, PRF GGM, GI
simulator) in parallel.

## 9. Module layout and ownership (proposal, consistent with the plan)

```
TCSlib/Complexity/Randomized.lean                 facade (register in TCSlib/ComputationalModels.lean)
TCSlib/Complexity/Randomized/PPT.lean             NUPPT, output, runAt/runAtL, Uniform, Computes, ofPolyTime, PPT
TCSlib/Complexity/Randomized/Primitives.lean      pairSplitAt (+ take/dropPoly)   [or appended to Build/Primitives by the integrator]
TCSlib/Complexity/Randomized/Closure.lean         exists_comp, exists_reparam, exists_withAdvice, exists_split, exists_seq
TCSlib/Complexity/Randomized/Repetition.lean      iterateFind, iterate, majority, pairXor, pairEq, blockSelect
TCSlib/Cryptography/Asymptotic/Adversary.lean     advInput re-export, decodeFin, padFin, inverter, distinguisher(L), predictor, invProbOpt
TCSlib/Cryptography/Asymptotic/OneWay.lean        FunFamily, Easy, Strong/Weak/WorstCaseOneWay, ofString, prod, weak_to_strong, strong_prod_two
TCSlib/Cryptography/Asymptotic/Ensembles.lean     Ensemble, uniform, Samplable, Indist, Pseudorandom, push, copies, 71.5, 71.6, 73.8
TCSlib/Cryptography/Asymptotic/PRF.lean           OracleEnsemble, OracleNUPPT, buildTree, OracleEnsemble.Indist, PRF, 97.3
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean   Move, Strategy, View, Execution, exec, Protocol, viewV/viewV'
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean  InteractiveProof(Err), WitnessRelation, EfficientProverProof
TCSlib/Cryptography/ZeroKnowledge/Defs.lean       HVZK, ZK, StatClose, StatZK, PerfectZK
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean / GraphIsomorphismZK.lean / Commitment.lean
```

Statement freeze candidates (to go into the plan verbatim): everything in §2.1, §2.3, §3.1,
§3.2, §4, §5, §6 above — all compiled in Appendix A.

## Appendix A. The compiled scratch file (`lake env lean /tmp/ps_design.lean`: 0 errors)

```lean
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.CircuitComplexity.Advice
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.OneWayFunctions.Amplification
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import TCSlib.Cryptography.Pseudorandom.Functions.Defs
import TCSlib.InformationTheory.StatisticalDistance
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! # Scratch: proposed signatures for the Pass–shelat computational-model layer (design run) -/

namespace Complexity

open Turing

/-! ## (a) Randomized machines: one structure, uniform = empty advice -/

/-- A non-uniform probabilistic polynomial-time machine [PS10, Definition 26.8, advice
formulation]: a finite binary machine `M` that halts on **every** input `z` within
`Ct (|z| + 1)^ct` steps, together with the explicit polynomial `Cr (n + 1)^cr` giving the
length of its uniform coin string at security parameter `n`, and an advice string `advice n`
of explicit polynomial length `Ca (n + 1)^ca` per parameter. A PPT [PS10, Definition 23.4]
is the case `advice n = []` (`NUPPT.Uniform`). The machine is run on the self-delimiting
pair `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`, so the random tape is part of the input and the running
time is bounded for every coin string [PS10, Definition 23.5]. -/
structure NUPPT where
  /-- the machine -/
  M : FinTM Bool
  /-- time bound coefficient and degree: `M` halts within `Ct (|z|+1)^ct` on every input `z` -/
  Ct : ℕ
  ct : ℕ
  /-- coin length coefficient and degree: `Cr (n+1)^cr` coins at parameter `n` -/
  Cr : ℕ
  cr : ℕ
  /-- advice length coefficient and degree -/
  Ca : ℕ
  ca : ℕ
  /-- the advice string at each parameter -/
  advice : ℕ → List Bool
  advice_length : ∀ n, (advice n).length = Ca * (n + 1) ^ ca
  /-- worst-case halting on every input -/
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT

variable (A : NUPPT)

/-- The time budget on a machine input of length `m`. -/
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct

/-- The number of coins at security parameter `n`. -/
def coinLen (n : ℕ) : ℕ := A.Cr * (n + 1) ^ A.cr

/-- The advice length at parameter `n`. -/
def adviceLen (n : ℕ) : ℕ := A.Ca * (n + 1) ^ A.ca

/-- The output of the machine on a raw input `z`: the content of the output tape when the
time budget expires (by `halts` the machine has halted by then). -/
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output

/-- `output` is the completed output of the machine within its budget. -/
theorem output_spec (z : List Bool) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length) := by
  obtain ⟨out, h⟩ := A.halts z
  obtain ⟨hs, -⟩ := (FinTM.computesInTime_iff _ _ _ _).mp h
  exact (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩

/-- The machine computes `output` within its budget on every input. -/
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound :=
  fun z => A.output_spec z

/-- The raw input/output function of a (non-uniform) PPT is polynomial-time computable. -/
theorem polyTimeComputable_output : PolyTimeComputable A.output :=
  ⟨A.M, A.Ct, A.ct, A.computesFunInTime⟩

/-- Any other completed output of the machine agrees with `output`. -/
theorem output_eq_of_computesInTime {z w : List Bool} {t : ℕ} (h : A.M.ComputesInTime z w t) :
    A.output z = w :=
  (A.output_spec z).output_unique h

/-- The input word of an adversary at security parameter `n` on argument `y`: `⟨1^n, y⟩`.
[PS10, Definition 27.3], the input `(1^n, y)`. -/
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y

theorem length_advInput (n : ℕ) (y : List Bool) : (advInput n y).length = 2 * n + 2 + y.length := by
  simp [advInput, length_pairEncode]

/-- The coin type of `A` at parameter `n`. -/
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool

/-- Run `A` at security parameter `n` on the argument `y` with coins `r` (the machine input is
`⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`). -/
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))

/-- Untyped variant: the coin string is any list (used by the interactive layouts). -/
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)

theorem runAt_eq (n : ℕ) (y : List Bool) (r : A.Coins n) : A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl

/-- A uniform machine: empty advice (a PPT, [PS10, Definition 23.4]). -/
def Uniform : Prop := ∀ n, A.advice n = []

/-- `A` computes `f` with probability one [PS10, Definition 24.6]: on every parameter, argument
and coin string the output is `f ⟨1^n, y⟩`. -/
def Computes (f : List Bool → List Bool) : Prop :=
  ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)

/-- The machine of a polynomial-time computable function, as a non-uniform PPT with the
given coin and advice polynomials (noncomputable: the machine is chosen from the existential). -/
noncomputable def ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f) (Cr cr Ca ca : ℕ)
    (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length = Ca * (n + 1) ^ ca) : NUPPT where
  M := Classical.choose hf
  Ct := Classical.choose (Classical.choose_spec hf)
  ct := Classical.choose (Classical.choose_spec (Classical.choose_spec hf))
  Cr := Cr
  cr := cr
  Ca := Ca
  ca := ca
  advice := advice
  advice_length := hα
  halts := fun z => ⟨f z, Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hf)) z⟩

/-- The machine built from `hf` outputs `f`. -/
theorem output_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f) (Cr cr Ca ca : ℕ)
    (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length = Ca * (n + 1) ^ ca) :
    (ofPolyTime hf Cr cr Ca ca advice hα).output = f := by
  funext z
  exact (ofPolyTime hf Cr cr Ca ca advice hα).output_eq_of_computesInTime
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hf)) z)

/-- A uniform PPT from a polynomial-time function: empty advice. -/
noncomputable def ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f) (Cr cr : ℕ) : NUPPT :=
  ofPolyTime hf Cr cr 0 0 (fun _ => []) (fun _ => by simp)

theorem ofPolyTimeUniform_uniform {f : List Bool → List Bool} (hf : PolyTimeComputable f) (Cr cr : ℕ) :
    (ofPolyTimeUniform hf Cr cr).Uniform := fun _ => rfl

end NUPPT

/-- Probabilistic polynomial-time machines [PS10, Definition 23.4]: non-uniform PPTs with
empty advice. -/
def PPT : Type 1 := {A : NUPPT // A.Uniform}

/-! ## (f) The closure lemmas the chapter 2–4 theorems consume (statements) -/

namespace Turing.FinTM

/-- NEW catalog primitive: split the payload of a pair at the length of its head component:
`⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩`; malformed inputs yield `[]`. With `u := 1^{C(|a|+1)^e}`
produced by `computesFunInTime_polyUnary`, this is how a reduction cuts its uniform coin
string into the segments for its sub-adversary and its own fresh samples. -/
theorem computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
          | none => [])
        fun n => c * (n + 1) := by
  sorry

end Turing.FinTM

/-- Derived: taking the first `C (|a|+1)^e` bits of the payload of `⟨a, b⟩` is polynomial-time
(pair `⟨1^{C(|a|+1)^e}, b⟩` by `polyTimeComputable_polyUnary ∘ pairFstD` and `pairSndD`, then
split, then project). -/
theorem polyTimeComputable_pairTakePoly (C e : ℕ) :
    PolyTimeComputable fun z => (pairSndD z).take (C * ((pairFstD z).length + 1) ^ e) := by
  sorry

theorem polyTimeComputable_pairDropPoly (C e : ℕ) :
    PolyTimeComputable fun z => (pairSndD z).drop (C * ((pairFstD z).length + 1) ^ e) := by
  sorry

/-- NEW (the hardest closure lemma): polynomially many rounds of a polynomial-time step with a
polynomially bounded orbit. The machine iterates `g` on the input `x` for at most `R |x|`
rounds, stopping at the first orbit point accepted by `acc` and emitting `out` of it (`[]` on
exhaustion). This is `Turing.FinTM.exists_loopFindTM` applied to a loop body assembled
from the clean-call modules of `exists_installCallTM` / `exists_emitCallTM` for `g`, the
threaded test `s ↦ ⟨[acc s], s⟩`, and `out`. -/
theorem polyTimeComputable_iterateFind {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    (CR cR Cs cs : ℕ)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ CR * (x.length + 1) ^ cR →
      (g^[i] x).length ≤ Cs * (x.length + 1) ^ cs) :
    PolyTimeComputable fun x =>
      match (List.range (CR * (x.length + 1) ^ cR + 1)).find? (fun i => acc (g^[i] x)) with
      | some i => out (g^[i] x)
      | none => [] := by
  sorry

/-- Derived: a fixed polynomial number of rounds (a unary round counter is threaded through the
state and `acc` tests it against `1^{R|x|}`). -/
theorem polyTimeComputable_iterate {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    (CR cR Cs cs : ℕ)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ CR * (x.length + 1) ^ cR →
      (g^[i] x).length ≤ Cs * (x.length + 1) ^ cs) :
    PolyTimeComputable fun x => g^[CR * (x.length + 1) ^ cR] x := by
  sorry

/-- Derived from `polyTimeComputable_iterate`: the majority bit of a word. -/
theorem polyTimeComputable_majority :
    PolyTimeComputable fun w => [decide (w.length < 2 * w.count true)] := by
  sorry

/-- Derived: bitwise XOR of the two components of a pair (equal lengths assumed by the users). -/
theorem polyTimeComputable_pairXor :
    PolyTimeComputable fun z => List.zipWith xor (pairFstD z) (pairSndD z) := by
  sorry

/-- Derived: equality test of the two components of a pair. -/
theorem polyTimeComputable_pairEq :
    PolyTimeComputable fun z => [decide (pairFstD z = pairSndD z)] := by
  sorry

/-- Derived: the `k`-th block of length `b` of the payload, the block index `k` given in
binary as the head component (`⟨bits k, w⟩`). -/
theorem polyTimeComputable_blockSelect (b : ℕ) :
    PolyTimeComputable fun z =>
      (pairSndD z).drop (Nat.ofBits (fun i : Fin (pairFstD z).length => (pairFstD z)[i]) * b) |>.take b := by
  sorry

/-- Closure of NUPPTs under post-processing by a polynomial-time map and pre-processing by
another: the composite has the advice of `A` and the same coins. -/
theorem NUPPT.exists_comp (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.Cr = A.Cr ∧ B.cr = A.cr ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r) := by
  sorry

end Complexity

/-! ## (b) One-way functions, asymptotic layer -/

namespace TCSlib.Cryptography

open Complexity Turing

/-- Decode a word as an `ℓ`-bit string; a word of the wrong length is a failure. -/
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool) :=
  if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none

/-- `A` as an inverter at parameter `n`: given an `m`-bit image, output an `ℓ`-bit preimage
candidate (or fail). -/
def _root_.Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt n (List.ofFn y) r)

/-- `A` as a distinguisher at parameter `n` on `m`-bit samples: accepts iff it outputs `[true]`. -/
def _root_.Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool :=
  fun t r => decide (A.runAt n (List.ofFn t) r = [true])

/-- `A` as a distinguisher of arbitrary words (views, ciphertexts, …). -/
def _root_.Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool :=
  fun w r => decide (A.runAt n w r = [true])

/-- `A` as a bit predictor at parameter `n` on `m`-bit inputs. -/
def _root_.Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool :=
  A.distinguisher n m

/-- Inversion probability for inverters that may fail (wrong-length output): the probability
over uniform `x` and coins that the output is `some x'` with `f x' = f x`. -/
noncomputable def invProbOpt {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : ℝ :=
  uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1

/-- Bridge to the concrete layer: failure counted as a default answer can only help. -/
theorem invProbOpt_le_invProb {α β ρ : Type*} [Fintype α] [Fintype ρ] [Inhabited α] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default) := by
  refine uprob_mono ?_
  rintro ⟨x, r⟩ ⟨x', hx', hf⟩
  simp [hx', hf]

/-- A total inverter is an `Option`-inverter that never fails. -/
theorem invProbOpt_some {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → α) :
    invProbOpt f (fun y r => some (A y r)) = invProb f A := by
  unfold invProbOpt invProb
  congr 1
  funext z
  simp

/-- A family of functions indexed by the security parameter, with explicit input and output
lengths: `f n : {0,1}^{inLen n} → {0,1}^{outLen n}`. The textbook `f : {0,1}* → {0,1}*`
is `FunFamily.ofString`; the direct product of [PS10, Theorem 35.1] is `FunFamily.prod`. -/
structure FunFamily where
  inLen : ℕ → ℕ
  outLen : ℕ → ℕ
  f : ∀ n, (Fin (inLen n) → Bool) → (Fin (outLen n) → Bool)

namespace FunFamily

/-- Easy to compute [PS10, Definitions 26.1(1), 27.3(1)]: a polynomial-time string function
computes `f n x` from `⟨1^n, x⟩`. (Deviation: a deterministic polynomial-time machine; a
PPT computing `f` with probability one, [PS10, Definition 24.6], is equivalent.) -/
def Easy (𝓕 : FunFamily) : Prop :=
  ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
    ∀ n (x : Fin (𝓕.inLen n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)

/-- The input lengths are polynomially bounded (the text's `x ← {0,1}^n`); without it a
family with superpolynomial input length is vacuously one-way. -/
def InLenPoly (𝓕 : FunFamily) : Prop := ∃ C c : ℕ, ∀ n, 𝓕.inLen n ≤ C * (n + 1) ^ c

/-- The success probability of `A` at inverting `f n` on a uniform input with uniform coins:
`Pr[x ← {0,1}^{inLen n}; y ← f(x) : f(A(1^n, y)) = y]`, with the output of `A` read as an
`inLen n`-bit string (Deviation: wrong length counts as failure). -/
noncomputable def invProbAt (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : ℝ :=
  invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen n) (𝓕.outLen n))

/-- Strong one-way function [PS10, Definition 27.3]. -/
structure StrongOneWay (𝓕 : FunFamily) : Prop where
  inLenPoly : 𝓕.InLenPoly
  easy : 𝓕.Easy
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n

/-- Weak one-way function [PS10, Definition 28.4]: some polynomial `q(n) = (Cq+1)(n+1)^cq`
bounds every adversary's success by `1 - 1/q(n)` for all large `n`. (`Cq + 1` keeps `q ≥ 1`;
with `q = 0` Lean's `1/0 = 0` would make the bound vacuous.) -/
structure WeakOneWay (𝓕 : FunFamily) : Prop where
  inLenPoly : 𝓕.InLenPoly
  easy : 𝓕.Easy
  hard : ∃ Cq cq : ℕ, ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀,
    𝓕.invProbAt A n ≤ 1 - 1 / (((Cq : ℝ) + 1) * ((n : ℝ) + 1) ^ cq)

/-- Worst-case one-way function [PS10, Definition 26.1]: no adversary inverts every input with
probability one. -/
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where
  inLenPoly : 𝓕.InLenPoly
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen n) → Bool),
    uprob (fun r : A.Coins n => ∃ x', A.inverter n (𝓕.inLen n) (𝓕.outLen n) (𝓕.f n x) r = some x' ∧
      𝓕.f n x' = 𝓕.f n x) = 1

/-- The output length of a string function on inputs of length `n` (read off the all-zero
input; meaningful under `LengthRegular`). -/
def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ := (f (List.replicate n false)).length

/-- The textbook function `f : {0,1}* → {0,1}*` as a family: parameter = input length. -/
def ofString (f : List Bool → List Bool) : FunFamily where
  inLen := id
  outLen := strOutLen f
  f _ x i := (f (List.ofFn x)).getD i false

/-- Length regularity: inputs of equal length have outputs of equal length. -/
def LengthRegular (f : List Bool → List Bool) : Prop := ∀ x, (f x).length = strOutLen f x.length

/-- Blocks: `(Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)`. -/
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- The direct product family `f'_n (x_1, …, x_{q n}) = (f_n x_1, …, f_n x_{q n})` of
[PS10, Theorem 35.1], on flat strings of length `q n * inLen n`. -/
def prod (𝓕 : FunFamily) (q : ℕ → ℕ) : FunFamily where
  inLen n := q n * 𝓕.inLen n
  outLen n := q n * 𝓕.outLen n
  f n x := (blocks (q n) (𝓕.outLen n)).symm
    (TCSlib.Cryptography.OneWay.prodFun (𝓕.f n) (q n) (blocks (q n) (𝓕.inLen n) x))

end FunFamily

/-- **Hardness amplification** [PS10, Theorem 35.1]: for a weak one-way family there is a
polynomial number of copies `m n = 2^(a + b ⌈log₂(n+1)⌉)` (a power of two so that a uniform
position in `[m n]` is a uniform bit string; `m n ≥ 2 n q(n)`) such that the direct product is
strongly one-way. -/
theorem weak_to_strong {𝓕 : FunFamily} (h : FunFamily.WeakOneWay 𝓕) :
    ∃ a b : ℕ, FunFamily.StrongOneWay (𝓕.prod fun n => 2 ^ (a + b * Nat.clog 2 (n + 1))) := by
  sorry

/-- [PS10, Theorem 35.2]: two copies of a strong one-way function. -/
theorem strong_prod_two {𝓕 : FunFamily} (h : FunFamily.StrongOneWay 𝓕) :
    FunFamily.StrongOneWay (𝓕.prod fun _ => 2) := by
  sorry

/-! ## (c) Ensembles and computational indistinguishability -/

/-- An ensemble [PS10, Definition 69.3]: at each `n` a sampler from a finite seed type into
strings of length `ℓ n`. Efficiently samplable ensembles have bit seeds of explicit polynomial
length (`Samplable`); the uniform ensemble and random-function ensembles use other seed types. -/
structure Ensemble (ℓ : ℕ → ℕ) where
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  X : ∀ n, σ n → (Fin (ℓ n) → Bool)

attribute [instance] Ensemble.fintype

namespace Ensemble

variable {ℓ : ℕ → ℕ}

/-- The uniform ensemble `{U_{ℓ(n)}}`. -/
def uniform (ℓ : ℕ → ℕ) : Ensemble ℓ where
  σ n := Fin (ℓ n) → Bool
  X _ := id

/-- Efficiently samplable: bit seeds of explicit polynomial length and a polynomial-time
sampler `S ⟨1^n, s⟩ = X n s`. -/
def Samplable (X : Ensemble ℓ) : Prop :=
  ∃ (Cs cs : ℕ) (e : ∀ n, (Fin (Cs * (n + 1) ^ cs) → Bool) ≃ X.σ n) (S : List Bool → List Bool),
    PolyTimeComputable S ∧ ∀ n s, S (NUPPT.advInput n (List.ofFn s)) = List.ofFn (X.X n (e n s))

/-- Computational indistinguishability [PS10, Definition 69.4]: every non-uniform PPT
distinguisher, given `1^n` and a sample, has negligible advantage. -/
def Indist (X Y : Ensemble ℓ) : Prop :=
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ n))

/-- Pseudorandom ensemble [PS10, Definition 74.1]. -/
def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)

/-- Pad or truncate a word to `ℓ` bits. -/
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i false

/-- The image ensemble `{M(X_n)}` under a (non-uniform) PPT `M` [PS10, Lemma 71.5], with
`M`'s output read as an `ℓ' n`-bit string. -/
def push (M : NUPPT) (ℓ' : ℕ → ℕ) (X : Ensemble ℓ) : Ensemble ℓ' where
  σ n := X.σ n × M.Coins n
  X n z := padFin (ℓ' n) (M.runAt n (List.ofFn (X.X n z.1)) z.2)

/-- `t n` independent copies [Gar26, Lemma 3.3]. -/
def copies (t : ℕ → ℕ) (X : Ensemble ℓ) : Ensemble (fun n => t n * ℓ n) where
  σ n := Fin (t n) → X.σ n
  X n s := (FunFamily.blocks (t n) (ℓ n)).symm (TCSlib.Cryptography.copies (t n) (X.X n) s)

end Ensemble

/-- Closure under efficient operations [PS10, Lemma 71.5]. -/
theorem Ensemble.Indist.push {ℓ ℓ' : ℕ → ℕ} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT) :
    (X.push M ℓ').Indist (Y.push M ℓ') := by
  sorry

/-- The hybrid lemma [PS10, Lemma 71.6], at one parameter: if `D` distinguishes `X 0` from
`X m` with advantage `ε` then it distinguishes some neighbours with advantage `≥ ε / m`.
(`exists_hybrid_gap` applied to the acceptance probabilities.) -/
theorem hybrid_lemma {σ γ ρ : Type*} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m)
    (X : ℕ → σ → γ) (D : γ → ρ → Bool) :
    ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i + 1)) D := by
  obtain ⟨i, hi, h⟩ := exists_hybrid_gap (fun i => acceptProb (X i) D) hm
  exact ⟨i, hi, h⟩

/-- Transitivity [PS10, Lemma 71.6, m = 3]. -/
theorem Ensemble.Indist.trans {ℓ : ℕ → ℕ} {X Y Z : Ensemble ℓ} (h₁ : X.Indist Y) (h₂ : Y.Indist Z) :
    X.Indist Z := by
  sorry

/-- Polynomially many copies [Gar26, Lemma 3.3; PS10, Lemma 71.6 applied to the multicopy
hybrids]: the hybrid index is hard-wired in the advice of the reduction. -/
theorem Ensemble.Indist.copies {ℓ : ℕ → ℕ} {X Y : Ensemble ℓ} (h : X.Indist Y) (Ct ct : ℕ) :
    (X.copies fun n => Ct * (n + 1) ^ ct).Indist (Y.copies fun n => Ct * (n + 1) ^ ct) := by
  sorry

/-- The sampler `b ← {0,1}; t ← X^b` with both seeds drawn (the unused one ignored). -/
def mixEnsemble {ℓ : ℕ → ℕ} (X₀ X₁ : Ensemble ℓ) (n : ℕ) :
    Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ n) → Bool) :=
  fun z => (z.1, if z.1 then X₁.X n z.2.2 else X₀.X n z.2.1)

/-- The prediction lemma [PS10, Lemma 73.8]: a distinguisher with advantage `μ n` infinitely
often yields a predictor of the bit `b` with success `1/2 + μ n / 2` infinitely often (the
predictor is `D` or its negation; which one is a single non-uniform choice). -/
theorem prediction_lemma {ℓ : ℕ → ℕ} (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ : ℕ → ℝ)
    (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv (X₀.X n) (X₁.X n) (D.distinguisher n (ℓ n))) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1 / 2 + μ n / 2 <
      uprob fun z : (Bool × (X₀.σ n × X₁.σ n)) × A.Coins n =>
        A.predictor n (ℓ n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1 := by
  sorry

/-! ## (d) Oracle indistinguishability and pseudorandom functions -/

/-- An ensemble of oracles [PS10, Definition 96.1]: at each `n` a sampler of functions
`{0,1}^{ℓ₁ n} → {0,1}^{ℓ₂ n}`. -/
structure OracleEnsemble (ℓ₁ ℓ₂ : ℕ → ℕ) where
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  O : ∀ n, σ n → (Fin (ℓ₁ n) → Bool) → (Fin (ℓ₂ n) → Bool)

attribute [instance] OracleEnsemble.fintype

/-- The random-function ensemble `RF_n` [PS10, §3.8.1]. -/
def OracleEnsemble.random (ℓ₁ ℓ₂ : ℕ → ℕ) : OracleEnsemble ℓ₁ ℓ₂ where
  σ n := (Fin (ℓ₁ n) → Bool) → (Fin (ℓ₂ n) → Bool)
  O _ := randomFunction _ _

/-- A keyed family `f_s` with keys of length `n` as an oracle ensemble. -/
def OracleEnsemble.keyed {ℓ₁ ℓ₂ : ℕ → ℕ} (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁ n) → Bool) → (Fin (ℓ₂ n) → Bool)) :
    OracleEnsemble ℓ₁ ℓ₂ where
  σ n := Fin n → Bool
  O n := F n

/-- An oracle machine's move: the next query, or the final verdict. -/
inductive OracleMove (ℓ₁ : ℕ)
  | query (x : Fin ℓ₁ → Bool)
  | ret (b : Bool)

/-- Decode a machine output as an oracle move: `⟨[false], x⟩` with `|x| = ℓ₁` is a query,
`[true, b]` is the verdict `b`, anything else the verdict `false`. -/
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁ :=
  match pairDecode w, w with
  | some ([false], x), _ => match decodeFin ℓ₁ x with
    | some x => .query x
    | none => .ret false
  | _, [true, b] => .ret b
  | _, _ => .ret false

/-- Encode the history of query/answer pairs. -/
def encodeHist {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool :=
  h.foldr (fun p acc => pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) acc) []

/-- The query tree of a next-query function with budget `q`: after `q` queries the verdict
is forced to `false`. -/
def buildTree {ℓ₁ ℓ₂ : ℕ} (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ℕ → List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
  | 0, hist => match next hist with
    | .ret b => .ret b
    | .query _ => .ret false
  | q + 1, hist => match next hist with
    | .ret b => .ret b
    | .query x => .query x (fun o => buildTree next q (hist ++ [(x, o)]))

/-- A non-uniform PPT oracle machine [PS10, Definition 96.1]: an `NUPPT` next-query machine
driven by the query/answer history, with an explicit polynomial query budget. (Deviation:
oracle tapes are not formalized; the machine is activated once per query on the history.) -/
structure OracleNUPPT extends NUPPT where
  Cq : ℕ
  cq : ℕ

/-- The query budget at parameter `n`. -/
def OracleNUPPT.queryBound (D : OracleNUPPT) (n : ℕ) : ℕ := D.Cq * (n + 1) ^ D.cq

/-- The oracle adversary (query tree per coin string) of an oracle machine at parameter `n`. -/
def OracleNUPPT.toAdversary (D : OracleNUPPT) (n ℓ₁ ℓ₂ : ℕ) :
    OracleAdversary (D.toNUPPT.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) :=
  fun r => buildTree (fun hist => decodeOracleMove ℓ₁ (D.toNUPPT.runAt n (encodeHist hist) r))
    (D.queryBound n) []

/-- The query tree makes at most `queryBound n` queries. -/
theorem OracleNUPPT.toAdversary_boundedBy (D : OracleNUPPT) (n ℓ₁ ℓ₂ : ℕ) :
    (D.toAdversary n ℓ₁ ℓ₂).BoundedBy (D.queryBound n) := by
  sorry

/-- Oracle indistinguishability [PS10, Definition 96.1]. -/
def OracleEnsemble.Indist {ℓ₁ ℓ₂ : ℕ → ℕ} (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=
  ∀ D : OracleNUPPT, Negligible fun n =>
    distAdv (O.O n) (O'.O n) (oracleDist (D.toAdversary n (ℓ₁ n) (ℓ₂ n)))

/-- Pseudorandom function [PS10, Definition 96.2]: `f_s : {0,1}^{|s|} → {0,1}^{|s|}`, computable
in polynomial time from `⟨s, x⟩`, and indistinguishable from a random function. -/
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  pseudorandom : (OracleEnsemble.keyed F).Indist (OracleEnsemble.random id id)

/-- The PRF advantage of an oracle machine at parameter `n` is the concrete `prfAdv`. -/
theorem prfAdv_toAdversary (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (D : OracleNUPPT) (n : ℕ) :
    distAdv ((OracleEnsemble.keyed F).O n) ((OracleEnsemble.random id id).O n)
        (oracleDist (D.toAdversary n n n)) =
      prfAdv (F n) (D.toAdversary n n n) := rfl

/-! ## (e) Interactive strategies, protocols, executions, views -/

/-- A move of an interactive machine: send a message or halt with an output. -/
inductive Move
  | send (m : List Bool)
  | halt (out : List Bool)

/-- Decode a machine output as a move: `⟨[true], m⟩` sends `m`, `⟨[false], o⟩` halts with
output `o`, anything else halts with output `[]`. -/
def decodeMove (w : List Bool) : Move :=
  match pairDecode w with
  | some ([true], m) => .send m
  | some ([false], o) => .halt o
  | _ => .halt []

/-- A next-message function: common input, auxiliary input, random tape, messages received. -/
abbrev NextMsg := List Bool → List Bool → List Bool → List (List Bool) → Move

/-- Encode a list of messages. -/
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []

/-- An interactive strategy [PS10, §4.4]: a next-message function and the explicit polynomial
length `Cr (|x|+1)^cr` of its random tape. Provers in the soundness condition are arbitrary
strategies; honest parties and simulators are `Efficient`. -/
structure Strategy where
  next : NextMsg
  Cr : ℕ
  cr : ℕ

namespace Strategy

/-- The random-tape length at common-input length `n`. -/
def coinLen (S : Strategy) (n : ℕ) : ℕ := S.Cr * (n + 1) ^ S.cr

/-- The next-message function of a (non-uniform) PPT: one activation runs the machine at
parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the whole random tape. -/
def ofNUPPT (A : NUPPT) : Strategy where
  next x z r hist := decodeMove (A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r)
  Cr := A.Cr
  cr := A.cr

/-- The strategy is computed by a PPT (an interactive machine with polynomial time complexity,
[PS10, §4.4]). -/
def Efficient (S : Strategy) : Prop := ∃ A : NUPPT, A.Uniform ∧ S = ofNUPPT A

end Strategy

/-- The view of a party [PS10, §4.4]: common input, auxiliary input, random tape, messages
received. -/
structure View where
  x : List Bool
  z : List Bool
  r : List Bool
  received : List (List Bool)

/-- Encode a view as a word (the input of a distinguisher of views). -/
def View.encode (v : View) : List Bool :=
  pairEncode (pairEncode v.x v.z) (pairEncode v.r (encodeMsgs v.received))

/-- An execution: both views and both outputs (`none` if the party never halted). -/
structure Execution where
  viewA : View
  viewB : View
  outA : Option (List Bool)
  outB : Option (List Bool)

/-- Run the protocol for at most `fuel` activations, `A` moving first; the protocol ends when
the active party halts. -/
def execAux (nA nB : NextMsg) (x zA zB rA rB : List Bool) :
    ℕ → Bool → List (List Bool) → List (List Bool) → Execution
  | 0, _, recA, recB => ⟨⟨x, zA, rA, recA⟩, ⟨x, zB, rB, recB⟩, none, none⟩
  | fuel + 1, true, recA, recB =>
    match nA x zA rA recA with
    | .send m => execAux nA nB x zA zB rA rB fuel false recA (recB ++ [m])
    | .halt o => ⟨⟨x, zA, rA, recA⟩, ⟨x, zB, rB, recB⟩, some o, none⟩
  | fuel + 1, false, recA, recB =>
    match nB x zB rB recB with
    | .send m => execAux nA nB x zA zB rA rB fuel true (recA ++ [m]) recB
    | .halt o => ⟨⟨x, zA, rA, recA⟩, ⟨x, zB, rB, recB⟩, none, some o⟩

/-- The execution `A_{rA}(x, zA) ↔ B_{rB}(x, zB)` with at most `R` activations. -/
def exec (A B : Strategy) (R : ℕ) (x zA zB rA rB : List Bool) : Execution :=
  execAux A.next B.next x zA zB rA rB R true [] []

/-- A protocol: a pair of strategies and an explicit polynomial bound on the number of
activations (Deviation: the text bounds total time per party; we bound activations). -/
structure Protocol where
  P : Strategy
  V : Strategy
  CR : ℕ
  cR : ℕ

namespace Protocol

/-- Activation bound at common-input length `n`. -/
def rounds (π : Protocol) (n : ℕ) : ℕ := π.CR * (n + 1) ^ π.cR

/-- Coins of a random execution of `P' ↔ V` on `x`. -/
abbrev ExecCoins (π : Protocol) (P' : Strategy) (x : List Bool) : Type :=
  (Fin (P'.coinLen x.length) → Bool) × (Fin (π.V.coinLen x.length) → Bool)

/-- The random execution `P'(x, y) ↔ V(x, z)`. -/
def execWith (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) : Execution :=
  exec P' π.V (π.rounds x.length) x y z (List.ofFn r.1) (List.ofFn r.2)

/-- `V` accepts: it halted with output `[true]`. -/
def accepts (e : Execution) : Prop := e.outB = some [true]

/-- The verifier's view in a random execution of the honest protocol: the sampler of
`view_V[P(x, y) ↔ V(x, z)]`. -/
def viewV (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
  (π.execWith π.P x y z r).viewB

/-- The view of an arbitrary verifier strategy `V'` interacting with the honest prover. -/
def viewV' (π : Protocol) (V' : Strategy) (x y z : List Bool)
    (r : (Fin (π.P.coinLen x.length) → Bool) × (Fin (V'.coinLen x.length) → Bool)) : View :=
  (exec π.P V' (π.rounds x.length) x y z (List.ofFn r.1) (List.ofFn r.2)).viewB

end Protocol

/-- Interactive proof [PS10, Definition 116.1]. (Deviation: `out_V = 0` is read as
"`V` does not output `[true]`"; a verifier that never halts is counted as rejecting.) -/
structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
  efficientV : π.V.Efficient
  complete : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => Protocol.accepts (π.execWith π.P x y z r)) = 1
  sound : ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - ε x.length < uprob (fun r : π.ExecCoins P' x => ¬ Protocol.accepts (π.execWith P' x [] z r))

/-- A witness relation for `L` with polynomially bounded witnesses, decidable in polynomial
time (the `R_L` of [PS10, Appendix B]). -/
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  bounded : ∃ C c : ℕ, ∀ x y, R x y → y.length ≤ C * (x.length + 1) ^ c
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧
    ∀ x y, T (pairEncode x y) = true ↔ R x y

/-- Interactive proof with an efficient prover [PS10, Definition 119.5]: `P` is a PPT and
completeness holds for every witness `y ∈ R_L(x)`. -/
structure EfficientProverProof (π : Protocol) (L : Language Bool)
    (R : List Bool → List Bool → Prop) : Prop extends InteractiveProof π L where
  efficientP : π.P.Efficient
  completeWitness : ∀ x y, R x y → ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => Protocol.accepts (π.execWith π.P x y z r)) = 1

/-- A simulator's output on `(x, z)`, read as a view. -/
def _root_.Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) : List Bool :=
  S.runAt x.length (pairEncode x z) r

/-- Honest-verifier zero-knowledge [PS10, Definition 121.1], with a strict PPT simulator. -/
def HVZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∃ S : NUPPT, S.Uniform ∧ ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ x y z, R x y →
      distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length

/-- Zero-knowledge [PS10, Definition 121.2] (Deviation: strict PPT simulators instead of
expected PPT). -/
def ZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ x y z, R x y →
      distAdv (fun r => (π.viewV' V' x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length

/-- Two samplers are `δ`-close in statistical distance: every test set has probabilities within
`δ` (the sup-over-sets form of `statDist`, usable for samples in the infinite type `List Bool`). -/
def StatClose {σ τ γ : Type*} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
  ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ

/-- A distinguisher's advantage is bounded by the statistical closeness (average over its coins;
each coin string gives one test set). -/
theorem distAdv_le_of_statClose {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ]
    (X : σ → γ) (Y : τ → γ) {δ : ℝ} (h : StatClose X Y δ) (D : γ → ρ → Bool) :
    distAdv X Y D ≤ δ := by
  sorry

/-- Statistical zero-knowledge with error `δ`: the simulated view is within statistical distance
`δ |x|` of the real one (implies `ZK` by `distAdv_le_of_statClose` for negligible `δ`);
`δ = 0` is perfect zero-knowledge [PS10, Theorem 122.3]. -/
def StatZK (π : Protocol) (R : List Bool → List Bool → Prop) (δ : ℕ → ℝ) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    StatClose (fun r => (π.viewV' V' x y z r).encode) (S.simulate x z) (δ x.length)

/-- Perfect zero-knowledge is statistical zero-knowledge with error `0`. -/
def PerfectZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop := StatZK π R (fun _ => 0)

theorem StatZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R := by
  sorry

/-- Commitment scheme [PS10, Definition 126.3]: `Com ⟨v, r⟩` for `|v| = n`, `|r| = ℓ n`.
(Source error: the text's binding clause omits `v₀ ≠ v₁`; as printed it is unsatisfiable.) -/
structure Commitment (Com : List Bool → List Bool) (ℓ : ℕ → ℕ) : Prop where
  easy : PolyTimeComputable Com
  ℓ_poly : ∃ C c : ℕ, ∀ n, ℓ n ≤ C * (n + 1) ^ c
  binding : ∀ n (v₀ v₁ r₀ r₁ : List Bool), v₀.length = n → v₁.length = n →
    r₀.length = ℓ n → r₁.length = ℓ n → v₀ ≠ v₁ → Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  hides : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
      (fun r : Fin (ℓ n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r)))
      (D.distinguisherL n) ≤ ε n


/-! ## (e′) Graph isomorphism: expressibility check -/

/-- A graph on `n` vertices as an adjacency predicate. -/
abbrev Graph (n : ℕ) := Fin n → Fin n → Bool

/-- `π(G)`: the graph with edge `(π u, π v)` for every edge `(u, v)` of `G`. -/
def permGraph {n : ℕ} (G : Graph n) (π : Equiv.Perm (Fin n)) : Graph n :=
  fun u v => G (π.symm u) (π.symm v)

/-- A permutation from `n` blocks of `k` uniform bits (Fisher–Yates with the block read modulo
the number of remaining positions; exactly uniform only when every `n - i` divides `2^k`, so
the honest prover and the simulator sample with statistical error `≤ n² / 2^k`). -/
def permOfBits (n k : ℕ) (b : Fin n → Fin k → Bool) : Equiv.Perm (Fin n) :=
  (List.finRange n).foldr
    (fun i σ => (Equiv.swap i ⟨(i + Nat.ofBits (b i) % (n - i)) % n, by
      have := i.isLt; exact Nat.mod_lt _ (by omega)⟩) * σ) 1

/-- [PS10, Lemma 123.5], first half, concrete and exact (uniform permutation on the finite
type): if `σ(G₀) = G₁` then `H = π(G_{b'})` for uniform `(π, b')` is distributed as `π(G₀)`. -/
theorem gi_sim_H_dist {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (hσ : permGraph G₀ σ = G₁)
    (p : Graph n → Prop) :
    uprob (fun z : Equiv.Perm (Fin n) × Bool => p (permGraph (cond z.2 G₁ G₀) z.1)) =
      uprob (fun π : Equiv.Perm (Fin n) => p (permGraph G₀ π)) := by
  sorry

/-- [PS10, Lemma 123.5], second half: whatever (randomized) function of `H` the verifier
`V*` answers with, it equals `b'` with probability exactly `1/2`. -/
theorem gi_sim_half {n : ℕ} {ρ : Type*} [Fintype ρ] (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n))
    (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool) :
    uprob (fun z : (Equiv.Perm (Fin n) × Bool) × ρ =>
      V (permGraph (cond z.1.2 G₁ G₀) z.1.1) z.2 = z.1.2) = 1 / 2 := by
  sorry

end TCSlib.Cryptography

#check @Complexity.NUPPT.runAt
#check @Complexity.NUPPT.ofPolyTime
#check @TCSlib.Cryptography.FunFamily.StrongOneWay
#check @TCSlib.Cryptography.weak_to_strong
#check @TCSlib.Cryptography.Ensemble.Indist
#check @TCSlib.Cryptography.OracleEnsemble.Indist
#check @TCSlib.Cryptography.ZK
#check @TCSlib.Cryptography.Commitment
#check @TCSlib.Cryptography.OneWay.yao_amplification_exp
```
