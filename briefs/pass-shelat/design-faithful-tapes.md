# Design: the computational-model layer, faithfulness-first ("tapes as tapes")

Campaign: Pass–shelat, *A Course in Cryptography* (2010), Chapters 2–4. Run 1, design panel.
Angle: **model the text literally where it is cheap, argue carefully where it is not.**
Companion file: `briefs/pass-shelat/design-faithful-tapes-scratch.lean` — every signature
below marked `[compiles]` is in that file, which typechecks against the current worktree
with `lake env lean` (10 s; only `sorry` warnings, no errors). Line numbers of library
facts cited below were read from the worktree on 2026-10-27.

## 0. Executive summary and recommendation

The literal objects of [PS10] are: a Turing machine **with a random tape** (Def 23.4),
running time bounded **for every random tape, in |x|** (Def 23.5), a **sequence of machines
with a description-size bound** (Def 26.8), **oracle machines with a query tape** (§3.8.2),
and **interactive machines with communication tapes** (§4.4). The library already contains,
unchanged, every ingredient needed to *state* three of these four literally:

| text object | literal rendering, zero new model code | where it comes from |
| --- | --- | --- |
| random tape | work tape `0` of a `Turing.FinTM Bool`, preloaded with `r`, i.e. the run starts at the library's clean seam `Cfg.ofWords M.tm.q₀ (stateWord M.k r)` | `Build/Convention.lean` (`Cfg.ofWords`), `Build/Loop.lean` (`stateWord`) |
| "halts within T(\|x\|) for every random tape" | `∀ x (r : Fin (T |x|) → Bool), (runCoins x (ofFn r) (T |x|)).state = none` | `MultiTapeTM.runFrom` |
| description size of `A_i` | `(A i).serialize.length` for `A i : CodeTM` | `Encoding.lean` (`CodeTM.serialize`, fixed canonical serialization) |
| oracle machine | `Turing.OracleTM` with a *language* oracle; a function oracle `F` is the language `{⟨x, 1^i⟩ | F(x)_i = 1}` | `TuringMachine/Oracle.lean` |

The fourth (ITMs with seven tapes and rounds) is *definable* at moderate cost but every
theorem about a concrete protocol would then be a machine-run argument; it is the one
place where I recommend the next-message model (D8) as the headline, with the literal ITM
as a derived object (§6).

**Recommendation.** Keep the literal *definitions* (they are cheap: ≈ 350 lines of
definitions, all compiled in the scratch), and pay for faithfulness in exactly **four
one-time bridge theorems**, after which every closure lemma is proved in the deterministic
`PolyTimeComputable`-on-`pairEncode x r` world (the plan's D3) and transported:

1. `exists_pairForm` (coin-tape machine → deterministic machine on `pairEncode x r`),
   ≈ 700–900 lines; **load-bearing** (every theorem that *consumes* an adversary).
2. `ofPairForm` (deterministic machine on `pairEncode x r` → coin-tape machine),
   ≈ 500–800 lines; needed to *present* a reduction as an adversary.
3. `nuppt_seq_iff_advice` (Def 26.8 verbatim ⇔ advice form), ≈ 1200–1600 lines, the
   `⇐` half conditional on `PolyBound c.canonizerTime` for the chosen effective code
   (precedent: `Complexity.TMSAT_mem_NP` carries the same hypothesis).
4. `exists_queryTree` (oracle machine → `OracleAdversary` query tree), ≈ 300–400 lines;
   plus, for oracle *reductions*, the stateful handler compilation, ≈ 1000–1500 lines
   (§5; the only item I rate as possibly prohibitive, with a named fallback).

If a bridge is not closed in the fill campaign, the literal definition still stands and the
bridge is **one named admission** instead of a deviation smeared over every theorem. That is
the whole point of the design: faithfulness is bought once, at the boundary.

Honest total: ≈ 9–12 k new Lean lines, 28–40 agent-days, of which the literal choices
cost ≈ 3.5–5 k lines / 11–16 days over the plan's D3/D4/D7/D8 baseline. Section 8 has the
per-component table.

---

## 1. (a) Probabilistic polynomial-time machines, literally

### 1.1 The text

* Def 23.4: a TM "equipped with an extra random tape. Each bit of the random tape is
  uniformly and independently chosen. Equivalently … access to a coin-tossing oracle".
* Def 23.5: "runs in time T(n) if for all x and **for every random tape**, A(x) halts within
  T(|x|) steps"; polynomial if T(n) = n^c for some c.
* Def 24.6: computes f if "A on input x outputs f(x) with probability 1".

### 1.2 Three literal candidates considered

**A1 — per-step coins (`Turing.FinNDTM`).** The NDTM of `Nondeterministic.lean` consumes one
choice bit per step (`runWith`), and `NDTM.HaltsWithin x t` is *exactly* "every choice word of
length t halts" — Def 23.5 verbatim, with the coin budget equal to the step budget. Nothing
new to define. Rejected because (i) there is no encoding of NDTMs (`CodeTM` is deterministic
and 1-tape), so Def 26.8's description size cannot be stated; (ii) no universal machine for
NDTMs; (iii) all closure infrastructure (`Composition`, `Build/*`) is deterministic, so the
NDTM→FinTM compilation of `ClassNP/Nondeterminism.lean` (the private `choiceCore*` family,
~1000 lines) would have to be promoted anyway. A1 is strictly dominated by A3.

**A2 — a new `MultiTapeTM` wrapper with a read-only coin tape.** A new structure
`CoinTM k Symbol State` whose step function reads an extra read-only tape. Rejected: it
re-derives the whole configuration/run/time lemma layer (`Oracle.lean` is 517 lines for a
one-step modification), and every library gadget (`leftCfg/rightCfg`, `capture_run`,
`bufferedSecondCfg_run`, the loop host) is stated for `MultiTapeTM`, not for the wrapper.

**A3 — coins pre-written on work tape 0 (chosen).** The library's machine-construction
discipline already starts machines at a *clean seam* `Cfg.ofWords q (stateWord k w)`:
control at `q`, input head at `1`, tape `0` holding `w` from the origin, other tapes blank,
output empty (`Build/Convention.lean:75`, `Build/Loop.lean:122`). A PPT is a `FinTM Bool`
started at the seam with `w := r`. The random tape is a genuine tape; the native input tape
holds `x`; time is measured in `|x|`. Deviation (recorded): the tape is read/write rather
than read-only, and finite (length `T |x|`), both harmless — a `T`-step run can neither
reach cell `T` of tape 0 nor benefit from writing coins it could have copied.

### 1.3 Signatures `[compiles]`

```lean
namespace Complexity.Randomized

/-- An explicit polynomial `C * (n + 1) ^ c` (campaign convention; never an abstract
`ℕ → ℕ`). -/
structure Poly where
  C : ℕ
  c : ℕ

def Poly.eval (p : Poly) (n : ℕ) : ℕ := p.C * (n + 1) ^ p.c

/-- Literal [PS10, Definition 23.4]: run `M` on native input `x` with the random tape `r`
written on work tape `0` (the library's clean seam), for `t` steps. -/
def _root_.Turing.FinTM.runCoins (M : FinTM Bool) (x r : List Bool) (t : ℕ) :
    Cfg M.k Bool M.State x :=
  M.tm.runFrom (Cfg.ofWords M.tm.q₀ (stateWord M.k r)) t

/-- A probabilistic polynomial-time machine [PS10, Definitions 23.4, 23.5]: halts within
`T |x|` steps for every input and every random tape of length `T |x|`. -/
structure PPT where
  M : FinTM Bool
  T : Poly
  halts : ∀ (x : List Bool) (r : Fin (T.eval x.length) → Bool),
    (M.runCoins x (List.ofFn r) (T.eval x.length)).state = none

abbrev PPT.Coins (A : PPT) (n : ℕ) : Type := Fin (A.T.eval n) → Bool

/-- Output on `x` with an arbitrary coin tape `r` (the run is cut at `T |x|`). -/
def PPT.runWith (A : PPT) (x r : List Bool) : List Bool :=
  (A.M.runCoins x r (A.T.eval x.length)).output

/-- Sampler at coin budget `N`: coins beyond `T |x|` are never read, so for `|x| ≤ N` this
is the distribution `A(x)` with extra unread uniform coins. -/
def PPT.sampleAt (A : PPT) (N : ℕ) (x : List Bool) (r : A.Coins N) : List Bool :=
  A.runWith x (List.ofFn r)

def PPT.sample (A : PPT) (x : List Bool) (r : A.Coins x.length) : List Bool :=
  A.sampleAt x.length x r

/-- [PS10, Definition 24.6]: `A` computes `f` with probability one. -/
def PPT.Computes (A : PPT) (f : List Bool → List Bool) : Prop :=
  ∀ x, uprob (fun r : A.Coins x.length => A.sample x r = f x) = 1
```

Why `sampleAt N` and not only `sample`: an adversary's input length varies with the
sample (e.g. `pairEncode 1^n (f x)` for a non-length-regular `f`, or an ensemble whose
samples have length `≤ ℓ(n)`); `uprob` needs one finite coin type per experiment, and a
Σ-type of coin strings of varying length is **not** the right measure (longer strings would
be over-weighted). The device "sample with the coins of the longest input, extra coins
unread" is exact because of the lemma below; it replaces the Σ-type everywhere.

### 1.4 Lemmas that make the definition usable (new, cheap)

```lean
/-- Cells of tape 0 at distance ≥ t are never visited in t steps: the first `t` coins
determine the run. (Same induction as `OracleTM.runFrom_workTapes_blank`.) -/
theorem runCoins_eq_of_take (M : FinTM Bool) (x r r' : List Bool) (t : ℕ)
    (h : r.take t = r'.take t) : M.runCoins x r t = M.runCoins x r' t
-- ≈ 80 lines

/-- `sampleAt N` for `|x| ≤ N` is `sample` with ignored extra coordinates; with
`acceptProb_fst`/`uprob_fst` this transports every probability statement. -/
theorem sampleAt_eq (A : PPT) {N : ℕ} (x : List Bool) (hN : x.length ≤ N)
    (r : A.Coins N) : A.sampleAt N x r = A.sample x (fun i => r (Fin.castLE (A.T.eval_mono hN) i))
-- ≈ 30 lines

/-- Probability one over a finite uniform space is "for all coins"
(`OneWay.forall_of_uprob_eq_one`). -/
theorem PPT.Computes.forall (h : A.Computes f) : ∀ x r, A.sample x r = f x

/-- Def 24.6 ⇔ deterministic polynomial time [PS10, Def 21.2/21.3]: fix the coins `1^T`.
(⇒) install `1^{T|x|}` on tape 0 by `computesFunInTime_polyUnary` through
`exists_installCallTM`, then run `M` from the seam: ≈ 200 lines.
(⇐) a deterministic machine ignoring tape 0: the `rightCfg_run` embedding of
`Simulation.lean:287` with a one-tape left block: ≈ 150 lines. -/
theorem ppt_computes_iff (f : List Bool → List Bool) :
    (∃ A : PPT, A.Computes f) ↔ PolyTimeComputable f
```

Audit notes on the quantifier shapes:
* `T.eval` is `C (n+1)^c`, never `0` for `C ≥ 1`; a `PPT` with `T.C = 0` is uninhabited
  (`not_computesInTime_zero`), which is the right behaviour (not a vacuous class).
* `halts` quantifies over tapes of length *exactly* `T |x|`; quantifying over all `List Bool`
  would also force halting when the tape runs out (blank symbols are a third value), a
  strengthening the text does not make. `runCoins_eq_of_take` extends to longer tapes.
* `M.k = 0` is allowed: `stateWord 0 r` is the empty family, the machine is deterministic.
  Harmless (a PPT may ignore its coins); recorded in the docstring.

### 1.5 How `1^n` is supplied; how outputs are decoded `[compiles]`

```lean
def ones (n : ℕ) : List Bool := List.replicate n true          -- the string 1^n
-- an adversary receiving (1^n, y) is run on `pairEncode (ones n) y`
-- (self-delimiting pairing; the brief forbids plain concatenation).

/-- Decoding an output as an `n`-bit string; a wrong length is a failure (D5). -/
def decodeBits (n : ℕ) (w : List Bool) : Option (Fin n → Bool) :=
  if w.length = n then some (fun i => w.getD i false) else none
```

Machines that must *produce* `1^n` from their own input use
`Complexity.polyTimeComputable_unary` (`x ↦ 1^{|x|}`) and `polyTimeComputable_polyUnary`
(`x ↦ 1^{C(|x|+1)^d}`), both proved (`ClassNP/PolyTimePairing.lean`).

### 1.6 Plugging into the concrete layer

`invProb f A` wants a total `A : β → ρ → α`; a machine's output decoded by `decodeBits` is
an `Option`. Two consistent conventions, both needed:

* **Hypothesis direction** (consuming an adversary): define the *asymptotic* success event
  literally with the `Option` (§2.2, `invSucc`), and prove
  `invSucc F A n ≤ invProb (F.f n) (getD-decoded A)` — every genuine success is a success of
  the totalised inverter — so the concrete reduction (`yao_amplification_exp`, Goldreich–Levin,
  …) can be fed.
* **Conclusion direction** (a reduction's output): the reduction's output is an honest
  `α` re-encoded with `List.ofFn`, and `decodeBits n (List.ofFn v) = some v`, so the
  asymptotic success *equals* the concrete one.

Distinguishers lose nothing: `D(t) = 1` is `decide (output = [true])`, a total `Bool`.

---

## 2. (a′) Non-uniform PPT: Definition 26.8 verbatim, with the advice form as a corollary

### 2.1 Two structures `[compiles]`

```lean
/-- Advice formulation (the text's "alternatively"; the plan's D4). Time and advice length
are measured in `|x|`, as in `Turing.FinTM.DecidesWithAdviceInTime`. -/
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

/-- [PS10, Definition 26.8] verbatim: a sequence of probabilistic machines `A₁, A₂, …` and
a polynomial `d` with `|A_i| < d(i)` and running time `< d(i)`; `A(x)` runs `A_{|x|}(x)`.
Machines are in code normal form (`CodeTM`: one work tape, which is the random tape);
`|A_i|` is the length of the library's fixed canonical serialization. -/
structure NUPPTSeq where
  mach : ℕ → CodeTM
  d : Poly
  size : ∀ n, (mach n).serialize.length < d.eval n
  halts : ∀ (x : List Bool) (r : Fin (d.eval x.length) → Bool),
    ((mach x.length).toFinTM.runCoins x (List.ofFn r) (d.eval x.length)).state = none
```

Deviations of `NUPPTSeq` from the text, all recorded: "running time less than d(i)" is
rendered as "halted after d(i) steps" (off by one); `|A_i|` is w.r.t. the library's
serialization (`CodeTM.serialize`, Encoding.lean:518; unary state indices, so the
serialization is quadratic in the number of states — still polynomially equivalent to any
reasonable encoding); the machines have one work tape, which is also the random tape
(`SingleTape.one_work_tape_binary` shows this loses only a quadratic factor).

### 2.2 The equivalence theorem `[compiles, sorried shape]`

```lean
/-- Behavioural equivalence of two coin-tape machines: same output on every input and every
sufficiently long coin tape (extra coins unread, §1.4). -/
def SameBehaviour (f g : List Bool → List Bool → List Bool) (ℓ : ℕ → ℕ) : Prop :=
  ∀ x r, ℓ x.length ≤ r.length → f x r = g x r

theorem nuppt_seq_iff_advice (c : EffectiveMachineCode) (hc : PolyBound c.canonizerTime) :
    (∀ A : NUPPTSeq, ∃ B : NUPPT, SameBehaviour A.runWith B.runWith
        (fun n => max (A.d.eval n) (B.T.eval n))) ∧
    (∀ B : NUPPT, ∃ A : NUPPTSeq, SameBehaviour A.runWith B.runWith
        (fun n => max (A.d.eval n) (B.T.eval n)))
```

**Proof plan and cost.**

*(⇒, sequence → advice).* Advice `α(n) := (A.mach n).serialize`, length `< d(n)`. The
uniform machine is the timed universal machine `Complexity.timed_universal_quantitative c`
(`ClassNP/TMSAT.lean:710`, public):
`U` on `pairEncode (pairEncode (Nat.bits t) α) x'` simulates `(c.decode α).toFinTM` on `x'`
for `t` steps within `(3|α| + 14·canonizerTime|α| + 50)(t+1)²`, which is polynomial in
`|α| ≤ d(n)` **iff** `canonizerTime` is polynomially bounded — hence the hypothesis `hc`
(`MathlibBridge.exists_effectiveMachineCode` makes "no polynomial claim"; `TMSAT_mem_NP`
carries the same hypothesis, so this is established precedent, not a new admission).
Two obstacles, both solvable:
1. `U` simulates a machine from its **blank** initial configuration, but `A_n` must start
   with the coin tape `r` on its tape. So the simulated machine is not `A_n` but its pair
   form `det(A_n)` (bridge (i) of §2.4 specialised to `CodeTM`, run on `pairEncode x r`);
   the advice becomes `serialize (det (A.mach n))`, which requires the size bound
   `|serialize (det M)| ≤ K·(|serialize M| + 1)²` — a bookkeeping lemma on the construction
   (≈ 150 lines) plus `serialize_length_le_sq : |serialize M| ≤ K (numStates+1)²` (≈ 80 lines,
   direct from the definition).
2. `U`'s input layout is `⟨⟨bits t, α⟩, x'⟩` while an `NUPPT` runs on
   `⟨x, α⟩` with coins on tape 0: compose with the polynomial-time rearrangement
   `⟨x, α⟩ ↦ ⟨⟨bits(d |x|), α⟩, ⟨x, r⟩⟩` — `PolyTimeComputable.pairEncode`,
   `polyTimeComputable_polyBits` (`Build/Primitives.lean:2183`), `pairFstD/pairSndD`; and the
   coins `r` must be moved from tape 0 into the input string, which is bridge (ii).
   Estimate (⇒): 400–600 lines on top of the bridges.

*(⇐, advice → sequence).* Given `B` (uniform `M`, advice `α`), build `A_n :=
hardwire(M₁, α n)` where `M₁` is a one-work-tape form of the **fixed** machine `M`
(`one_work_tape_binary`; since `M` is fixed, `M₁` has a constant number of states — no size
bound through the robustness theorem is needed), and `hardwire(M₁, w)` runs `M₁` on the
*virtual* input `pairEncode x w` (x native, doubled bits; `w` read from finite control) with
`M₁`'s single tape = the coin tape. Its state type is `M₁.State × Fin (2|w| + 4)`, so
`numStates ≤ K_M (|w| + 1)` and `|serialize| ≤ K'_M (|w|+1)² < d(n)` for `d` of degree
`2·deg a + 1`. The lockstep lemma "doubled-input decoding + finite-control suffix" is the
same gadget as bridge (i); state reindexing to `Fin` is `exists_codeTM` (Encoding.lean:583)
transported along `StateRenaming`. Estimate (⇐): 800–1000 lines, 2–3 days.

**Cheapest faithful alternative if (⇐) stalls.** Replace `|A_i|` by the table-size proxy
`Fintype.card (A i).State * 3 ^ ((A i).k + 1)` on multi-tape `FinTM`s (polynomially
equivalent to any serialization, documented as a Deviation). Then (⇐) needs no single-tape
conversion and no serialization lemma: `hardwire` keeps `M`'s `k` tapes plus one coin tape
and its state type is visible (`bufferedCompTM`'s state type is a public definition), so the
bound is `simp [Fintype.card_prod, Fintype.card_sum]`. ≈ 500 lines. The text's "description
size" is then a proxy — acceptable, but the verbatim form is my recommendation.

### 2.3 Policy on quantifiers

All chapter 2–4 security definitions are stated over `NUPPT` (advice form). The verbatim
form is available through `nuppt_seq_iff_advice` as a corollary of each definition
(`StrongOneWay_iff_seq : StrongOneWay F ↔ PolyTimeComputable F.str ∧ ∀ A : NUPPTSeq, Negligible (invSuccSeq F A)`,
proved by transporting `SameBehaviour` through `uprob` with `runCoins_eq_of_take`). This
keeps the closure calculus free of code-size bookkeeping, which the existential API of the
machine library (`∃ M c, …`) could not support anyway.

### 2.4 The two bridges to the deterministic world (the price of A3)

```lean
/-- The D3 face of a coin-tape machine: a deterministic polynomial-time machine on
`pairEncode x r` with the same input/output behaviour. -/
def PairForm (A : NUPPT) (f : List Bool → List Bool) : Prop :=
  PolyTimeComputable f ∧ ∀ x (r : A.Coins x.length),
    f (pairEncode x (List.ofFn r)) = A.sampleAt x.length x r

theorem exists_pairForm (A : NUPPT) : ∃ f, PairForm A f            -- bridge (i)
theorem ofPairForm (f) (hf : PolyTimeComputable f) (ℓ : Poly) :          -- bridge (ii)
    ∃ B : NUPPT, ∀ x (r : Fin (ℓ.eval x.length) → Bool),
      B.sampleAt (ℓ.eval x.length) x (… r padded …) = f (pairEncode x (List.ofFn r))
```

*Bridge (i), construction.* On native input `z = pairEncode x r`: (1) copy `z` to tape 0
(`pairDup`-style scan, or the install-call of `id`); (2) `exists_installCallTM` applied to
`computesFunInTime_pairSnd` installs `r = pairSndD z` on tape 0 from the seam
(Build/Loop.lean:5645, public, proved); (3) run `M` with the **doubled-input decoder**: the
native head sits on the first cell of each doubled pair; a virtual cell is `bb`, the virtual
right blank is the separator `01`, the virtual left blank is the native left blank; each
simulated step costs ≤ 4 native steps; state type `M.State × Fin 4`. (3) is a lockstep lemma
in the style of `leftCfg_run`/`capture_run` (`runFrom_comm_of_step`), ≈ 300 lines; phases (1)–(2)
are seam-to-seam and compose with `runFrom_add`. Total ≈ 700–900 lines. Time
`O(|z| + T|x|)`, polynomial in `|z|`. The same decoder is reused by §2.2 (⇐).

*Bridge (ii), construction.* From the seam (native `x`, tape 0 = `r`), emit the string
`pairEncode x r` into a buffer (doubling scan of the native input, separator, copy of tape 0;
a 1-tape emitter with its run lemma, ≈ 200 lines), then run the deterministic machine on the
buffer as virtual input: this is phase 2 of `bufferedCompTM`, whose public run lemma
`Simulation.lean:807 bufferedSecondCfg_run` takes an **arbitrary** second-machine
configuration and arbitrary left-block tapes — so the coin tape in the left block costs
nothing. Only the phase-1 lemma `bufferedComp_start` (Simulation.lean:925) is stated from
`Cfg.init`; a seam variant is a private copy (≈ 150 lines, request promotion). Total
≈ 500–800 lines.

Both bridges are the only places where coin-tape semantics meets string semantics. Every
closure lemma of §7 is proved on the string side and transported.

---

## 3. (b) One-way functions and Theorem 35.1

### 3.1 Domains

[PS10] writes `f : {0,1}* → {0,1}*`. Two renderings were costed:

* **Literal strings** `f : List Bool → List Bool` with `x ← {0,1}^n`. Feasible with the
  `sampleAt N` device (`N := 2n + 2 + L_f(n)`, `L_f` the output-length polynomial from
  `PolyTimeComputable.output_length_le`), and the concrete layer tolerates `β := List Bool`
  (`invProb` needs only `DecidableEq β`). Cost: every statement carries the length bound and
  a `pairEncode`-tuple encoding of `Fin q → List Bool` for products.
* **Typed, length-regular families** (the plan's D5): the concrete layer's convention; the
  only change for faithfulness is to allow the domain at parameter `n` to be `{0,1}^{ℓ(n)}`
  rather than `{0,1}^n`, which Theorem 35.1 needs (`f'` lives on `{0,1}^{n·m(n)}`).

I take the typed family, with the Deviation recorded once in the structure's docstring.
`[compiles]`:

```lean
structure FunFamily where
  ℓ : Poly
  m : Poly
  f : ∀ n, (Fin (ℓ.eval n) → Bool) → Fin (m.eval n) → Bool

/-- The string function the "easy to compute" clause is about. -/
def FunFamily.str (F : FunFamily) (w : List Bool) : List Bool :=
  List.ofFn (F.f w.length (fun i => w.getD i false))
/-- `|pairEncode 1^n y|` for `|y| = m n`. -/
def FunFamily.advIn (F : FunFamily) (n : ℕ) : ℕ := 2 * n + 2 + F.m.eval n

/-- `Pr[x ← {0,1}^{ℓ n}; y ← f(x) : f(A(1^n, y)) = y]`, output decoded as an `ℓ n`-bit string
(wrong length = failure). [PS10, Definition 27.3] -/
noncomputable def invSucc (F : FunFamily) (A : NUPPT) (n : ℕ) : ℝ :=
  uprob fun z : (Fin (F.ℓ.eval n) → Bool) × A.Coins (F.advIn n) =>
    ∃ x', decodeBits (F.ℓ.eval n)
      (A.sampleAt (F.advIn n) (pairEncode (ones n) (List.ofFn (F.f n z.1))) z.2) = some x' ∧
      F.f n x' = F.f n z.1

/-- [PS10, Definition 27.3]. "∃ negligible e, ∀ n, … ≤ e n" is `Negligible` (§4.2). -/
def StrongOneWay (F : FunFamily) : Prop :=
  PolyTimeComputable F.str ∧ ∀ A : NUPPT, Negligible (invSucc F A)

/-- [PS10, Definition 28.4]. `0 < q.C` is load-bearing: with `q = 0` the bound `1 - 1/0 = 1`
is vacuous. -/
def WeakOneWay (F : FunFamily) : Prop :=
  PolyTimeComputable F.str ∧ ∃ q : Poly, 0 < q.C ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀,
    invSucc F A n ≤ 1 - 1 / (q.eval n : ℝ)

/-- [PS10, Definition 26.1]: no adversary inverts everywhere with probability one.
Literal detail: here `A` receives `f(x)` only (no `1^n`), as in the text. -/
def WorstCaseOneWay (F : FunFamily) : Prop :=
  PolyTimeComputable F.str ∧ ¬ ∃ A : NUPPT, ∀ n (x : Fin (F.ℓ.eval n) → Bool),
    uprob (fun r : A.Coins (F.m.eval n) =>
      ∃ x', decodeBits (F.ℓ.eval n) (A.sampleAt (F.m.eval n) (List.ofFn (F.f n x)) r)
        = some x' ∧ F.f n x' = F.f n x) = 1
```
(The scratch file has `WorstCaseOneWay` with `1^n` supplied; the literal form above is the
one to freeze — the difference matters only for length-shrinking `f`, which is exactly the
pathology the text discusses after Def 27.3.)

"Easy to compute" is `PolyTimeComputable F.str`, which by `ppt_computes_iff` (§1.4) is the
text's "a PPT `C` computes `f`" with probability 1.

### 3.2 Theorem 35.1 `[compiles, sorried shape]`

```lean
/-- `f'(x₁,…,x_{m n}) = (f x₁, …, f x_{m n})` at parameter `n`, flattened to bit strings;
domain `{0,1}^{ℓ(n)·m(n)}` via `finProdFinEquiv`. [PS10, Theorem 35.1] -/
def FunFamily.prod (F : FunFamily) (m : Poly) : FunFamily

theorem weak_to_strong (F : FunFamily) (hF : WeakOneWay F) :
    ∃ m : Poly, StrongOneWay (F.prod m)
```
Deviation: the inverter of `f'` receives `1^n` (the family's parameter) rather than
`1^{n·m(n)}`; `f'` is defined only on lengths `ℓ(n)m(n)`. Both are what the text's
statement means (it indexes by `n` and uses `p(nm)` for the adversary's polynomial).

**Proof plan reusing `TCSlib.Cryptography.OneWay.yao_amplification_exp`** (its statement,
read from `OneWayFunctions/Amplification.lean:296`):
```
yao_amplification_exp [Inhabited α] [NeZero q] [Nonempty ρ] (f : α → β)
  (B : (Fin q → β) → ρ → (Fin q → α)) {n α' μ₀ : ℝ} (T : ℕ) (hα₁ : α' ≤ 1)
  (hq : 2 * n ≤ α' * q) (hT : 2 * n * q ≤ μ₀ * T) (hμ₀ : 2 * Real.exp (-n) < μ₀)
  (hμ : μ₀ ≤ invProb (prodFun f q) B) :
  1 - α' / 2 - Real.exp (-n) ≤ invProb f (yaoInverter f B T)
```
1. From `hF` get `q_w : Poly`; set `m := ⟨2 q_w.C, q_w.c + 1⟩` (so `m n ≥ 2n q_w(n)`, the
   text's `m = 2nq(n)`; `q := m n` is the concrete `q` with `α' := 1/q_w(n)`, and
   `2n ≤ α' q` holds).
2. Suppose `¬ StrongOneWay (F.prod m)`: some `A' : NUPPT` with `¬ Negligible (invSucc …)`;
   `not_negligible_iff` gives `c` and infinitely many `n` with `invSucc ≥ 1/n^c =: μ₀ n`.
3. At each such `n`, let `B := decode ∘ A'.sampleAt …` (output decoded as `Fin q → Fin (ℓ n) → Bool`
   through `finProdFinEquiv`, wrong length ↦ `default`), `ρ := A'.Coins _`;
   `invSucc_le_invProb` (§1.6) gives `hμ`. Take `T := 2 n q · n^c`; `hT`, `hμ₀` hold for
   large `n` (`2e^{-n} < n^{-c}` eventually: `negligible_two_pow_neg`-style bound).
4. Conclude `1 - α'/2 - e^{-n} ≤ invProb f (yaoInverter f B T)`, which exceeds
   `1 - 1/q_w(n)` for large `n`.
5. **Machine closure**: exhibit `yaoInverter f B T` as (the sampler of) a single
   `NUPPT A` independent of `n`, with advice `α_A(n) := α_{A'}(advIn (F.prod m) n)`
   (advice pass-through, C6 of §7). The machine: `exists_loopFindTM` with fuel
   `R n := T(n)` (computed by `polyBits`), round state = the remaining coins, body =
   [split off one chunk of coins (C3), compute `i` and `x_j`s and plant `y`
   (`F.str` via `PolyTimeComputable`, install-called), call `B` (pair form of `A'`, bridge (i),
   install-called), test `f(z_i) = y` (`polyTimeComputable_lenEq`+`ite`), accept with payload
   `z_i`]. The loop's `List.range.find?` semantics equals `yaoInverter`'s `foldr`-first-success
   by a 40-line pure lemma. Then `A := ofPairForm` (bridge (ii)) is the `NUPPT` the hypothesis
   `hF` is instantiated with.
6. Contradiction with `hF` at a large `n` of step 2.

Closure lemmas named: C3 (coin splitting), C5/C6 (advice), C7 (polynomially many fresh-coin
calls, first success), C10 (deterministic sub-steps as calls), bridges (i)/(ii).
Negligible-arithmetic: `not_negligible_iff`, `Negligible.mono`, `negligible_two_pow_neg`.

Theorem 35.2 (`g(x,y) = (f x, f y)`) is the `q = 2`, `T = 1` instance of the same skeleton
without the loop (C3 + C10 only); it is the smoke test of the closure layer.

---

## 4. (c) Ensembles and computational indistinguishability

### 4.1 Ensembles `[compiles]`

```lean
/-- [PS10, Definition 69.3], Deviation D6: samplers from uniform seeds of explicit
polynomial length; samples are strings of length ≤ `len n` (exact length `ℓ(n)` is the
predicate `Regular` below), so that `M(X_n)` is again an ensemble without padding. -/
structure Ensemble where
  s : Poly
  len : Poly
  X : ∀ n, (Fin (s.eval n) → Bool) → List Bool
  len_le : ∀ n r, (X n r).length ≤ len.eval n

def Ensemble.Regular (X : Ensemble) : Prop := ∀ n r, (X.X n r).length = X.len.eval n
def uniformEnsemble (l : Poly) : Ensemble := ⟨l, l, fun _ r => List.ofFn r, by simp⟩
```
Why not the literal "any probability distribution over `{0,1}*`" (`FinDist`): every
distribution in the text is efficiently samplable, the concrete lemmas (`distAdv_sunglassRed`,
`exists_multicopyRed_ge`) are stated for samplers, and the multicopy reduction *needs*
samplability. A `FinDist` layer would be a second concrete layer. Deviation recorded (D6).

### 4.2 Indistinguishability `[compiles]`

```lean
/-- The distinguisher of a machine at length bound `N`: `D(t) = 1` iff output `[true]`.
Literal detail: `D` receives `t` only (no `1^n`), as in Definition 69.4; its advice and time
are therefore indexed by `|t|`. -/
def NUPPT.dist (D : NUPPT) (N : ℕ) : List Bool → D.Coins N → Bool :=
  fun t r => decide (D.sampleAt N t r = [true])

/-- [PS10, Definition 69.4]. -/
def CompIndist (X Y : Ensemble) : Prop :=
  ∀ D : NUPPT, Negligible fun n =>
    distAdv (X.X n) (Y.X n) (D.dist (max (X.len.eval n) (Y.len.eval n)))
```
`∃ e negligible, ∀ n, adv n < e n` ⇔ `Negligible adv`: (⇒) `Negligible.mono`; (⇐)
`e n := |adv n| + 2^{-n}` with `Negligible.add`, `negligible_two_pow_neg`. 20-line lemma
`negligible_iff_exists_bound`, used by every definition of the form "∃ e …".

### 4.3 Lemma 71.5 (closure under efficient operations) `[compiles, sorried]`

```lean
/-- `M(X_n)`: seeds of `X` followed by coins for `M` (seed budget majorised by one explicit
polynomial, `mapSeed_le`). -/
def Ensemble.map (X : Ensemble) (M : NUPPT) : Ensemble
theorem CompIndist.map (h : CompIndist X Y) (M : NUPPT) : CompIndist (X.map M) (Y.map M)
```
Proof: `D' := D ∘ M` with coins split (C3), advice paired (C6); then
`distAdv_sunglassRed (P := M's sampler) X Y D` (Pseudorandom/Indistinguishability.lean:146)
gives *equal* advantage, after `acceptProb_comp_equiv` for the seed re-association
(`Equiv.prodAssoc`-style, as in the file's own `acceptProb_bind`).

### 4.4 Lemma 71.6 (hybrid) and Lemma 73.8 (prediction) `[compiles, sorried]`

```lean
theorem hybrid_lemma {m : ℕ} (hm : 1 < m) (X : Fin m → σ → γ) (D : γ → ρ → Bool) {ε : ℝ}
    (h : ε < distAdv (X ⟨0,_⟩) (X ⟨m-1,_⟩) D) :
    ∃ i, ∃ hi : i + 1 < m, ε / m < distAdv (X ⟨i,_⟩) (X ⟨i+1,hi⟩) D
-- direct from `exists_hybrid_gap (P := fun i => acceptProb (X i) D)` (m-1 gaps, `ε/(m-1) ≥ ε/m`).

/-- The identity behind Lemma 73.8 (as in `predProb_owpPredictor_false`, via `uprob_bool_prod`). -/
theorem predict_eq (X : Bool → σ → γ) (D : γ → ρ → Bool) :
    uprob (fun z : Bool × σ × ρ => D (X z.1 z.2.1) z.2.2 = z.1) =
      1 / 2 + (acceptProb (X true) D - acceptProb (X false) D) / 2

theorem prediction_lemma (X⁰ X¹ : Ensemble) (D : NUPPT) (μ : ℕ → ℝ)
    (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv (X⁰.X n) (X¹.X n) (D.dist _)) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1/2 + μ n / 2 ≤ uprob (fun z => … A predicts b …)
```
`A` is `D` or `¬D` (C12, `polyTimeComputable_ite`), chosen *uniformly* by pigeonhole over
the infinite set (one sign occurs infinitely often) — no advice needed, matching the text.

### 4.5 Garg reuse map

| text | concrete lemma reused | asymptotic glue |
| --- | --- | --- |
| 71.5 | `distAdv_sunglassRed`, `pushSampler`, `acceptProb_bind` | C1+C3+C6, `Ensemble.map` |
| 71.6 | `exists_hybrid_gap`, `abs_sub_le_sum_hybrids` | none |
| multicopy (used by 93.1/99.2) | `exists_multicopyRed_ge` (index `k` as advice C14), `distAdv_multicopyAvgRed` not used (uniform `k ← [t]` is non-dyadic) | C7 (sample `t-1` copies) |
| 73.8 | `uprob_bool_prod` | C12 |
| 75.4 next-bit | `exists_prgExtBitsRed_ge`'s hybrid shape | C7, C12 |
| 79.4 / 81.7 | `exists_owpPredictorBits`, `exists_prgExtBitsRed_ge` | C3, C14 (`flip` as advice) |
| 87.3 GL | `invProb_guessInverter_cubic` | C7 (`n(2^k-1)` calls), C9 (majority) |

---

## 5. (d) Oracle machines and pseudorandom functions

### 5.1 Literal oracle machines `[compiles]`

`Turing.OracleTM k Symbol State` (Oracle.lean) has a query tape (index `Fin.last k`), the
states `qQuery/qYes/qNo`, and a **language** oracle. The text's oracle "receives requests on a
special tape and writes its responses to a tape"; a function oracle `F : {0,1}^n → {0,1}^n`
is rendered as the language of bit queries:

```lean
structure FinOracleTM where
  k : ℕ
  State : Type
  [fintypeState : Fintype State]
  [decEqState : DecidableEq State]
  tm : OracleTM k Bool State
  wf : tm.WellFormed

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
  /-- time bound for every oracle, every input, every random tape -/
  halts : ∀ (O : Language Bool) (x : List Bool) (r : Fin (T.eval x.length) → Bool),
    (M.runCoins O (pairEncode x (advice x.length)) (List.ofFn r) (T.eval x.length)).state = none

/-- `⟨x, 1^i⟩ ∈ O_F ↔ F(x)_i = 1`: a function oracle as a language, one bit per query. -/
def langOf {n : ℕ} (F : (Fin n → Bool) → Fin n → Bool) : Language Bool :=
  {w | ∃ (x : Fin n → Bool) (i : Fin n), w = pairEncode (List.ofFn x) (ones i) ∧ F x i = true}

abbrev NUOraclePPT.Coins (D : NUOraclePPT) (n : ℕ) : Type := Fin (D.T.eval n) → Bool
/-- `D^{F}(1^n) = 1`. -/
noncomputable def NUOraclePPT.oracleDist (D : NUOraclePPT) (n : ℕ) :
    ((Fin n → Bool) → Fin n → Bool) → D.Coins n → Bool :=
  fun F r => decide ((D.M.runCoins (langOf F) (pairEncode (ones n) (D.advice n))
    (List.ofFn r) (D.T.eval n)).output = [true])
```
Deviation: the oracle answers one output bit per query (`n` queries per evaluation of `F`),
a polynomial overhead over the text's string-valued oracle; `WellFormed` is the standing
hypothesis of the oracle interface (Oracle.lean docstring, finding 2). Note that the
*definition* of oracle indistinguishability needs no query trees at all.

```lean
/-- [PS10, Definition 96.1] (the text's `{O'_n} ≈ {O'_n}` is a typo for `{O_n} ≈ {O'_n}`). -/
structure OracleEnsemble where
  s ℓ₁ ℓ₂ : Poly
  O : ∀ n, (Fin (s.eval n) → Bool) → (Fin (ℓ₁.eval n) → Bool) → Fin (ℓ₂.eval n) → Bool
def OracleIndist (O O' : OracleEnsemble) : Prop :=   -- with `langOf` generalised to ℓ₁/ℓ₂
  ∀ D : NUOraclePPT, Negligible fun n => distAdv (O.O n) (O'.O n) (D.oracleDist' n)

/-- [PS10, Definition 96.2]. -/
def PRFFamily := ∀ n, (Fin n → Bool) → (Fin n → Bool) → Fin n → Bool
def IsPRF (F : PRFFamily) : Prop :=
  PolyTimeComputable (fun w => List.ofFn (F (pairFstD w).length (decode (pairFstD w)) (decode (pairSndD w)))) ∧
  ∀ D : NUOraclePPT, Negligible fun n =>
    distAdv (F n) (randomFunction (Fin n → Bool) (Fin n → Bool)) (D.oracleDist n)
```
`[compiles]` (PRFFamily/IsPRF). The second conjunct is literally `prfAdv (F n) (tree of D)`
once the bridge below is in place.

### 5.2 Bridge to Garg's query trees (new, ≈ 300–400 lines)

```lean
theorem exists_queryTree (D : NUOraclePPT) (n : ℕ) :
    ∃ A : OracleAdversary (D.Coins n) (Fin n → Bool) (Fin n → Bool),
      A.BoundedBy (D.T.eval n) ∧ ∀ F r, oracleDist A F r = D.oracleDist n F r
```
Construction: by fuel recursion on the remaining `T n` steps, run the oracle machine until it
halts or enters `qQuery`; at a query with query string `w` (`OracleTM.queryString`), parse
`w` as `⟨x, 1^i⟩` (`pairDecode`); emit `QueryTree.query x (fun ans => continue in state
qYes/qNo according to ans i)`; malformed queries continue deterministically in `qNo`
(the language `langOf F` contains no malformed string, whatever `F`). This is exactly the
shape `QueryTree.simulate` expects (`OracleAdversary.lean:simulate`: `π (x,i) := x`,
`ans (x,i) o := o i`). The correctness lemma `eval_treeOf` is an induction on fuel using
`OracleTM.step_eq_of_ne_qQuery`; `BoundedBy` holds because a query consumes a step.

With it, `IsPRF F ↔ (… ∧ ∀ D, Negligible (fun n => prfAdv (F n) (treeOf D n)))`.

### 5.3 Efficiency condition imposed by the asymptotic layer

The query trees that count are **exactly those produced by an `NUOraclePPT`**; the query
bound is `T(n)` automatically. This is stronger than D7's "driven by an nuPPT with
polynomially many queries" and is the literal class. There is no separate "polynomially many
queries" hypothesis to audit.

### 5.4 Theorem 97.3 (GGM) and the cost of oracle *reductions*

`exists_ggmBits_dist` (Functions/GGM.lean:331) yields indices `i*, j*` (non-uniform advice,
C14) and the PRG distinguisher `ggmBitsDist G A q i j`, defined through `tableDist`/
`levelAdv` (lazy sampling: it answers `A`'s queries from a table of `q` PRG outputs it
builds *while* reading `A`'s queries). To present it as an `NUPPT` we must run the oracle
machine `D` and answer its queries by a **stateful** polynomial-time handler (the lazily
sampled table). Required new infrastructure:

```lean
/-- Oracle elimination with a stateful handler: for a fixed oracle machine and a polynomial-time
handler `h : state × query ↦ state × answer`, a plain machine simulating `M^{O_h}` where the
oracle's answers are produced by iterating `h`. -/
theorem exists_handlerSim (M : FinOracleTM) (h : List Bool → List Bool) (hh : PolyTimeComputable h) :
    ∃ (M' : FinTM Bool) (c : ℕ), ∀ x r s₀, M'.runCoins (pairEncode x s₀) r … = …
```
Construction sketch: `OracleTM.plainEmptyOracle` (Oracle.lean) shows the pattern of
replacing the query behaviour by a transition; here the replacement is a call: at `qQuery`,
copy the query tape to the handler's argument tape, `exists_installCallTM h` from the seam
(handler state is tape-resident in the argument), read the answer bit, resume in `qYes/qNo`.
Lockstep away from queries (`step_eq_of_ne_qQuery`), seam-to-seam at queries, `T` queries at
most. ≈ 1000–1500 lines; the heaviest single item of this design (§8).

**Fallback if prohibitive (named, not smeared).** Keep the literal definitions and the tree
bridge; prove 97.3 for the class of *next-query* adversaries (a PPT `step` mapping
`(1^n, history of answers)` to the next query or the output; the tree is its unfolding) and
state `oracleTM_iff_nextQuery` (both directions are the same handler-simulation work) as
the one admission. The plan's D7 is this fallback.

---

## 6. (e) Chapter 4: interaction

### 6.1 Literal ITMs versus next-message strategies

The text's ITM has seven tapes and rounds in which the active machine runs until it idles.
A literal rendering is definable (≈ 600–800 lines): two `FinTM`s with designated send tape
(the append-only output tape is a perfect send tape) and receive tape (a work tape — the
`Cfg` input tape is a type index and cannot grow — onto which the peer's last message is
written between rounds by configuration surgery), an idle state, `round`, `exec`, views, and
"time complexity t(|x|) in every interaction". But every protocol theorem would then be a
machine-run argument, and the ZK simulator "emulates V*, feeding it H and random coins,
and restarts" is a universal-machine-grade construction when V* is a machine parameter.
That is prohibitive.

**Chosen (D8, argued):** strategies are next-message functions; a strategy is *efficient* if
a PPT computes its next-message function **with the strategy's random tape as the
machine's coin tape** — i.e. the same `r` on tape 0 in every round, which is literally the
ITM's single random tape. The literal ITM becomes a derived notion with a (sorried-if-needed)
equivalence: `Strategy.ofITM`/`ITM.ofStrategy`; direction ITM → strategy is "re-run from
the start feeding the history" (≈ 800 lines of simulation), the other direction ≈ 400 lines.
I recommend stating neither in run 2: nothing in Chapter 4 consumes them.

### 6.2 Signatures `[compiles]`

```lean
/-- Self-delimiting encoding of a message list. -/
def encodeList : List (List Bool) → List Bool
  | [] => []
  | m :: ms => pairEncode m (encodeList ms)

/-- A strategy: common input, auxiliary input, random tape, messages received so far ↦ next
message (the value on the full history is the party's output). Coins: any function of `|x|`,
so unbounded provers may be arbitrarily randomised. -/
structure Strategy where
  coins : ℕ → ℕ
  next : (x z : List Bool) → (Fin (coins x.length) → Bool) → List (List Bool) → List Bool

abbrev Strategy.Coins (S : Strategy) (x : List Bool) : Type := Fin (S.coins x.length) → Bool

/-- Efficient strategy: a PPT computes `next`, with the strategy's random tape as its coin
tape, on input `⟨⟨x, z⟩, history⟩`. Deviation: time is polynomial in `|x| + |z| + |history|`
(the text: in `|x|` alone; see §6.5). -/
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
    if k % 2 = 0 then (e.1, e.2 ++ [P.A.next x z₁ r₁ e.1]) else (e.1 ++ [P.B.next x z₂ r₂ e.2], e.2)

/-- `view_B[A_{r₁}(x,z₁) ↔ B_{r₂}(x,z₂)] = (x, z₂, r₂, M_B)`. -/
def Protocol.viewB (P : Protocol) (x z₁ z₂) (r₁) (r₂) : List Bool × List Bool × List Bool × List (List Bool)
def Protocol.outB  (P : Protocol) (x z₁ z₂) (r₁) (r₂) : List Bool
```
Executions, transcripts (`(e.1, e.2)`), views and outputs are thus definitional; "random
executions" are `uprob` over `P.A.Coins x × P.B.Coins x`.

### 6.3 Interactive proofs, efficient provers `[compiles]`

```lean
structure NPRelation where            -- Appendix B witness relation
  rel : List Bool → List Bool → Prop
  wlen : Poly
  inP : {w | ∃ x y, w = pairEncode x y ∧ rel x y} ∈ Complexity.P
def NPRelation.lang (R : NPRelation) : Language Bool :=
  {x | ∃ y, y.length ≤ R.wlen.eval x.length ∧ R.rel x y}
-- `R.lang ∈ Complexity.NP` by `Complexity.mem_NP_iff_exists_length_le` (NP.lean:536), the
-- `≤`-length pairEncode form of the library's NP: a 30-line lemma.

/-- [PS10, Definition 116.1]. -/
structure IsInteractiveProof (Pv V : Strategy) (rounds : Poly) (L : Language Bool) : Prop where
  V_ppt : V.IsPPT
  complete : ∀ x ∈ L, ∃ y : List Bool, ∀ z,
    uprob (fun r : Pv.Coins x × V.Coins x => (⟨Pv, V, rounds⟩ : Protocol).outB x y z r.1 r.2 = [true]) = 1
  sound : ∃ e : ℕ → ℝ, Negligible e ∧ ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - e x.length < uprob (fun r : P'.Coins x × V.Coins x =>
      (⟨P', V, rounds⟩ : Protocol).outB x [] z r.1 r.2 = [false])

/-- [PS10, Definition 119.5]. -/
structure HasEfficientProver (Pv V : Strategy) (rounds : Poly) (R : NPRelation) : Prop where
  ip : IsInteractiveProof Pv V rounds R.lang
  P_ppt : Pv.IsPPT
  complete_witness : ∀ x y, R.rel x y → ∀ z, uprob (… outB x y z … = [true]) = 1
```
Quantifier audit: soundness has `∃ e` *before* `∀ x ∉ L, ∀ P*`, as in the text (the error
is uniform in the cheating prover); `P*` ranges over all strategies including randomised
ones (an averaging argument shows deterministic ones suffice — not needed). The malicious
prover gets no auxiliary input (`[]`), as the text says. Completeness "= 1" is
`uprob = 1`, i.e. for all coin pairs (`forall_of_uprob_eq_one`).

### 6.4 Zero knowledge, commitments `[compiles]`

```lean
/-- [PS10, Definition 121.1] with a strict PPT simulator (Deviation D8). -/
def HVZK (Pv V : Strategy) (rounds : Poly) (R : NPRelation) : Prop :=
  ∃ S : PPT, ∀ D : NUPPT, ∃ e : ℕ → ℝ, Negligible e ∧ ∀ x y z, R.rel x y → ∃ N,
    distAdv (fun r : Pv.Coins x × V.Coins x => encodeView ((⟨Pv, V, rounds⟩ : Protocol).viewB x y z r.1 r.2))
      (fun r => S.sampleAt N (pairEncode x z) r) (D.dist N) ≤ e x.length

/-- [PS10, Definition 121.2], strict-PPT simulator, `V*` any PPT strategy. -/
def ZK (Pv V : Strategy) (rounds : Poly) (R : NPRelation) : Prop :=
  ∀ V' : Strategy, V'.IsPPT → ∃ S : PPT, ∀ D : NUPPT, ∃ e : ℕ → ℝ, Negligible e ∧
    ∀ x y z, R.rel x y → ∃ N, distAdv (real view of V') (fun r => S.sampleAt N (pairEncode x z) r) (D.dist N) ≤ e x.length

/-- [PS10, Definition 126.3]. The text's binding clause omits `v₀ ≠ v₁` (as printed it is
unsatisfiable); inserted. -/
structure Commitment where
  com : List Bool → List Bool → List Bool
  l : Poly
  poly : PolyTimeComputable (fun w => com (pairFstD w) (pairSndD w))
structure Commitment.Secure (C : Commitment) : Prop where
  binding : ∀ n (v₀ v₁ : Fin n → Bool) (r₀ r₁ : Fin (C.l.eval n) → Bool), v₀ ≠ v₁ →
    C.com (List.ofFn v₀) (List.ofFn r₀) ≠ C.com (List.ofFn v₁) (List.ofFn r₁)
  hide : ∀ D : NUPPT, ∃ e, Negligible e ∧ ∀ n (v₀ v₁ : Fin n → Bool), ∃ N,
    distAdv (fun r => C.com (ofFn v₀) (ofFn r)) (fun r => C.com (ofFn v₁) (ofFn r)) (D.dist N) ≤ e n
```
(`hiding` is a Lean keyword; the field is `hide`.) The `∃ N` is the distinguisher's coin
budget: the length bound of the two samples, a function of `x, z` resp. `n`; it can be made
explicit (`encodeView` length ≤ polynomial in `|x| + |z|`), and should be at freeze time.

**Perfect zero knowledge.** The text's "perfect" ZK pairs with an *expected*-PPT simulator,
which finite coin strings cannot express (an unbounded number of attempts needs unbounded
coins and a measure). Cheapest faithful alternative: Goldreich's form —
```lean
/-- Perfect ZK with abort [Goldreich, Def. 4.3.1]: the simulator may output `⊥` with
probability ≤ 1/2, and conditioned on not aborting its output is identically distributed
to the view. Implies statistical ZK with error 2^{-n} by `n`-fold repetition (C7). -/
def PerfectZK (Pv V : Strategy) (rounds : Poly) (R : NPRelation) : Prop :=
  ∀ V' : Strategy, V'.IsPPT → ∃ S : PPT, ∀ x y z, R.rel x y →
    uprob (fun r => S.sample ⟨x,z⟩ r = abort) ≤ 1/2 ∧
    ∀ v, uprob (fun r => real view = v) = uprob (fun r => S.sample ⟨x,z⟩ r = encodeView v) / (1 - Pr[abort])
```
This is a *strengthening* in the simulator's resources (strict PPT), a weakening in the
conditioning; both recorded. Theorem 122.3 is stated with it (§6.6).

### 6.5 Deviations in this section, each with its reason

1. Time of a strategy polynomial in `|x| + |z| + |history|`, not in `|x|`: the text's bound
   makes a PPT `V*` unable to read a long `z`, and the simulator `S(x, z)` is "p.p.t." in the
   text with no statement of what that means; our reading is Goldreich's and is the one
   under which `S` calling `V*` is well-typed.
2. Rounds: a fixed `2·rounds(|x|)` alternation instead of "the active machine halts"; the
   text's protocols are all fixed-round.
3. Strict-PPT simulators; perfect ZK in the abort form.

### 6.6 Graph isomorphism: expressibility, Lemma 123.5, Theorem 122.3

Graphs on `n` vertices: `SimpleGraph (Fin n)` with `DecidableRel G.Adj`, encoded as the
`n²` adjacency bits; isomorphism `∃ σ : Equiv.Perm (Fin n), G₀.map σ.toEmbedding = G₁`
(`SimpleGraph.map`, Mathlib `Combinatorics/SimpleGraph/Maps.lean`, `[compiles]`).

Protocol 120.6 as strategies (`x = ⟨G₀, G₁⟩`, prover witness `z_P = σ`, three messages):
* `P.next x σ r [] := H := π(G₀)` with `π := permOfCoins n r`;
  `P.next x σ r [H, b] := if b = 0 then π else π ∘ σ⁻¹`;
* `V.next x z r [H] := [r 0]` (the bit `b`); `V.next x z r [H, b, γ] := [decide (γ(G_b) = H)]`.
* Simulator (Algorithm 123.4, one attempt): `b' ← bit`, `π ← permOfCoins`, `H := π(G_{b'})`,
  `b := V'.next x z r_V [H]`; output `(x, z, r_V, [H, [b'], π])` if `b = b'`, else `⊥`.

```lean
/-- [PS10, Lemma 123.5], first half: for `x ∈ L_iso`, `H = π(G_{b'})` with uniform `(b', π)`
is distributed as `π(G₀)` with uniform `π`. -/
theorem lemma_123_5_H {n} (G₀ G₁ : SimpleGraph (Fin n)) (hiso : graphIso G₀ G₁) (H : SimpleGraph (Fin n)) :
    uprob (fun w : Bool × Equiv.Perm (Fin n) => (if w.1 then G₁ else G₀).map w.2.toEmbedding = H) =
    uprob (fun π : Equiv.Perm (Fin n) => G₀.map π.toEmbedding = H)
-- proof: `uprob_bool_prod` + `uprob_comp_equiv (Equiv.mulRight σ)`.
/-- second half: `Pr[b' = b] = 1/2`, for every `V*`, since `b` depends only on `H`. -/
theorem lemma_123_5_b … : uprob (fun w => V'.next x z w.rV [encode (π(G_{b'}))] = [b']) = 1/2
```
**Audit finding (new):** with bit-coin PPT parties, "π ← S_n" is not samplable exactly
(`n!` is not a power of two for `n ≥ 3`). Consequences: (a) the concrete statements above
must take the permutation seed type `Equiv.Perm (Fin n)` (the concrete layer allows any
finite seed type) — this is how 123.5 is proved *as stated*; (b) the efficient prover and
the simulator sample `π` by rejection from bits (`permOfCoins`, a `(Fin ℓ → Bool) → Option
(Equiv.Perm (Fin n))` that is uniform conditioned on `some`, failure `≤ 2^{-n}`; machine
realisation ≈ 400–600 lines, a loop with a membership check); (c) **Theorem 122.3 cannot be
perfect with perfect completeness** for bit-coin parties: if the honest prover falls back to
a default permutation on sampling failure, the real view and the simulation differ by the
failure probability (the fallback breaks right-invariance of π's law), and if the prover
instead aborts, completeness drops to `1 - 2^{-n}`. Statement to freeze:
```lean
theorem gi_perfectZK_withAbort : PerfectZK giProver giVerifier ⟨1,0⟩ giRelation
  -- prover aborts on sampling failure (completeness 1 - 2^{-n}, recorded), OR
theorem gi_statisticalZK : StatZK (error 2^{-n}) …   -- prover falls back, completeness 1.
```
Both are honest readings of "perfect zero-knowledge interactive proof"; the panel should
pick one (I recommend the second plus the first as a remark, matching D8's "statistical").
The non-uniform-coin issue also affects the GNI verifier (Protocol 118.3) and the
3-colouring prover's random colour permutation (6 permutations: dyadic only by rejection).

Closure needed by the simulator: `V*` is a PPT strategy, so "feeding it H and coins" is an
install-call of its pair form (bridge (i)) with coins taken from the simulator's own coin
tape (C3); the `n`-attempt truncation is `exists_loopFindTM` (C7) with payload the view.

---

## 7. (f) The machine-closure lemmas, with their sources

Every lemma is stated on the D3 face (`PolyTimeComputable` on `pairEncode x r`, coins a
flat string of explicit polynomial length) and lifted through bridges (i)/(ii).

| id | closure lemma | status / source |
| --- | --- | --- |
| C1 | post-processing `Q ∘ A`, `Q` det. polytime | exists: `PolyTimeComputable.comp` (PolyTime.lean:131) |
| C2 | pre-processing `A ∘ P` keeping the coins: `⟨x,r⟩ ↦ ⟨P x, r⟩` | exists: `polyTimeComputable_pairSwap`, `PolyTimeComputable.pairMapSnd`, `.comp` (PolyTimePairing.lean) |
| C3 | coin splitting `r = r₁ ++ r₂` with `|r₁| = C(n+1)^c` known from `x` | **new primitive** `computesFunInTime_takeDropUnary : ⟨u, w⟩ ↦ ⟨w.take |u|, w.drop |u|⟩`, linear time, two tapes (≈ 300 lines); `u := 1^{ℓ(|x|)}` by `polyTimeComputable_polyUnary` |
| C4 | extra/unread coins | new `runCoins_eq_of_take` (§1.4, ≈ 80 lines) + concrete `acceptProb_fst`, `uprob_fst` |
| C5 | hard-wiring a string (advice) into a uniform machine | exists: `computesFunInTime_pairEncodeFixed`, `polyTimeComputable_const`, `PolyTimeComputable.pairEncode`; into a *sequence-form* machine: §2.2 (⇐) |
| C6 | advice pass-through / pairing of two advices | trivial on D4 (`pairEncode α₁ α₂`, `pairFstD/pairSndD`) |
| C7 | polynomially many fresh-coin calls, first success (Yao, GI simulator), with a polytime per-round body | `exists_loopFindTM` (Loop.lean:2633) + `exists_installCallTM` (:5645) for the body's calls + C3 + fuel `polyBits`; **new assembly** `Repetition.lean` ≈ 800–1200 lines; the round contract (`hstart`, positive duration, anchor exclusion, `Inv`) is the heavy part |
| C8 | same, concatenate all results (GL trials, multicopy samples, next-bit hybrids) | `exists_emitLoopTM` (:5508) + `exists_emitCallTM` (:5691); same assembly |
| C9 | majority vote of a polynomial number of bits | **new primitive** (two unary counters, linear) ≈ 250 lines, or a `CounterProg` program (`CounterProgPolyTime.lean`) |
| C10 | deterministic polytime computation as a PPT / as a call inside a PPT | `rightCfg_run` (Simulation.lean:287) embedding (≈ 150 lines); calls: `exists_installCallTM` |
| C11 | PPT computing with probability 1 ⇒ `PolyTimeComputable` | new ≈ 200 lines (install `1^T`, run from the seam) |
| C12 | Boolean post-processing (`= [true]`, negation, `ite`) | exists: `polyTimeComputable_ite`, `computesFunInTime_ifEq`, `polyTimeComputable_lenEq` |
| C13 | sampling an efficiently samplable ensemble `t-1` times inside a reduction | C8 with the sampler called per round |
| C14 | non-uniform index (hybrid `k`, GL `flip`, GGM `i*, j*`) | C5/C6 (advice `α(n) := encode k`); uniform `k ← [t]` is non-dyadic and is *not* used |
| C15 | length checks / output decoding `decodeBits` | exists: `polyTimeComputable_lenEq`, `pairLenCheck`, `ite` |
| C16a | oracle machine → query tree | new `exists_queryTree` (§5.2) ≈ 350 lines |
| C16b | oracle machine with a stateful polytime handler → plain machine | new `exists_handlerSim` (§5.4) ≈ 1000–1500 lines, highest risk |
| C17 | running a next-message PPT with chosen coins/messages; rewinding | free in the next-message model: a call (C10) with the same `r` |
| C18 | uniform permutation of `[n]` from bits, with abort | new ≈ 400–600 lines (loop + membership check), §6.6 |
| B1/B2 | bridges (i)/(ii) | new (§2.4) |
| B3 | `nuppt_seq_iff_advice` | new (§2.2) |

Everything "exists" was read in `ClassNP/PolyTimePairing.lean`, `TuringMachine/Composition.lean`,
`Build/Wrappers.lean` (`computesFunInTime_cond`), `Build/Loop.lean`, `Build/Primitives.lean`,
`Simulation.lean`, `CircuitComplexity/Advice.lean`, `TuringMachine/Universal.lean`,
`ClassNP/TMSAT.lean` (`timed_universal_quantitative`).

### Module layout proposed for the machine layer

```
TCSlib/Complexity/Randomized.lean              facade
TCSlib/Complexity/Randomized/Poly.lean         `Poly`, eval, mono, pos (≈ 80 lines)
TCSlib/Complexity/Randomized/PPT.lean          runCoins, PPT, sample(At), Computes, runCoins_eq_of_take,
                                               ppt_computes_iff (≈ 500)
TCSlib/Complexity/Randomized/NonUniform.lean   NUPPT, NUPPTSeq, SameBehaviour, nuppt_seq_iff_advice (≈ 300 defs + 1400 proof)
TCSlib/Complexity/Randomized/PairForm.lean     bridges (i)/(ii) (≈ 1500)
TCSlib/Complexity/Randomized/Closure.lean      C1–C6, C10–C12, C15 lifted (≈ 700)
TCSlib/Complexity/Randomized/Repetition.lean   C3 primitive, C7, C8, C9 (≈ 1500)
TCSlib/Complexity/Randomized/Oracle.lean       FinOracleTM, NUOraclePPT, langOf, exists_queryTree, (exists_handlerSim) (≈ 600 + 1200)
TCSlib/Cryptography/Asymptotic/…               as in the plan
TCSlib/Cryptography/ZeroKnowledge/…            as in the plan (Interaction.lean = §6.2)
```

---

## 8. (g) Risks, audit sensitivity, effort

### 8.1 Audit-sensitive quantifier shapes (what could make a definition vacuous or too strong)

1. `Poly.eval = C (n+1)^c`: never `0` for `C ≥ 1`; `C = 0` yields an empty machine class, not a
   vacuous security statement. `WeakOneWay` needs `0 < q.C` (else `1 - 1/0 = 1`). `Negligible`
   is on `ℝ` with `|·|`; all our advantages lie in `[0,1]`.
2. `halts` over coin tapes of length exactly `T |x|` (not all lists); longer tapes by lemma.
   Never quantify "for every `r : List Bool`" — too strong (blank-cell reads).
3. `sampleAt N` must only be used with `|x| ≤ N`; every definition fixes `N` as a length
   bound derived from the parameter (`advIn`, `len`, `encodeView` bound). An `N` smaller
   than the actual input length would silently run the machine with blanks as coins.
4. `NUPPT.advice_len` is `≤` (the text: "polynomial-length"); `=` would need padding lemmas
   for every construction (cf. `DTIMEAdvice`'s exact-length `α`, which forced
   `PPoly_eq_iUnion_DTIMEAdvice_pow` to be stated twice).
5. Def 69.4's `D(t)` gets no `1^n`; advice/time are in `|t|`. Supplying `1^n` is a
   strengthening of the adversary (weaker indistinguishability); do not mix.
6. Worst-case OWF (26.1): `A(f(x))` without `1^n`; strong/weak (27.3/28.4): with `1^n`.
7. Soundness: `∃ e` precedes `∀ x ∉ L ∀ P* ∀ z`; `P*` unrestricted (any `coins : ℕ → ℕ`).
   `outB = [false]` literal (a verifier emitting anything else is neither accepting nor
   rejecting; the honest verifiers always emit a bit).
8. Commitment binding needs `v₀ ≠ v₁` (source error).
9. `Ensemble.len` is a bound; `Regular` where the text says "over `{0,1}^{ℓ(n)}`".
10. Hybrid lemma needs `1 < m` (`exists_hybrid_gap` needs `0 < t`).
11. "Infinitely many `n`" is `∀ n₀, ∃ n ≥ n₀, …` (the form of `not_negligible_iff`); do not use
    `Filter.Frequently` in statements (harder to audit).
12. GI/GNI/3COL: uniform permutations are non-dyadic (§6.6); perfect completeness and perfect
    ZK cannot both hold literally with bit-coin parties.
13. `NUPPTSeq.size` strict `<` and time "`< d(i)`" rendered as "halted at `d(i)`".
14. Sanity theorems to include at skeleton time (they catch vacuity): `¬ StrongOneWay idFamily`
    (the trivial inverter is an `NUPPT`), `StrongOneWay F → WeakOneWay F`,
    `CompIndist X X`, `IsInteractiveProof` for the trivial NP protocol (`P` sends `y`).

### 8.2 Risks

* **R1 (medium-high)** Bridges (i)/(ii): bespoke lockstep simulations; the library's
  `capture_run`/`leftCfg_run`/`bufferedSecondCfg_run` are the templates, but the doubled-input
  decoder is new. If (i) fails, nothing downstream closes; mitigation: the definitions are
  unchanged and (i) is one admission.
* **R2 (medium)** `Repetition` (C7/C8): the loop combinator's round contract is demanding
  (positive duration, anchor exclusion, invariant); each body is itself a chain of
  install-calls whose seams must be composed exactly. The library has precedents
  (`computesFunInTime_splitSolveWith`'s body).
* **R3 (high)** `exists_handlerSim` (C16b) for oracle reductions. Fallback named (§5.4).
* **R4 (medium)** `nuppt_seq_iff_advice` (⇐): serialization bookkeeping; (⇒) conditional on
  `PolyBound c.canonizerTime` (hypothesis, precedent `TMSAT_mem_NP`).
* **R5 (low-medium)** Permutation sampling (C18) and the perfect-vs-statistical choice for
  122.3.
* **R6 (low)** Σ-type temptation: any agent who writes `(x : Fin n → Bool) × A.Coins |pairEncode 1^n (f x)|`
  gets a wrong measure; `sampleAt` must be the only entry point. Enforce by not exporting a
  dependent-coin sampler.

### 8.3 Effort (new Lean lines / agent-days), literal design versus the plan's baseline

| component | baseline (D3/D4/D7/D8) | literal (this design) | delta |
| --- | --- | --- | --- |
| Poly, PPT, samplers, `Computes` ⇔ polytime | 300 / 1 | 500 / 1.5 | +200 |
| NUPPT advice form | 150 / 0.5 | 150 / 0.5 | 0 |
| NUPPTSeq + equivalence | — | 1700 / 5 | +1700 |
| PairForm bridges | — | 1500 / 4 | +1500 |
| Closure C1–C6, C10–C12, C15 | 600 / 2 | 700 / 2 | +100 |
| Repetition C3, C7–C9 | 1500 / 5 | 1500 / 5 | 0 |
| Oracle defs + tree bridge | 300 / 1 | 600 / 2 | +300 |
| Oracle handler simulation (GGM reductions) | 1200 / 4 (also needed for next-query model's reductions) | 1200 / 4 | 0 |
| Ensembles/≈/closure/hybrid/prediction | 500 / 2 | 500 / 2 | 0 |
| OWF defs, 35.2, 35.1 | 700 / 3 | 700 / 3 | 0 |
| Interaction, IP, HVZK, ZK, commitment | 700 / 2 | 800 / 2.5 | +100 |
| GI protocol, 123.5, 122.3, C18 | 1200 / 4 | 1300 / 4.5 | +100 |
| **total** | ≈ 7.2k / 29 | ≈ 11.2k / 36 | ≈ +4k / +7 |

The literal premium is concentrated in two items (NUPPTSeq equivalence, PairForm bridges),
both of which degrade gracefully to a single named admission each.

---

## 9. Source errors and gaps found while designing (for the run-1 inventory)

* Definition 126.3 (binding) omits `v₀ ≠ v₁`; as printed, no scheme is binding.
* Definition 26.1 gives the adversary `f(x)` only, Definitions 27.3/28.4 give `(1^n, y)`; the
  two must not be unified silently (the text's own remark after 27.3 explains why).
* Definition 69.4's distinguisher has no `1^n`; Definition 75.2's predictor has (Remark 75.3).
* Definition 96.1: `{O'_n} ≈ {O'_n}` typo (already in the plan).
* Protocol 120.6 / Theorem 122.3: "π ← S_n" is not exactly samplable by a bit-coin PPT;
  perfect completeness and perfect ZK cannot both be literal (§6.6). Same for 118.3 (σ) and
  127.5 (the colour permutation).
* Definition 121.2 relies on expected polynomial time, which the finite-coin model cannot
  express; Goldreich's abort form is the faithful substitute.
* Section 4.4's time complexity "t(|x|) regardless of messages" makes the simulator's call to
  `V*` ill-defined for long `z`; the standard reading (time in total input length) is used.

## 10. What the orchestrator should freeze from this design (if adopted)

1. `Poly`, `Turing.FinTM.runCoins`, `PPT`, `PPT.sampleAt`, `NUPPT`, `NUPPTSeq`, `SameBehaviour`
   exactly as in `design-faithful-tapes-scratch.lean` (compiled).
2. The statement of `exists_pairForm` / `ofPairForm` / `nuppt_seq_iff_advice` as the three
   machine-layer headline theorems of run 2 (sorried under sketches), plus `runCoins_eq_of_take`
   and `ppt_computes_iff`.
3. `invSucc`, `StrongOneWay`, `WeakOneWay`, `WorstCaseOneWay` (literal `f(x)`-only input),
   `FunFamily.prod`, `weak_to_strong`.
4. `Ensemble`, `NUPPT.dist`, `CompIndist`, `Ensemble.map`, the hybrid/prediction shapes.
5. `FinOracleTM`, `NUOraclePPT`, `langOf`, `oracleDist`, `IsPRF`, `exists_queryTree`.
6. `Strategy`, `Strategy.IsPPT`, `Protocol`, `exec/viewB/outB`, `NPRelation`,
   `IsInteractiveProof`, `HasEfficientProver`, `HVZK`, `ZK`, `PerfectZK` (abort form),
   `Commitment(.Secure)`, `graphIso`.
