/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.CircuitComplexity.Advice

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Non-uniform PPT: the two formulations of Definition 26.8

[PS10, Definition 26.8] defines a non-uniform probabilistic polynomial-time machine in two
ways. **Machine-sequence form:** a sequence `A = {A₁, A₂, …}` of probabilistic machines with
a polynomial `d` such that `|Aᵢ| < d(i)` and the running time of `Aᵢ` is less than `d(i)`;
`A(x)` denotes the distribution obtained by running `A_{|x|}(x)`. **Advice form** ("alternatively"):
a uniform p.p.t. machine `A` that receives an advice string for each input length. The text
adds that "any adversarial algorithm `A` will implicitly be a non-uniform PPT", the standing
convention governing Definitions 26.1, 27.3, 28.4, 41.1(4), 56.1(5) and the hardness
assumptions.

The frozen definition is the advice form, `Complexity.NUPPT` of
`TCSlib.Complexity.Randomized.PPT` (foundation decision D4): `advice n` of length
`≤ adv.eval n`, run on `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The input-length-indexed activation
`A_{|y|}(y)` of the text is `NUPPT.runLit y r := runAt |y| y r` — the prefix `1^{|y|}` carries
no information — and it is the layout of the literal forms of Definition 26.1
(`WorstCaseOneWay`, `inverterLit`) and Definition 69.4 (`Ensemble.IndistLit`). The
machine-sequence form is reflected only as a sanity statement here: at every parameter `n`
the activation is a deterministic polynomial-time function of `(y, r)`
(`NUPPT.polyTimeComputable_runAtL`), i.e. each "`A_n`" is a polynomial-size machine.

**Deviation:** `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core
(optional module). The equivalence of the two forms (`NUPPTSeq`, `nuppt_seq_iff_advice`, with
`Turing.CodeTM.serialize` as the description size, `⇒` through `Turing.timed_universal`) is
the optional module `Randomized/Sequence.lean` with one named admission; no theorem of
chapters 2–4 depends on it.

This file also holds the uniformity lemmas (a PPT is an `NUPPT` with empty advice,
`Complexity.PPT` the subtype) and the **optional** sanity bridge to the library's
advice-taking machines `Turing.FinTM.DecidesWithAdviceInTime` [AB09, Definition 6.16]
(`NUPPT.decides_of_decidesWithAdviceInTime`, stated with its sketch; it needs the clocking
construction `NUPPT.ofPartial` and is off every critical path).

## Main definitions

* `Complexity.PPT.toNUPPT`, `Complexity.PPT.ofPolyTime` — the subtype API of PPTs.

## Main results

* `Complexity.NUPPT.runLit_eq_runAt`, `NUPPT.runLit_eq_runAtL` — the literal activation
  unfolds to the activation at parameter `|y|`.
* `Complexity.NUPPT.Uniform.advice_eq`, `NUPPT.Uniform.runAtL_eq`, `NUPPT.Uniform.runAt_eq`,
  `NUPPT.ofPolyTime_uniform` — uniform machines run on `⟨⟨⟨1^n, y⟩, []⟩, r⟩`.
* `Complexity.NUPPT.polyTimeComputable_runAtL` — at a fixed parameter the activation is a
  deterministic polynomial-time function of `(y, r)` (the "`A_n`" of the machine-sequence
  form).
* `Complexity.NUPPT.decides_of_decidesWithAdviceInTime` — (optional, sorried) a language
  decided with polynomial advice in polynomial time [AB09, Definition 6.16] is decided by an
  `NUPPT` at the input length.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1.3, Definition 26.8.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.3, Definition 6.16, machines with advice.)
-/

namespace Complexity

open Turing

namespace NUPPT

variable (A : NUPPT)

/-- The literal activation `A_{|y|}(y)` is the activation at parameter `|y|`
[PS10, Definition 26.8, "`A(x)` denotes `A_{|x|}(x)`"]. -/
theorem runLit_eq_runAt (y : List Bool) (r : A.Coins y.length) :
    A.runLit y r = A.runAt y.length y r := rfl

/-- The literal activation with the coins as a list. -/
theorem runLit_eq_runAtL (y : List Bool) (r : A.Coins y.length) :
    A.runLit y r = A.runAtL y.length y (List.ofFn r) := rfl

/-- A uniform machine has empty advice at every parameter. -/
theorem Uniform.advice_eq {A : NUPPT} (h : A.Uniform) (n : ℕ) : A.advice n = [] := h n

/-- A uniform machine runs on the layout `⟨⟨⟨1^n, y⟩, []⟩, r⟩`: the advice slot is empty. -/
theorem Uniform.runAtL_eq {A : NUPPT} (h : A.Uniform) (n : ℕ) (y r : List Bool) :
    A.runAtL n y r = A.output (pairEncode (pairEncode (advInput n y) []) r) := by
  simp [runAtL, h n]

/-- A uniform machine runs on the layout `⟨⟨⟨1^n, y⟩, []⟩, r⟩` (typed coins). -/
theorem Uniform.runAt_eq {A : NUPPT} (h : A.Uniform) (n : ℕ) (y : List Bool) (r : A.Coins n) :
    A.runAt n y r = A.output (pairEncode (pairEncode (advInput n y) []) (List.ofFn r)) := by
  rw [NUPPT.runAt_eq, h.runAtL_eq]

/-- `ofPolyTime` with an everywhere-empty advice function is uniform. -/
theorem ofPolyTime_uniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (h : ∀ n, advice n = []) : (ofPolyTime hf coins adv advice hα).Uniform := h

/-- Uniformity is the conjunction of the advice clauses (definitional unfolding). -/
theorem uniform_iff : A.Uniform ↔ ∀ n, A.advice n = [] := Iff.rfl

/-- The literal activation of a uniform polynomial-time machine is `f` on
`⟨⟨⟨1^{|y|}, y⟩, []⟩, r⟩`. -/
theorem runLit_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) (y : List Bool) (r : (ofPolyTimeUniform hf coins).Coins y.length) :
    (ofPolyTimeUniform hf coins).runLit y r =
      f (pairEncode (pairEncode (advInput y.length y) []) (List.ofFn r)) := by
  rw [runLit_eq_runAtL, runAtL_ofPolyTimeUniform]

/-- **The machine-sequence view, sanity direction.** At a fixed parameter `n`, the activation
of `A` is a deterministic polynomial-time function of the pair `⟨y, r⟩`: the "`A_n`" of
[PS10, Definition 26.8]'s first formulation is a polynomial-size machine (the advice `advice n`
and the prefix `1^n` are hard-wired constants).

**Proof sketch.** The raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` is assembled from `⟨y, r⟩` by
`PolyTimeComputable.pairEncode` with the constant strings `1^n` and `advice n`
(`polyTimeComputable_const`) and the projections `pairFstD`/`pairSndD`; then
`NUPPT.polyTimeComputable_output`. -/
theorem polyTimeComputable_runAtL (n : ℕ) :
    PolyTimeComputable fun z => A.runAtL n (pairFstD z) (pairSndD z) := by
  have h := A.polyTimeComputable_output.comp
    ((((polyTimeComputable_const (List.replicate n true)).pairEncode
      polyTimeComputable_pairFstD).pairEncode (polyTimeComputable_const (A.advice n))).pairEncode
      polyTimeComputable_pairSndD)
  convert h using 1

/-- **Optional sanity bridge** (not on the critical path): a language decided by a machine
with polynomial-length advice within polynomial time [AB09, Definition 6.16]
(`Turing.FinTM.DecidesWithAdviceInTime`) is decided by an `NUPPT` activated at the input
length, i.e. by a non-uniform PPT in the sense of [PS10, Definition 26.8]. The two advice
notions agree: `α n` becomes the advice at parameter `n` and the time bound in `|x|` becomes
a bound in the machine-input length.

**Proof sketch.** The hypothesis bounds `M` only on the well-formed inputs
`pairEncode x (α |x|)`; the `NUPPT` must halt on every input, so `M` is first clocked:
`Turing.timed_universal` run on `⟨⟨bits (C (m+1)^c), code M⟩, w⟩` halts on every `w`
within a polynomial of `|w|` and agrees with `M` whenever `M` halts within the clock
(this is the optional lemma `NUPPT.ofPartial`). The `NUPPT` `A` has advice `α n` (length
`Ca (n+1)^ca = (normal Ca ca).eval n`, so `adv := normal Ca ca`), no coins (`coins := const 0`),
and output function `z ↦ clockedM (pairEncode (inArg z) (inAdvice z))` where `inArg`/`inAdvice`
are the projections of the raw layout (FP by the pairing calculus). On the raw input
`⟨⟨⟨1^{|x|}, x⟩, α |x|⟩, r⟩` the re-pairing is `pairEncode x (α |x|)`, on which `M` halts within
`C (|x|+1)^c` with output `[indicator L x]` (hypothesis `h x`), so the clocked machine returns
the same by determinism (`NUPPT.output_eq_of_computesInTime`). -/
theorem decides_of_decidesWithAdviceInTime (M : FinTM Bool) (L : Language Bool)
    (α : ℕ → List Bool) (C c Ca ca : ℕ) (hα : ∀ n, (α n).length = Ca * (n + 1) ^ ca)
    (h : M.DecidesWithAdviceInTime L α (fun n => C * (n + 1) ^ c)) :
    ∃ A : NUPPT, ∀ x (r : A.Coins x.length),
      A.runAt x.length x r = [MultiTapeTM.indicator (L : Set (List Bool)) x] := by
  sorry

end NUPPT

namespace PPT

/-- The underlying non-uniform machine of a PPT. -/
def toNUPPT (A : PPT) : NUPPT := A.1

/-- A PPT has empty advice. -/
theorem uniform (A : PPT) : A.toNUPPT.Uniform := A.2

/-- The PPT with output function `f` and coin polynomial `coins`
(`Complexity.NUPPT.ofPolyTimeUniform`). -/
noncomputable def ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : PPT :=
  ⟨NUPPT.ofPolyTimeUniform hf coins, NUPPT.ofPolyTimeUniform_uniform hf coins⟩

/-- The underlying machine of `PPT.ofPolyTime hf coins` is `NUPPT.ofPolyTimeUniform hf coins`. -/
theorem toNUPPT_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTime hf coins).toNUPPT = NUPPT.ofPolyTimeUniform hf coins := rfl

end PPT

end Complexity
