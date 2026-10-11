/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Machines.DblLang

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Random access to a general input in logarithmic space

A logspace machine reads its input at a position held in binary on a work tape [AB09, §4.1:
"a pointer into the input"]. The received `LogProg` layer has no such access for a general
(non-unary) input: the input instructions of `Complexity.LogProg.ARM` presuppose inputs
`⟨1ⁿ, w⟩` or `⟨1ⁿ, ⟨u, w⟩⟩`, and a call's virtual input is the whole input or its leading run
of `1`s followed by register words (P0 reception audit, `audits/ch34-p0-findings.md`). This
file supplies the missing piece twice, at the two levels later logspace programs use:

* **as a program fragment**: `Complexity.LogProg.readIn_run` reads bit `i` of the input,
  `i` held in binary on a register, into the control state (a counter register stepped up to
  `i` in lockstep with the input head, the received equality, increment, rewind and clear
  fragments), and restores everything else;
* **as a language pair**: `Complexity.implicitlyLogspaceComputable_id` — the bit and length
  languages of the identity, `Complexity.inputBitLang` and `Complexity.inputLenLang`, are in
  `L` — so an abstract register machine reads its own input at a register-held position by a
  `whole`-mode call with that register as its one argument (`Complexity.LogProg.vword_whole₁`,
  `Complexity.indicator_indexLang_pairEncode`).

Phase P4.4b of `AroraBarakChapters3-4Plan.md` (the B7 statement mini-phase, recorded in
`audits/ch4-p44-resolutions-addendum.md`). The fragment is campaign-owned and lives here,
not in `Machines/`, by decision D3; it is built only from received fragments.

## Main definitions

* `Complexity.LogProg.RdPh`, `Complexity.LogProg.readTr` — the phases and the transition
  table of the input-read fragment.
* `Complexity.inputBitLang`, `Complexity.inputLenLang` — `{⟨u, i⟩ | uᵢ = 1}` and
  `{⟨u, i⟩ | i < |u|}`.

## Main results

* `Complexity.LogProg.vword_whole₁` — a `whole` call with one argument presents `⟨u, V r⟩`.
* `Complexity.indicator_indexLang_pairEncode` — the answer of an `indexLang` decider on a
  genuine pair.
* `Complexity.pairEncode_ne_nil` — no pair is empty (so `[]` lies in no `indexLang`).
* `Complexity.LogProg.readIn_run` — the input-read fragment (sorried; phase-P4.4b
  statement).
* `Complexity.implicitlyLogspaceComputable_id` — input random access in `L` (sorried;
  phase-P4.4b statement), with `Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; §4.3, Definition 4.16.)
-/

namespace Complexity

open Turing

/-- No pair encoding is the empty word: `pairEncode x y` contains the separator. -/
theorem pairEncode_ne_nil (x y : List Bool) : pairEncode x y ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [length_pairEncode] at this

/-- **The answer of an index-language decider on a genuine pair**: the indicator of
`indexLang p` at `⟨u, bits v⟩` is the decision of `p u v`. -/
theorem indicator_indexLang_pairEncode (p : List Bool → ℕ → Prop) (u : List Bool) (v : ℕ) :
    MultiTapeTM.indicator (indexLang p : Set (List Bool)) (pairEncode u (Nat.bits v)) =
      @decide (p u v) (Classical.dec _) := by
  rw [LogProg.indicator_eq_decide]
  exact decide_eq_decide.mpr (pairEncode_mem_indexLang p u v)

namespace LogProg

/-- **A `whole`-mode call with one argument** presents the pair of the whole input and the
argument register's word: its virtual input is `⟨u, V r⟩`. -/
theorem vword_whole₁ {m d : ℕ} {Λ : Type} (u : List Bool) (j : Fin d) (r : Fin m) (l₁ l₀ : Λ)
    (V : Fin m → List Bool) :
    vword (callSegs ⟨j, .whole, [r], l₁, l₀⟩ u V) = pairEncode u (V r) := by
  simp [callSegs, Mode.seg0, argSegs, vword, render, pairEncode_eq_dbl]

/-! ## The input-read fragment -/

/-- The phases of the input-read fragment: the equality test of the counter with the index
(`eC`, `eBy`, `eBn`), the read (`yes`) or advance (`no`) step, the counter increment (`iC`,
`iB`), and, carrying the symbol read, the input rewind (`rw₁`, `rw₂`) and the counter clear
(`cR`, `cE`). -/
inductive RdPh where
  | eC | eBy | eBn
  | yes | no
  | iC | iB
  | rw₁ (a : Option Bool) | rw₂ (a : Option Bool)
  | cR (a : Option Bool) | cE (a : Option Bool)
  deriving DecidableEq, Fintype

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- **The transition table of the input-read fragment** on index register `r` and counter
register `s`, its phases embedded by `st` and its exits by `ex`. With the input head on
position `k + 1` (input symbol `k`) and the counter holding `bits k`: compare the counter with
the index (`eq_run`); if equal, take the symbol under the head; if not, stop at the right
blank, or else step the input head right and increment the counter (`inc_run`). Then rewind
the input head to position `1` (`rewind_x`) and clear the counter (`clr_run`), exiting into
`ex a` with the symbol `a` taken. -/
def readTr (r s : Fin m) (st : RdPh → Λ) (ex : Option Bool → Λ) :
    RdPh → Option Bool → (Fin m → Option Bool) → Action m Bool Λ
  | .eC, _, w => eqCAct s r (st .eC) (st .eBy) (st .eBn) (w s) (w r)
  | .eBy, _, w => eqBAct s r (st .eBy) (st .yes) (w s)
  | .eBn, _, w => eqBAct s r (st .eBn) (st .no) (w s)
  | .yes, a, _ => goAct (st (.rw₁ a))
  | .no, a, _ =>
    match a with
    | none => goAct (st (.rw₁ none))
    | some _ => xAct s 1 0 (st .iC)
  | .iC, _, w => incCAct s (st .iC) (st .iB) (w s)
  | .iB, _, w => incBAct s (st .iB) (st .eC) (w s)
  | .rw₁ a, _, _ => xAct s (-1) 0 (st (.rw₂ a))
  | .rw₂ a, b, _ => rw2Act s (st (.rw₂ a)) (st (.cR a)) b
  | .cR a, _, w => toEndAct s (st (.cR a)) (st (.cE a)) (w s)
  | .cE a, _, w => clrEAct s (st (.cE a)) (ex a) (w s)

section Read

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r s : Fin m) (hrs : r ≠ s)
  (st : RdPh → Λ) (ex : Option Bool → Λ)
  (htr : ∀ ph a w, P.tm.tr (st ph) a w = readTr r s st ex ph a w)
  (hc : ∀ ph, P.call (st ph) = none)

include hrs htr hc in
/-- **The input-read fragment** (phase P4.4b; spec, fill pending): from phase `eC`, with
`bits i` on the index register `r`, an empty counter register `s`, both heads on cell `0` and
the input head on position `1`, the program reaches the exit `ex x[i]?` — symbol `i` of the
input, `none` when `i ≥ |x|` — in the same configuration otherwise (registers, heads, input
position and output restored). Throughout, only registers `s` and `r` change (the tape of `s`,
the heads of both), both heads stay in `[-1, |bits (|x| + 1)|]`, and every state is an
ordinary fragment state: the fragment's space is these two ranges, independently of `i`.
A hand-built fragment: no received layer reads a general input at a register-held position
(the `Parse` fragments assume unary-first inputs).

**Proof sketch.** Induction on the counter value `k ≤ min i |x|`, the input head on position
`k + 1`. `eq_run` (with `r₁ := s`, so both heads stay within `|bits k|`) compares `bits k`
with `bits i`. If `k = i`, phase `yes` takes `inSym x (i + 1) = x[i]?`. Otherwise phase `no`
reads `inSym x (k + 1)`: at the right blank (`k = |x| < i`) the symbol taken is
`none = x[i]?`; on a letter (`k < |x|`) the head steps right and `inc_run` turns `bits k` into
`bits (k + 1)`, `k + 1 ≤ |x|`. Then `rewind_x` returns the input head to position `1`, and
`clr_run` empties the counter (its head within `|bits k|`). -/
theorem readIn_run (c : Cfg m Bool Λ x) (i : ℕ)
    (hr : c.workTapes r = FinTM.bufferTape (Nat.bits i)) (hs : c.workTapes s = FinTM.bufferTape [])
    (hrp : c.workTapePos r = 0) (hsp : c.workTapePos s = 0) (hip : c.inputPos.val = 1) :
    ∃ T, rrun P oracle { c with state := some (st .eC) } T = { c with state := some (ex x[i]?) } ∧
      ∀ t < T, ∃ (ph : RdPh) (ip : Fin (x.length + 2)) (f : ℤ → Option Bool) (q q' : ℤ),
        rrun P oracle { c with state := some (st .eC) } t =
          ⟨some (st ph), ip, Function.update c.workTapes s f,
            Function.update (Function.update c.workTapePos s q) r q', c.output⟩ ∧
        -1 ≤ q ∧ q ≤ (Nat.bits (x.length + 1)).length ∧
        -1 ≤ q' ∧ q' ≤ (Nat.bits (x.length + 1)).length := by
  sorry

end Read

end LogProg

/-! ## Input access as a language pair -/

/-- The bit language of the identity: `{⟨u, bits i⟩ | uᵢ = 1}` (`0`-based; `false` beyond the
end). -/
def inputBitLang : Language Bool := indexLang fun u i => u.getD i false = true

/-- The length language of the identity: `{⟨u, bits i⟩ | i < |u|}`. -/
def inputLenLang : Language Bool := indexLang fun u i => i < u.length

/-- **Input random access is logspace** (phase P4.4b; spec, fill pending): the identity is
implicitly logspace computable — its output bound is trivial and its two query languages,
`Complexity.inputBitLang` and `Complexity.inputLenLang`, are in `L`. [AB09, §4.1: a pointer
into the input] It is stated, and will be proved, as a corollary of
`Complexity.LogProg.readIn_run`.

**Proof sketch.** The bound is `|x| ≤ 1 · (|x| + 1)^1`. For the two languages, one call-free
register program with a mode bit, compiled against the empty bank `LogProg.Dbl.nilTM` as in
`LogProg.dblLang_mem` (`compile_space`): on `y`, validate `y = pairEncode z (bits r)` (an
aligned two-cell scan to the first aligned `[false, true]`, then a canonical tail — empty or
ending in `true`), reading each cell with `readIn_run`; reject otherwise. Then walk a counter
`k` over the pairs of `dbl z`, comparing `bits k` with the tail in lockstep (the comparison
pattern of `LogProg.cmpPlain_run`); on a match answer cell `2k` (resp. `true`), at the
separator answer `false`. Each register holds a counter of at most `|bits (|y| + 1)|` bits,
and `readIn_run` keeps every head within `[-1, |bits (|y| + 1)|]`. So each work tape visits
`O(logSpace |y|)` cells, its origin and the boundary cells included (an interval `[-1, W]` has
`W + 2` cells), and `compile_space` gives the space bound from these ranges. -/
theorem implicitlyLogspaceComputable_id : ImplicitlyLogspaceComputable id := by
  sorry

/-- `Complexity.inputBitLang` is in `L` (from `Complexity.implicitlyLogspaceComputable_id`). -/
theorem inputBitLang_mem : inputBitLang ∈ LOGSPACE := implicitlyLogspaceComputable_id.2.1

/-- `Complexity.inputLenLang` is in `L` (from `Complexity.implicitlyLogspaceComputable_id`). -/
theorem inputLenLang_mem : inputLenLang ∈ LOGSPACE := implicitlyLogspaceComputable_id.2.2

end Complexity
