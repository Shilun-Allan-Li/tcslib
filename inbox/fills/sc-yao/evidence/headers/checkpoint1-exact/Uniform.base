/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.Linarith
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import TCSlib.Complexity.CircuitComplexity.UnaryCode

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# P-uniform circuit families

[AB09, §6.2]: a circuit family is *P-uniform* when some polynomial-time machine, on input
`1ⁿ`, outputs the description of the `n`-th circuit [AB09, Def 6.12]. This needs a
string description of the book-model circuits `BoolCircuit.DAGCircuit`; this file fixes
one, a self-delimiting binary encoding, and proves it injective.

## Main definitions

* `BoolCircuit.DAGCircuit.encode` — the binary description of a `DAGCircuit n`: the
  number of inputs, the gate list, and the output vertex, every number in unary.
* `BoolCircuit.DAGCircuitFamily.IsPUniform` — some polynomial-time computable function
  maps `1ⁿ` to the description of `C n`. [AB09, Def 6.12]

## Main results

* `BoolCircuit.DAGCircuit.encode_injective` — distinct circuits have distinct
  descriptions; `BoolCircuit.DAGCircuit.eq_of_encode_eq` — the description also
  determines the number of inputs.
* `BoolCircuit.DAGCircuit.size_le_length_encode` — the description is at least as long
  as the circuit's size; `BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo` — for
  fan-in-two circuits it is at most `12 · size²`.
* `BoolCircuit.DAGCircuitFamily.IsPUniform.isPolySize` — a P-uniform family has
  polynomial size.

## Design and divergences from [AB09, §6.2]

* **The encoding.** [AB09] leaves "the description of the circuit" unspecified (and
  sketches an adjacency-matrix representation for Def 6.14). We encode a natural `k` as
  `1ᵏ0`, a list as `1 e₁ 1 e₂ … 1 eₘ 0`, a gate label in two bits, and a circuit as
  `code(n) · code(gates) · code(output)`. Unary numbers cost at most a polynomial factor
  over binary ones **for fan-in-two circuits** (`DAGCircuit.length_encode_le_of_isFaninTwo`:
  the description has length at most `12 · size²`, every vertex index being below the
  size); without a fan-in bound (or well-formedness) a gate's argument list may repeat
  vertices and the description is not bounded by any function of the size. Design note:
  any reasonable description is convertible to this one in polynomial time, so the
  choice should not affect P-uniformity; [AB09] makes no such robustness claim for
  Def 6.12 on pp. 106–115, and the library does not state one. (The robustness claim the
  book does make, for logspace uniformity under the adjacency-matrix description of
  Def 6.14, is proved for canonical families:
  `BoolCircuit.DAGCircuitFamily.isLogspaceUniform_iff` in `LogspaceUniformAdj`.)
* **Relation to `Encoding.lean`.** `TCSlib.Complexity.CircuitComplexity.Encoding` encodes
  the formula model `BoolCircuit.TreeCircuit` (for `CKT-SAT`); this file encodes the
  book-model `DAGCircuit`. Both write numbers with the unary code `BoolCircuit.encodeNat`
  of `UnaryCode.lean`.
* **Only the description map is constrained.** Def 6.12 asks only for the generating
  machine; fan-in two, well-formedness or polynomial size are separate predicates
  (`HasFaninTwo`, `IsWellFormed`, `IsPolySize`), and polynomial size follows
  (`IsPUniform.isPolySize`).
* **Thm 6.13.** The "if" direction of [AB09, Thm 6.13] (P-uniform circuits ⇒ `L ∈ P`) is
  `Language.mem_P_of_isPUniform` in `CircuitComplexity.PUniformP`; the converse
  (`L ∈ P` ⇒ P-uniform fan-in-two circuits, from the P-uniform form of [AB09, Thm 6.6],
  Remark 6.7) is `Language.exists_isPUniform_of_mem_P` in `CircuitComplexity.UniformTableau`,
  and the equivalence is `Language.mem_P_iff_exists_isPUniform`.
  Logspace-uniform families [AB09, Def 6.14] are `IsLogspaceUniform` in
  `LogspaceUniform.lean`, over the implicitly logspace-computable functions of
  `SpaceComplexity` (`ImplicitlyLogspaceComputable`, [AB09, Def 4.16]); [AB09, Thm 6.15] and
  the logarithmic-space half of [AB09, Remark 6.7] are
  `Language.mem_P_iff_exists_isLogspaceUniform` and `Complexity.tabFamily_isLogspaceUniform`
  in `LogspaceTableau.lean`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.2; Definitions 6.12 and 6.14, Theorem 6.13.)
-/

namespace BoolCircuit

/-- An encoder is *prefix-free* when an encoding followed by anything determines both the
encoded value and the rest. -/
private def PrefixFree {α : Type} (f : α → List Bool) : Prop :=
  ∀ a b (s t : List Bool), f a ++ s = f b ++ t → a = b ∧ s = t

/-- The code of a list: each element preceded by `1`, the whole followed by `0`. -/
def encodeList {α : Type} (f : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: as => true :: (f a ++ encodeList f as)

/-- The two-bit code of a gate label. -/
def GateKind.encode : GateKind → List Bool
  | .and => [false, false]
  | .or => [false, true]
  | .not => [true, false]

/-- The code of a gate: its label, then the list of vertices it reads. -/
def DAGGate.encode (g : DAGGate) : List Bool :=
  g.kind.encode ++ encodeList encodeNat g.args

/-- **The description of a circuit**: the number of inputs, the gates in order, and the
output vertex, numbers in unary (`BoolCircuit.encodeNat`). This is the string a
uniformity machine must output [AB09, Def 6.12]; see the module docstring for the
choice of representation. -/
def DAGCircuit.encode {n : ℕ} (C : DAGCircuit n) : List Bool :=
  encodeNat n ++ (encodeList DAGGate.encode C.gates ++ encodeNat C.output)

/-- The unary code `1ᵏ0` is prefix-free. -/
private lemma encodeNat_prefixFree : PrefixFree encodeNat := by
  intro a
  induction a with
  | zero =>
    intro b s t h
    cases b with
    | zero => simpa [encodeNat] using h
    | succ b => simp [encodeNat, List.replicate_succ] at h
  | succ a ih =>
    intro b s t h
    cases b with
    | zero => simp [encodeNat, List.replicate_succ] at h
    | succ b =>
      simp only [encodeNat, List.replicate_succ, List.cons_append, List.cons.injEq,
        true_and] at h
      obtain ⟨rfl, rfl⟩ := ih b s t (by simpa [encodeNat] using h)
      exact ⟨rfl, rfl⟩

/-- The list code of a prefix-free element code is prefix-free. -/
private lemma encodeList_prefixFree {α : Type} {f : α → List Bool} (hf : PrefixFree f) :
    PrefixFree (encodeList f) := by
  intro as
  induction as with
  | nil =>
    intro bs s t h
    cases bs with
    | nil => simpa [encodeList] using h
    | cons b bs => simp [encodeList] at h
  | cons a as ih =>
    intro bs s t h
    cases bs with
    | nil => simp [encodeList] at h
    | cons b bs =>
      simp only [encodeList, List.cons_append, List.cons.injEq, true_and,
        List.append_assoc] at h
      obtain ⟨rfl, h'⟩ := hf a b _ _ h
      obtain ⟨rfl, rfl⟩ := ih bs s t h'
      exact ⟨rfl, rfl⟩

/-- The two-bit gate-label code is prefix-free. -/
private lemma GateKind.encode_prefixFree : PrefixFree GateKind.encode := by
  intro a b s t h
  cases a <;> cases b <;> simp_all [GateKind.encode]

/-- The gate code (label, then argument list) is prefix-free. -/
private lemma DAGGate.encode_prefixFree : PrefixFree DAGGate.encode := by
  rintro ⟨k₁, as₁⟩ ⟨k₂, as₂⟩ s t h
  simp only [DAGGate.encode, List.append_assoc] at h
  obtain ⟨rfl, h'⟩ := GateKind.encode_prefixFree k₁ k₂ _ _ h
  obtain ⟨rfl, rfl⟩ := encodeList_prefixFree encodeNat_prefixFree as₁ as₂ s t h'
  exact ⟨rfl, rfl⟩

/-- The description determines the circuit, including its number of inputs: if two
circuits (possibly with different input counts) have the same description, the input
counts agree and so do the circuits.

**Proof sketch.** All three components are prefix-free codes, so equal descriptions
have equal input counts, equal gate lists and equal output vertices; a circuit is
determined by its gates and output (the other fields are proofs). -/
theorem DAGCircuit.eq_of_encode_eq {n₁ n₂ : ℕ} {C₁ : DAGCircuit n₁} {C₂ : DAGCircuit n₂}
    (h : C₁.encode = C₂.encode) : n₁ = n₂ ∧ C₁.gates = C₂.gates ∧ C₁.output = C₂.output := by
  obtain ⟨hn, h₁⟩ := encodeNat_prefixFree n₁ n₂ _ _ h
  obtain ⟨hg, h₂⟩ := encodeList_prefixFree DAGGate.encode_prefixFree _ _ _ _ h₁
  obtain ⟨ho, -⟩ := encodeNat_prefixFree _ _ [] [] (by simpa using h₂)
  exact ⟨hn, hg, ho⟩

/-- Distinct circuits on `n` inputs have distinct descriptions. -/
theorem DAGCircuit.encode_injective (n : ℕ) :
    Function.Injective (DAGCircuit.encode : DAGCircuit n → List Bool) := by
  intro C₁ C₂ h
  obtain ⟨-, hg, ho⟩ := DAGCircuit.eq_of_encode_eq h
  cases C₁
  cases C₂
  subst hg
  subst ho
  rfl

/-- A code of a list is longer than the list. -/
lemma length_encodeList_ge {α : Type} (f : α → List Bool) (as : List α) :
    as.length + 1 ≤ (encodeList f as).length := by
  induction as with
  | nil => simp [encodeList]
  | cons a as ih => simp only [encodeList, List.length_cons, List.length_append]; omega

/-- The description of a circuit is at least as long as its size (number of vertices,
inputs included). -/
theorem DAGCircuit.size_le_length_encode {n : ℕ} (C : DAGCircuit n) :
    C.size ≤ C.encode.length := by
  have := length_encodeList_ge DAGGate.encode C.gates
  simp only [DAGCircuit.size, DAGCircuit.encode, encodeNat, List.length_append,
    List.length_replicate, List.length_singleton]
  omega

/-- A list code is at most one plus (one more than the longest element code) per
element. -/
private lemma length_encodeList_le {α : Type} (f : α → List Bool) (B : ℕ) (as : List α)
    (h : ∀ a ∈ as, (f a).length ≤ B) :
    (encodeList f as).length ≤ as.length * (B + 1) + 1 := by
  induction as with
  | nil => simp [encodeList]
  | cons a as ih =>
    have ha := h a (List.mem_cons_self ..)
    have hs := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [encodeList, List.length_cons, List.length_append]
    nlinarith

/-- For fan-in-two circuits the description has length polynomial (quadratic) in the
size: `|encode C| ≤ 12 · size(C)²`. This is what makes the unary encoding harmless for
[AB09]'s circuits; without a fan-in bound a gate may list arbitrarily many (repeated)
arguments and the description is not bounded by any function of the size.

**Proof sketch.** Write `S` for the size; the output vertex is below `S`, so `S ≥ 1`.
Every argument is a vertex below `S`, so its unary code has length at most `S`; a gate
has at most two arguments, so its code has length at most `2S + 5`; the gate list (at
most `S` gates) has code length at most `S(2S + 6) + 1`; adding the codes of `n ≤ S` and
of the output (`≤ S + 1` each) gives at most `2S² + 8S + 2 ≤ 12S²`. -/
theorem DAGCircuit.length_encode_le_of_isFaninTwo {n : ℕ} (C : DAGCircuit n)
    (h : C.IsFaninTwo) : C.encode.length ≤ 12 * C.size ^ 2 := by
  have hS1 : 1 ≤ C.size := by have := C.output_lt; simp only [DAGCircuit.size]; omega
  -- every argument of every gate is a vertex below the size
  have hgate : ∀ g ∈ C.gates, g.encode.length ≤ 2 * C.size + 5 := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have hargs : ∀ a ∈ C.gates[i].args, (encodeNat a).length ≤ C.size := by
      intro a ha
      have := C.args_lt i hi a ha
      simp only [encodeNat, List.length_append, List.length_replicate,
        List.length_singleton, DAGCircuit.size]
      omega
    have hl := length_encodeList_le encodeNat C.size _ hargs
    have h2 := h.2 _ hg
    have hk : C.gates[i].kind.encode.length = 2 := by cases C.gates[i].kind <;> rfl
    simp only [DAGGate.encode, List.length_append, hk]
    nlinarith
  have hlist := length_encodeList_le DAGGate.encode _ C.gates hgate
  have hG : C.gates.length ≤ C.size := by simp only [DAGCircuit.size]; omega
  have hn : n ≤ C.size := by simp only [DAGCircuit.size]; omega
  have ho : C.output < C.size := C.output_lt
  simp only [DAGCircuit.encode, encodeNat, List.length_append, List.length_replicate,
    List.length_singleton]
  nlinarith

namespace DAGCircuitFamily

/-- **P-uniform circuit families** [AB09, Def 6.12]: a polynomial-time computable
function (`Complexity.PolyTimeComputable`, a machine running in time `C · (n + 1)^c`)
maps `1ⁿ` to the description `BoolCircuit.DAGCircuit.encode` of the `n`-th circuit.
The function's values on strings other than `1ⁿ` are unconstrained. -/
def IsPUniform (C : DAGCircuitFamily) : Prop :=
  ∃ f : List Bool → List Bool, Complexity.PolyTimeComputable f ∧
    ∀ n, f (List.replicate n true) = (C.circuit n).encode

/-- A P-uniform family has polynomial size. [AB09, §6.2]

**Proof sketch.** A polynomial-time function has polynomially bounded output length
(`Complexity.PolyTimeComputable.output_length_le`), and the size of a circuit is at
most the length of its description (`DAGCircuit.size_le_length_encode`); the input
`1ⁿ` has length `n`. -/
theorem IsPUniform.isPolySize {C : DAGCircuitFamily} (h : C.IsPUniform) : C.IsPolySize := by
  obtain ⟨f, hf, hC⟩ := h
  obtain ⟨A, c, hb⟩ := hf.output_length_le
  refine ⟨A, c, fun n => ?_⟩
  have hn := hb (List.replicate n true)
  rw [hC, List.length_replicate] at hn
  exact (DAGCircuit.size_le_length_encode _).trans hn

end DAGCircuitFamily

end BoolCircuit
