/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.UnaryArith
import TCSlib.Cryptography.ZeroKnowledge.Encoding
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The 3-colouring witness of the gadget graph

A satisfying assignment of a 3-CNF gives an explicit proper 3-colouring of the gadget graph
`gadgetGraph K mem` (`LevinHardness/Gadget.lean`), and the encoded colouring is a
polynomial-time function of the pair `⟨s, a⟩` of the formula word and the assignment word.

**Overlap (disclosed, brief EF-H12 item (b)).** The colouring `gadgetColor` re-derives, for the
`Fin N` layout of `Gadget.lean`, the completeness colouring of the course reduction
(`SATtoColor.SATtoColorCompleteness`, `Complexity/NPReductions/ThreeSATToColoring.lean:193`,
whose colourings `sat3Coloring` and `clauseGadgetColor` are private there): the palette vertex
`p` gets colour `p`, a literal node gets `1` if the literal is true and `2` otherwise, and the six
nodes of a clause gadget get the colours of the course table `clauseGadgetColor`
(`gadgetNodeColor` here). The proof that it is proper is redone here by a case analysis over the
edge families of `gadgetEdge`.

## Main definitions

* `TCSlib.Cryptography.LevinHardness.gadgetNodeColor` — the colours of the six gadget nodes.
* `TCSlib.Cryptography.LevinHardness.gadgetColor` — the colouring of the gadget graph.
* `TCSlib.Cryptography.LevinHardness.colorWord` — the encoded colouring of `⟨s, a⟩`.

## Main results

* `TCSlib.Cryptography.LevinHardness.properColoring_gadgetColor` — the colouring is proper
  when every clause of the formula is satisfied.
* `TCSlib.Cryptography.LevinHardness.threeColorable_gadgetGraph` — hence the gadget graph is
  3-colourable.
* `TCSlib.Cryptography.LevinHardness.polyTimeComputable_colorWord` — the witness map
  `⟨s, a⟩ ↦ colorWord s a` is polynomial-time.

## References

* CS 294-268 course material (UC Berkeley, Spring 2026, V. Guruswami), the 3SAT → 3-colouring
  reduction as formalized in `Complexity/NPReductions/ThreeSATToColoring.lean`.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.3.)
-/

namespace TCSlib.Cryptography.LevinHardness

open Complexity TCSlib.Cryptography.EncodingMachines

/-! ### The colouring -/

/-- **The colours of the six nodes of a clause gadget** whose literals have the truth values
`a, b, c`, at index `i` (re-derived from the course table `clauseGadgetColor`,
`ThreeSATToColoring.lean`): node `5` gets `1`; if `a = b = c = false` every other node gets `0`;
if `a = b = false` the nodes `4, 3, 2, 1, 0` get `2, 0, 2, 1, 0`; otherwise they get
`0, 2, 1, (b ? 2 : 0), (a ∧ ¬b ? 2 : 0)`. -/
def gadgetNodeColor (a b c : Bool) (i : ℕ) : Fin 3 :=
  if i = 5 then 1
  else if (!a && !b && !c) = true then 0
  else if (!a && !b) = true then
    (if i = 4 then 2 else if i = 3 then 0 else if i = 2 then 2 else if i = 1 then 1 else 0)
  else
    (if i = 4 then 0 else if i = 3 then 2 else if i = 2 then 1
     else if i = 1 then (if (!b) = true then 0 else 2)
     else (if (!a) = true then 0 else if (!b) = true then 2 else 0))

/-- The defining equation of `gadgetNodeColor` (see its docstring for the table). -/
theorem gadgetNodeColor_eq (a b c : Bool) (i : ℕ) :
    gadgetNodeColor a b c i =
      if i = 5 then 1
      else if (!a && !b && !c) = true then 0
      else if (!a && !b) = true then
        (if i = 4 then 2 else if i = 3 then 0 else if i = 2 then 2 else if i = 1 then 1 else 0)
      else
        (if i = 4 then 0 else if i = 3 then 2 else if i = 2 then 1
         else if i = 1 then (if (!b) = true then 0 else 2)
         else (if (!a) = true then 0 else if (!b) = true then 2 else 0)) := rfl

/-- **The 3-colouring of the gadget graph** from the assignment `val` (re-derived, for the
`Fin N` layout, from the completeness colouring `sat3Coloring` of the course reduction): the
palette `t < 3` gets colour `t`; the literal node `3 + ℓ` gets `1` if `litVal val ℓ` and `2`
otherwise; gadget node `i` of clause code `c` (vertex `3 + 2K + 6c + i`) gets
`gadgetNodeColor` of the truth values of the clause's three literals at `i`. -/
def gadgetColor (K : ℕ) (val : ℕ → Bool) (t : ℕ) : Fin 3 :=
  if t = 0 then 0 else if t = 1 then 1 else if t = 2 then 2
  else if t < 3 + 2 * K then (if litVal val (t - 3) = true then 1 else 2)
  else gadgetNodeColor (litVal val (clauseLit K ((t - (3 + 2 * K)) / 6) 0))
    (litVal val (clauseLit K ((t - (3 + 2 * K)) / 6) 1))
    (litVal val (clauseLit K ((t - (3 + 2 * K)) / 6) 2)) ((t - (3 + 2 * K)) % 6)

/-- The defining equation of `gadgetColor` (see its docstring for the cases). -/
theorem gadgetColor_eq (K : ℕ) (val : ℕ → Bool) (t : ℕ) :
    gadgetColor K val t =
      if t = 0 then 0 else if t = 1 then 1 else if t = 2 then 2
      else if t < 3 + 2 * K then (if litVal val (t - 3) = true then 1 else 2)
      else gadgetNodeColor (litVal val (clauseLit K ((t - (3 + 2 * K)) / 6) 0))
        (litVal val (clauseLit K ((t - (3 + 2 * K)) / 6) 1))
        (litVal val (clauseLit K ((t - (3 + 2 * K)) / 6) 2)) ((t - (3 + 2 * K)) % 6) := rfl

/-- The palette vertex `t < 3` has colour `t`: `(gadgetColor K val t : ℕ) = t`. -/
theorem gadgetColor_val_of_lt_three (K : ℕ) (val : ℕ → Bool) {t : ℕ} (ht : t < 3) :
    (gadgetColor K val t : ℕ) = t := by
  rw [gadgetColor_eq]
  interval_cases t <;> rfl

/-- The literal node `t` (`3 ≤ t < 3 + 2K`) has colour `1` if `litVal val (t - 3)` and `2`
otherwise. -/
theorem gadgetColor_of_lit (K : ℕ) (val : ℕ → Bool) {t : ℕ} (h3 : 3 ≤ t)
    (hL : t < 3 + 2 * K) :
    gadgetColor K val t = if litVal val (t - 3) = true then 1 else 2 := by
  rw [gadgetColor_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hL]

/-- A gadget vertex `t ≥ 3 + 2K` has colour `gadgetNodeColor` of the truth values of the three
literals of its clause code `(t - (3 + 2K)) / 6`, at index `(t - (3 + 2K)) % 6`. -/
theorem gadgetColor_of_gadget (K : ℕ) (val : ℕ → Bool) {t : ℕ} (hL : 3 + 2 * K ≤ t) :
    gadgetColor K val t =
      gadgetNodeColor (litVal val (clauseLit K ((t - (3 + 2 * K)) / 6) 0))
        (litVal val (clauseLit K ((t - (3 + 2 * K)) / 6) 1))
        (litVal val (clauseLit K ((t - (3 + 2 * K)) / 6) 2)) ((t - (3 + 2 * K)) % 6) := by
  rw [gadgetColor_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-! ### The colouring is proper, edge family by edge family -/

/-- Glue. Inside the gadget of a satisfied clause, the seven internal edges get distinct
colours: `(i, j)` in the internal pair list and `a ∨ b ∨ c` give
`gadgetNodeColor a b c i ≠ gadgetNodeColor a b c j`. -/
private theorem gadgetNodeColor_ne_internal {a b c : Bool} (habc : (a || b || c) = true)
    {i j : ℕ} (hij : (i, j) ∈ [(0, 1), (0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (4, 5)]) :
    gadgetNodeColor a b c i ≠ gadgetNodeColor a b c j := by
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hij
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert habc <;> revert a b c <;> decide

/-- Glue. The three literal–gadget edges get distinct colours, for any truth values:
the first literal against node `0`, the second against node `1`, the third against node `4`. -/
private theorem litColor_ne_gadgetNodeColor (a b c : Bool) :
    ((if a = true then 1 else 2 : Fin 3) ≠ gadgetNodeColor a b c 0) ∧
    ((if b = true then 1 else 2 : Fin 3) ≠ gadgetNodeColor a b c 1) ∧
    ((if c = true then 1 else 2 : Fin 3) ≠ gadgetNodeColor a b c 4) := by
  revert a b c; decide

/-- Glue. One orientation of each edge of the gadget graph joins two vertices of distinct
colours, when every clause of the formula is satisfied: `t ≠ t'` and
`gadgetEdge K mem t t' = true` give `gadgetColor K val t ≠ gadgetColor K val t'`.

**Proof sketch.** Split `gadgetEdge_eq` into its six edge families. Palette edges: the colours
are the vertices themselves. Base–literal: `0` against `1` or `2`. Positive–negative literal:
the two literal codes `2v, 2v + 1` have opposite `litVal`. Internal gadget edges: both ends lie
in the gadget of the same clause code `c`, which is in the formula and hence satisfied, so
`gadgetNodeColor_ne_internal`. Literal–gadget edges: the literal's colour is the colour of the
matching truth value, `litColor_ne_gadgetNodeColor`. Node `5` (colour `1`) against the base
(`0`) and the false node (`2`). -/
private theorem gadgetColor_ne_of_edge {K : ℕ} {mem : ℕ → Bool} {val : ℕ → Bool}
    (hsat : ∀ c, mem c = true → clauseSat K val c = true) {t t' : ℕ} (hne : t ≠ t')
    (h : gadgetEdge K mem t t' = true) : gadgetColor K val t ≠ gadgetColor K val t' := by
  rw [gadgetEdge_eq] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (((((⟨ht, ht'⟩ | ⟨⟨rfl, h3⟩, hL⟩) | ⟨⟨⟨h3, hL⟩, hev⟩, rfl⟩) | h4) | h5) | h6)
  · intro heq
    have := congrArg Fin.val heq
    rw [gadgetColor_val_of_lt_three K val ht, gadgetColor_val_of_lt_three K val ht'] at this
    exact hne this
  · rw [gadgetColor_of_lit K val h3 hL]
    intro heq
    have := congrArg Fin.val heq
    rw [gadgetColor_val_of_lt_three K val (by omega)] at this
    split_ifs at this <;> simp at this
  · rw [gadgetColor_of_lit K val h3 hL, gadgetColor_of_lit K val (by omega) (by omega)]
    have hneg : litVal val (t + 1 - 3) = !litVal val (t - 3) := by
      rw [litVal_eq, litVal_eq, if_neg (by omega), if_pos hev,
        show (t + 1 - 3) / 2 = (t - 3) / 2 by omega]
    rw [hneg]
    cases litVal val (t - 3) <;> decide
  · obtain ⟨⟨⟨⟨⟨⟨hLt, -⟩, hLt'⟩, -⟩, hq⟩, hm⟩, hij⟩ := h4
    rw [gadgetColor_of_gadget K val hLt, gadgetColor_of_gadget K val hLt', ← hq]
    have hc := hsat _ hm
    rw [clauseSat_eq] at hc
    exact gadgetNodeColor_ne_internal hc hij
  · obtain ⟨⟨⟨⟨h3, hL⟩, hLt'⟩, -⟩, hj⟩ := h5
    rw [gadgetColor_of_lit K val h3 hL, gadgetColor_of_gadget K val hLt']
    rcases hj with (⟨he, hi⟩ | ⟨he, hi⟩) | ⟨he, hi⟩ <;> rw [he, hi]
    · exact (litColor_ne_gadgetNodeColor _ _ _).1
    · exact (litColor_ne_gadgetNodeColor _ _ _).2.1
    · exact (litColor_ne_gadgetNodeColor _ _ _).2.2
  · obtain ⟨⟨⟨hLt, -⟩, h5⟩, h02⟩ := h6
    rw [gadgetColor_of_gadget K val hLt, h5, gadgetNodeColor_eq, if_pos rfl]
    intro heq
    have := congrArg Fin.val heq
    rcases h02 with rfl | rfl <;>
      rw [gadgetColor_val_of_lt_three K val (by omega)] at this <;> simp at this

/-- **The colouring `gadgetColor` is proper** (completeness colouring of the 3SAT → 3COL
reduction, re-derived for the `Fin N` layout from `SATtoColor.SATtoColorCompleteness`,
`ThreeSATToColoring.lean`): if every clause code in the formula (`mem c = true`) is satisfied by
`val` (`clauseSat K val c = true`), then
`ProperColoring (gadgetGraph K mem) (fun u => gadgetColor K val u)`. Gadgets of clause codes
outside the formula carry no internal edges, and their edges to literals, base and false node
are properly coloured for any truth values. -/
theorem properColoring_gadgetColor (K : ℕ) (mem : ℕ → Bool) (val : ℕ → Bool)
    (hsat : ∀ c, mem c = true → clauseSat K val c = true) :
    ProperColoring (gadgetGraph K mem) (fun u => gadgetColor K val u) := by
  rw [ProperColoring_iff]
  intro u v huv
  rw [gadgetGraph_apply, gadgetAdj_eq] at huv
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at huv
  obtain ⟨hne, he | he⟩ := huv
  · exact gadgetColor_ne_of_edge hsat hne he
  · exact fun heq => gadgetColor_ne_of_edge hsat (Ne.symm hne) he heq.symm

/-- **The gadget graph of a satisfied formula is 3-colourable**: if
`∀ c, mem c = true → clauseSat K val c = true`, then `ThreeColorable (gadgetGraph K mem)`,
witnessed by `gadgetColor K val` (`properColoring_gadgetColor`). -/
theorem threeColorable_gadgetGraph (K : ℕ) (mem : ℕ → Bool) (val : ℕ → Bool)
    (hsat : ∀ c, mem c = true → clauseSat K val c = true) :
    ThreeColorable (gadgetGraph K mem) :=
  (threeColorable_iff _).2 ⟨_, properColoring_gadgetColor K mem val hsat⟩

/-! ### The encoded colouring -/

/-- **The witness string of the gadget graph**: for the formula word `s` (with `K = |s|`
variables) and the assignment word `a` (read with default `false`),
`colorWord s a = encColoring (fun u : Fin (gadgetN |s|) => gadgetColor |s| (a.getD · false) u)`,
the encoding of the colouring `gadgetColor` (re-derived from the course completeness
colouring). -/
def colorWord (s a : List Bool) : List Bool :=
  encColoring (fun u : Fin (gadgetN s.length) =>
    gadgetColor s.length (fun v => a.getD v false) u)

/-- The defining equation of `colorWord`. -/
theorem colorWord_eq (s a : List Bool) :
    colorWord s a = encColoring (fun u : Fin (gadgetN s.length) =>
      gadgetColor s.length (fun v => a.getD v false) u) := rfl

/-- Glue. The two bits `[x / 2 = 1, x % 2 = 1]` of a colour in the layout of `encColoring`. -/
private def colorBits (x : Fin 3) : List Bool := [decide (x.val / 2 = 1), decide (x.val % 2 = 1)]

/-- Glue. Concatenating the two bits of the colours `g 0, …, g (n - 1)` gives
`encColoring (fun u : Fin n => g u)`.

**Proof sketch.** By induction on `n` (`List.range_succ`, `List.getD_append`,
`List.getD_append_right`) the concatenation has length `2n` and bits `2i`, `2i + 1` equal to the
two bits of `g i`; these are the bits of `encColoring` (`getD_encColoring_two_mul`,
`getD_encColoring_two_mul_add_one`, `length_encColoring`), so the lists agree
(`List.ext_getElem`). -/
private theorem flatMap_colorBits (g : ℕ → Fin 3) (n : ℕ) :
    (List.range n).flatMap (fun t => colorBits (g t)) = encColoring (fun u : Fin n => g u) := by
  have hlen : ∀ n, ((List.range n).flatMap (fun t => colorBits (g t))).length = 2 * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append, ih]
      simp [colorBits]
      ring
  have hget : ∀ n i, i < n →
      ((List.range n).flatMap (fun t => colorBits (g t))).getD (2 * i) false =
        decide ((g i).val / 2 = 1) ∧
      ((List.range n).flatMap (fun t => colorBits (g t))).getD (2 * i + 1) false =
        decide ((g i).val % 2 = 1) := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      rcases Nat.lt_or_ge i n with h | h
      · rw [List.getD_append _ _ _ _ (by rw [hlen]; omega),
          List.getD_append _ _ _ _ (by rw [hlen]; omega)]
        exact ih i h
      · obtain rfl : i = n := by omega
        rw [List.getD_append_right _ _ _ _ (by simp [hlen]),
          List.getD_append_right _ _ _ _ (by simp [hlen]), hlen]
        simp [colorBits]
  have hgetD : ∀ (l : List Bool) (m : ℕ) (h : m < l.length), l[m] = l.getD m false :=
    fun l m h => by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  refine List.ext_getElem (by rw [hlen, length_encColoring]; ring) fun m h1 h2 => ?_
  rw [hgetD _ _ h1, hgetD _ _ h2]
  rw [hlen] at h1
  rcases Nat.even_or_odd' m with ⟨i, rfl | rfl⟩
  · have := getD_encColoring_two_mul (fun u : Fin n => g u) ⟨i, by omega⟩
    rw [(hget n i (by omega)).1, this]
  · have := getD_encColoring_two_mul_add_one (fun u : Fin n => g u) ⟨i, by omega⟩
    rw [(hget n i (by omega)).2, this]

/-! ### The witness map is polynomial-time -/

/-- Glue. The two bits of the gadget-node colour are a polynomial-time function of the three
truth values (one-bit tests) and the index (unary):
`x ↦ colorBits (gadgetNodeColor (a x) (b x) (c x) (i x))`, an `ite` tree of constants
(`polyTimeComputable_ite`, `polyTimeComputable_and`, `polyTimeComputable_not`,
`EncodingMachines.eqTest_poly`). -/
private theorem gadgetNodeColorBits_poly {a b c : List Bool → Bool} {i : List Bool → ℕ}
    (ha : PolyTimeComputable fun x => [a x]) (hb : PolyTimeComputable fun x => [b x])
    (hc : PolyTimeComputable fun x => [c x])
    (hi : PolyTimeComputable fun x => List.replicate (i x) true) :
    PolyTimeComputable fun x => colorBits (gadgetNodeColor (a x) (b x) (c x) (i x)) := by
  have hk : ∀ k : ℕ, PolyTimeComputable fun x => [decide (i x = k)] :=
    fun k => eqTest_poly hi (unaryConst_poly k)
  have na := polyTimeComputable_not ha
  have nb := polyTimeComputable_not hb
  have h2 := polyTimeComputable_and na nb
  have h3 := polyTimeComputable_and h2 (polyTimeComputable_not hc)
  have K : ∀ v : Fin 3, PolyTimeComputable fun _ : List Bool => colorBits v :=
    fun v => polyTimeComputable_const _
  refine (polyTimeComputable_ite (hk 5) (K 1) (polyTimeComputable_ite h3 (K 0)
    (polyTimeComputable_ite h2
      (polyTimeComputable_ite (hk 4) (K 2) (polyTimeComputable_ite (hk 3) (K 0)
        (polyTimeComputable_ite (hk 2) (K 2) (polyTimeComputable_ite (hk 1) (K 1) (K 0)))))
      (polyTimeComputable_ite (hk 4) (K 0) (polyTimeComputable_ite (hk 3) (K 2)
        (polyTimeComputable_ite (hk 2) (K 1) (polyTimeComputable_ite (hk 1)
          (polyTimeComputable_ite nb (K 0) (K 2))
          (polyTimeComputable_ite na (K 0) (polyTimeComputable_ite nb (K 2) (K 0)))))))))).congr
    fun x => ?_
  rw [gadgetNodeColor_eq]
  simp only [decide_eq_true_eq]
  split_ifs <;> rfl

/-- Glue. The two bits of the colour `gadgetColor (K x) (a x).getD (t x)` are a polynomial-time
function of the unary `K x`, `t x` and the word `a x` (an `ite` tree over the vertex ranges,
`litVal_poly`, `clauseLit_poly`, `gadgetNodeColorBits_poly`). -/
private theorem gadgetColorBits_poly {K t : List Bool → ℕ} {a : List Bool → List Bool}
    (hK : PolyTimeComputable fun x => List.replicate (K x) true)
    (ht : PolyTimeComputable fun x => List.replicate (t x) true) (ha : PolyTimeComputable a) :
    PolyTimeComputable fun x =>
      colorBits (gadgetColor (K x) (fun v => (a x).getD v false) (t x)) := by
  have hk : ∀ k : ℕ, PolyTimeComputable fun x => [decide (t x = k)] :=
    fun k => eqTest_poly ht (unaryConst_poly k)
  have hL : PolyTimeComputable fun x => List.replicate (3 + 2 * K x) true :=
    unaryAdd_poly (unaryConst_poly 3) (unaryMul_poly (unaryConst_poly 2) hK)
  have hd := unarySub_poly ht hL
  have hlit := litVal_poly (unarySub_poly ht (unaryConst_poly 3)) ha
  have hj : ∀ j : Fin 3, PolyTimeComputable fun x =>
      [litVal (fun v => (a x).getD v false) (clauseLit (K x) ((t x - (3 + 2 * K x)) / 6) j)] :=
    fun j => litVal_poly (clauseLit_poly hK (unaryDivConst_poly hd 6) j) ha
  have hnode := gadgetNodeColorBits_poly (hj 0) (hj 1) (hj 2) (unaryModConst_poly hd 6)
  have C : ∀ v : Fin 3, PolyTimeComputable fun _ : List Bool => colorBits v :=
    fun v => polyTimeComputable_const _
  refine (polyTimeComputable_ite (hk 0) (C 0) (polyTimeComputable_ite (hk 1) (C 1)
    (polyTimeComputable_ite (hk 2) (C 2) (polyTimeComputable_ite (ltTest_poly ht hL)
      (polyTimeComputable_ite hlit (C 1) (C 2)) hnode)))).congr fun x => ?_
  rw [gadgetColor_eq]
  simp only [decide_eq_true_eq]
  split_ifs <;> rfl

/-- **The witness map of the gadget graph is polynomial-time**:
`PolyTimeComputable fun z => colorWord (pairFstD z) (pairSndD z)`.

**Proof sketch.** `colorWord s a` is the concatenation over `t < gadgetN |s|` of the two bits
`[c / 2 = 1, c % 2 = 1]` of the colour `c = gadgetColor |s| (a.getD · false) t` (the layout of
`encColoring`: `getD_encColoring_two_mul`, `getD_encColoring_two_mul_add_one`,
`length_encColoring`). Emit it with the tabulation host
`ComposeMachines.polyTimeComputable_flatMap_range`: the count `gadgetN |s| = 3 + 2K + 6(2K)³` is
unary arithmetic (`EncodingMachines.unaryAdd_poly`, `EncodingMachines.unaryMul_poly`), and each
chunk is an `ite` tree of constants over unary comparisons of `t`, divisions and remainders by
constants and by `2K`, and bits of `a` at unary indices (`EncodingMachines.getBit_poly`). -/
theorem polyTimeComputable_colorWord :
    PolyTimeComputable fun z => colorWord (pairFstD z) (pairSndD z) := by
  have hK : PolyTimeComputable fun z => List.replicate (pairFstD z).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hE : PolyTimeComputable fun w =>
      (fun z t => colorBits (gadgetColor (pairFstD z).length
        (fun v => (pairSndD z).getD v false) t)) (pairSndD w) (pairFstD w).length :=
    gadgetColorBits_poly (hK.comp polyTimeComputable_pairSndD) hK
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hM : PolyTimeComputable fun z => List.replicate (2 * (pairFstD z).length) true :=
    unaryMul_poly (unaryConst_poly 2) hK
  have hn : PolyTimeComputable fun z => List.replicate (gadgetN (pairFstD z).length) true :=
    (unaryAdd_poly (unaryAdd_poly (unaryConst_poly 3) hM)
      (unaryMul_poly (unaryConst_poly 6) (unaryMul_poly (unaryMul_poly hM hM) hM))).congr
      fun z => by rw [gadgetN_eq]; ring_nf
  refine (SecureComputation.ComposeMachines.polyTimeComputable_flatMap_range
    (E := fun z t => colorBits (gadgetColor (pairFstD z).length
      (fun v => (pairSndD z).getD v false) t)) hE hn).congr fun z => ?_
  rw [colorWord_eq, flatMap_colorBits]

end TCSlib.Cryptography.LevinHardness
