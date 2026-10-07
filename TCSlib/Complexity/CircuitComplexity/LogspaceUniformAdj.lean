/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.LogspaceUniformScan
import TCSlib.Complexity.CircuitComplexity.LogspaceUniformWalk

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Logspace-uniformity via the adjacency representation

[AB09, p. 112]: "a circuit family is logspace-uniform iff `SIZE(n)`, `TYPE(n, i)` and
`EDGE(n, i, j)` are computable in `O(log n)` space", the circuit being given by its
adjacency matrix, inputs first and output last.

## Main results

* `BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.hasLogspaceAdjacency` — logspace-uniform
  families have logspace adjacency representations (any family).
* `BoolCircuit.DAGCircuitFamily.isLogspaceUniform_iff` — for canonical families the two are
  equivalent. [AB09, p. 112]

## Divergences from [AB09]

* The representation's conventions (threshold `SIZE`, one `TYPE` language per type,
  canonical circuits) are recorded in
  `TCSlib.Complexity.CircuitComplexity.LogspaceUniformAdjBasic`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.2.1, p. 112.)
-/

namespace BoolCircuit

open Turing Complexity LogProg

namespace AdjScan

/-- The language decided by the scanner for task `τ`. -/
def lang (C : DAGCircuitFamily) : Task → Language Bool
  | .size => C.sizeLang
  | .type t => C.typeLang t
  | .edge => C.edgeLang

/-- Every member of the scanner's language passes the scanner's format check. -/
lemma valid_of_mem {C : DAGCircuitFamily} {τ : Task} {x : List Bool} (h : x ∈ lang C τ) :
    Valid τ x := by
  cases τ with
  | size => obtain ⟨n, i, rfl, -⟩ := h; exact ⟨n, _, rfl, canon_bits i⟩
  | type t => obtain ⟨n, i, rfl, -⟩ := h; exact ⟨n, _, rfl, canon_bits i⟩
  | edge => obtain ⟨n, i, j, rfl, -⟩ := h; exact ⟨n, _, _, rfl, canon_bits i, canon_bits j⟩

/-- On a well-formed input every configuration meets the scanner's syntactic preconditions. -/
lemma preS_scan {τ : Task} {x : List Bool} (hv : Valid τ x) (a : AConf 3 Lbl) :
    PreS (scan τ) x a := by
  obtain ⟨_ | l, v, res⟩ := a
  · trivial
  · cases τ <;> simp only [Valid] at hv <;> cases l <;>
      simp [PreS, scan, rd, hit, hv] <;> rename_i ex <;> cases ex <;> simp

/-- The word of the input `⟨1ⁿ, w⟩` naming the target (and source) vertex. -/
def word : Task → ℕ → ℕ → List Bool
  | .edge, iv, tv => pairEncode (Nat.bits iv) (Nat.bits tv)
  | _, _, tv => Nat.bits tv

/-- The scanner's answer is membership in its language.

**Proof sketch.** Case on the task. Rewrite membership in the language at `⟨1ⁿ, word⟩` by
`mem_sizeLang`, `mem_typeLang` or `mem_edgeLang`, then split on whether the target vertex is an
input, a gate or beyond the circuit, and compare with `nAns` and `hitAns`. -/
lemma answer_eq (C : DAGCircuitFamily) (τ : Task) (n iv tv : ℕ) (w : List Bool)
    (hw : Target τ (X n w) iv tv) (hx : w = word τ iv tv) :
    (if tv < n then nAns τ else
        if h : tv - n < (C.circuit n).gates.length then hitAns iv (C.circuit n).gates[tv - n] τ
        else false) = MultiTapeTM.indicator (lang C τ : Set (List Bool)) (X n w) := by
  rw [indicator_eq_decide]
  cases τ with
  | size =>
    simp only [word] at hx; subst hx
    have : X n (Nat.bits tv) ∈ lang C .size ↔ tv < (C.circuit n).size := C.mem_sizeLang
    simp only [this, DAGCircuit.size, nAns, hitAns]
    split_ifs <;> simp <;> omega
  | type t =>
    simp only [word] at hx; subst hx
    have : X n (Nat.bits tv) ∈ lang C (.type t) ↔
        tv < (C.circuit n).size ∧ (C.circuit n).vtype tv = t := C.mem_typeLang
    simp only [this, DAGCircuit.size, nAns, hitAns, DAGCircuit.vtype]
    split_ifs with h1 h2
    · have : tv < n + (C.circuit n).gates.length := by omega
      simp [this, eq_comm]
    · simp [h2, eq_comm]; omega
    · simp; intro h; omega
  | edge =>
    simp only [word] at hx; subst hx
    have : X n (pairEncode (Nat.bits iv) (Nat.bits tv)) ∈ lang C .edge ↔
        (C.circuit n).Edge iv tv := C.mem_edgeLang
    simp only [this, nAns, hitAns, DAGCircuit.Edge]
    split_ifs with h1 h2
    · simp; omega
    · simp [List.getElem?_eq_getElem h2]; omega
    · simp only [Bool.false_eq, decide_eq_false_iff_not, not_and, not_exists]
      intro _ g hg
      rw [List.getElem?_eq_none (by omega)] at hg
      exact absurd hg (by simp)

/-- **The scanner decides its language in `L`**, given an implicitly logspace computable
description `f`.

**Proof sketch.** `arm_decides_poly` with the bit language of `f` as the only decider: on a
malformed input the scanner rejects at once; on `⟨1ⁿ, …⟩` its run (`scan_halts`) reads the
description `f 1ⁿ = encode Cₙ` and keeps every register below `|f 1ⁿ| ≤ C (n + 1)^c`. -/
theorem lang_mem (C : DAGCircuitFamily) (f : List Bool → List Bool)
    (hf : ImplicitlyLogspaceComputable f)
    (hC : ∀ n, f (List.replicate n true) = (C.circuit n).encode) (τ : Task) :
    lang C τ ∈ LOGSPACE := by
  obtain ⟨⟨Cf, cf, hlen⟩, hbit, -⟩ := hf
  refine arm_decides_poly (scan τ) .start (fun _ => indexLang fun x i => (f x).getD i false = true)
    (fun _ => hbit) Cf cf fun x => ?_
  by_cases hv : Valid τ x
  · -- decompose the input
    obtain ⟨n, w, iv, tv, rfl, hw, hx⟩ : ∃ n w iv tv, x = X n w ∧ Target τ (X n w) iv tv ∧
        w = word τ iv tv := by
      cases τ with
      | edge =>
        obtain ⟨n, u, w', rfl, hu, hw'⟩ := hv
        refine ⟨n, _, bitsVal u, bitsVal w', rfl, ?_, ?_⟩
        · simp only [Target, X, pairWords_pairEncode]
          rw [← canon_eq_bits u hu, ← canon_eq_bits w' hw']
        · simp only [word]; rw [← canon_eq_bits u hu, ← canon_eq_bits w' hw']
      | size =>
        obtain ⟨n, w', rfl, hw'⟩ := hv
        refine ⟨n, w', 0, bitsVal w', rfl, ?_, by simp only [word]; exact canon_eq_bits w' hw'⟩
        simp only [Target, X, plainWord_pairEncode]; exact canon_eq_bits w' hw'
      | type t =>
        obtain ⟨n, w', rfl, hw'⟩ := hv
        refine ⟨n, w', 0, bitsVal w', rfl, ?_, by simp only [word]; exact canon_eq_bits w' hw'⟩
        simp only [Target, X, plainWord_pairEncode]; exact canon_eq_bits w' hw'
    have hrd : ∀ p, (fun (_ : Fin 1) V => MultiTapeTM.indicator
        ((indexLang fun x i => (f x).getD i false = true : Language Bool) : Set (List Bool)) V)
        0 (X n (Nat.bits p)) = (C.circuit n).encode.getD p false := by
      intro p
      have hm := pairEncode_mem_indexLang (fun x i => (f x).getD i false = true)
        (List.replicate n true) p
      rw [← hC n]
      simp only [MultiTapeTM.indicator, X]
      split_ifs with h
      · exact (hm.mp h).symm
      · cases e : (f (List.replicate n true)).getD p false
        · rfl
        · exact absurd (hm.mpr e) h
    have := scan_halts (o := fun (_ : Fin 1) V => MultiTapeTM.indicator
        ((indexLang fun x i => (f x).getD i false = true : Language Bool) : Set (List Bool)) V)
      (C.circuit n) hrd hw hv
    rw [answer_eq C τ n iv tv w hw hx] at this
    refine this.mono fun a ha => ⟨preS_scan hv a, fun r => (ha r).trans ?_⟩
    rw [← hC n]
    refine (hlen _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    simp only [List.length_replicate, X, pairEncode_eq_dbl, List.length_append, length_dbl]
    omega
  · -- malformed input: rejected at once
    have hn : MultiTapeTM.indicator (lang C τ : Set (List Bool)) x = false := by
      rw [indicator_eq_decide]; simpa using fun h => hv (valid_of_mem h)
    rw [hn]
    refine ⟨1, ?_, ?_, fun t ht => ?_⟩
    · cases τ <;> simp only [Valid] at hv <;> simp [arun, astep, scan, hv]
    · cases τ <;> simp only [Valid] at hv <;> simp [arun, astep, scan, hv]
    · obtain rfl : t = 0 := by omega
      exact ⟨by simp [PreS, scan]; cases τ <;> trivial, fun r => by simp [arun]⟩

end AdjScan

namespace AdjWalk

/-- A list code is at most one plus (one more than the longest element code) per element. -/
lemma length_encodeList_le' {α : Type} (f : α → List Bool) (b : ℕ) (as : List α)
    (h : ∀ a ∈ as, (f a).length ≤ b) : (encodeList f as).length ≤ as.length * (b + 1) + 1 := by
  induction as with
  | nil => simp [encodeList]
  | cons a as ih =>
    have ha := h a (List.mem_cons_self ..)
    have hs := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp only [encodeList, List.length_cons, List.length_append]
    rw [Nat.succ_mul]
    omega

/-- A canonical circuit's description has length at most `4 (|C| + 1)³`.

**Proof sketch.** A canonical gate's arguments are distinct vertices below `S = |C|`, so it
lists at most `S` of them, each with a code of length at most `S + 1`; there are at most `S`
gates, and the codes of `n` and of the output have length at most `S + 1`. -/
lemma length_encode_le_of_canonical {n : ℕ} (C : DAGCircuit n) (hC : C.IsCanonical) :
    C.encode.length ≤ 4 * (C.size + 1) ^ 3 := by
  set S := C.size with hS
  have hgate : ∀ g ∈ C.gates, g.encode.length ≤ S * (S + 2) + 3 := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have hlt : ∀ a ∈ C.gates[j].args, a < S := fun a ha => by
      have := C.args_lt j hj a ha; simp only [hS, DAGCircuit.size]; omega
    have hlen : C.gates[j].args.length ≤ S := by
      have := ((hC.1 _ hg).nodup.subperm (l₂ := List.range S)
        (fun a ha => List.mem_range.mpr (hlt a ha))).length_le
      simpa using this
    have hcode := length_encodeList_le' encodeNat (S) C.gates[j].args fun a ha => by
      have := hlt a ha; simp [encodeNat]; omega
    have hk : C.gates[j].kind.encode.length = 2 := by cases C.gates[j].kind <;> rfl
    simp only [DAGGate.encode, List.length_append, hk]
    have := Nat.mul_le_mul_right (S + 1) hlen
    nlinarith
  have hl := length_encodeList_le' DAGGate.encode _ C.gates hgate
  have hG : C.gates.length ≤ S := by simp only [hS, DAGCircuit.size]; omega
  have hn : n ≤ S := by simp only [hS, DAGCircuit.size]; omega
  have ho : C.output < S := C.output_lt
  have := Nat.mul_le_mul_right (S * (S + 2) + 3 + 1) hG
  simp only [DAGCircuit.encode, encodeNat, List.length_append, List.length_replicate,
    List.length_singleton]
  have e1 : S * (S * (S + 2) + 3 + 1) = S * S * S + 2 * (S * S) + 4 * S := by ring
  have e2 : 4 * (S + 1) ^ 3 = 4 * (S * S * S) + 12 * (S * S) + 12 * S + 4 := by ring
  rw [e1] at this
  rw [e2]
  generalize S * S * S = c3 at *
  generalize S * S = c2 at *
  omega

/-- The uniformity function built from the walk: the description of `C_{|x|}` on unary
inputs, the empty word elsewhere. -/
noncomputable def descr (C : DAGCircuitFamily) (x : List Bool) : List Bool :=
  open Classical in
  if x = List.replicate x.length true then (C.circuit x.length).encode else []

/-- On `1ⁿ`, `descr C` is the description of `Cₙ`. -/
lemma descr_replicate (C : DAGCircuitFamily) (n : ℕ) :
    descr C (List.replicate n true) = (C.circuit n).encode := by
  have : (List.replicate n true).length = n := List.length_replicate
  unfold descr
  rw [if_pos (by rw [this]), this]

/-- Where `descr C` is nonempty its argument is unary. -/
lemma eq_replicate_of_descr_ne {C : DAGCircuitFamily} {x : List Bool} (h : descr C x ≠ []) :
    x = List.replicate x.length true := by
  unfold descr at h; split_ifs at h with hx
  · exact hx
  · exact absurd rfl h

/-- On a well-formed input every configuration meets the walk's syntactic preconditions. -/
lemma preS_walk {lm : Bool} {y : List Bool} (hv : ValidPlain y) (a : AConf 4 Lbl) :
    PreS (walk lm) y a := by
  obtain ⟨_ | l, v, res⟩ := a
  · trivial
  · cases l <;> simp [PreS, walk, hv]

/-- **The walk decides the index languages of `descr C` in `L`**, for canonical
polynomial-size families with `SIZE`, `TYPE`, `EDGE` in `L`.

**Proof sketch.** `arm_decides_poly` with the five deciders: on malformed inputs the walk
rejects at once (and no malformed input is in the language, as `descr C` is empty off
unary inputs); on `⟨1ⁿ, bits i⟩` it answers by `walk_halts`, with registers at most
`|encode Cₙ| ≤ 4 (|Cₙ| + 1)³`, a polynomial. -/
lemma walk_lang (C : DAGCircuitFamily) (hcan : C.IsCanonical) (hA : C.HasLogspaceAdjacency)
    (lm : Bool) (p : List Bool → ℕ → Prop) (hp : ∀ x i, p x i → descr C x ≠ [])
    (hans : ∀ n i, (if i < (C.circuit n).encode.length then
        lm || (C.circuit n).encode.getD i false else false) =
      @decide (p (List.replicate n true) i) (Classical.dec _)) :
    indexLang p ∈ LOGSPACE := by
  obtain ⟨⟨a, k, hsz⟩, hS, hT, hE⟩ := hA
  have hAs : ∀ j, decs C j ∈ LOGSPACE := by
    intro j
    match j with
    | 0 => exact hS
    | 1 => exact hT _
    | 2 => exact hT _
    | 3 => exact hT _
    | 4 => exact hE
  refine arm_decides_poly (walk lm) .start (decs C) hAs (4 * (a + 1) ^ 3) (3 * k) fun y => ?_
  by_cases hv : ValidPlain y
  · obtain ⟨n, w, rfl, hw⟩ := hv
    rw [canon_eq_bits w hw]
    set i := bitsVal w
    have hrun := walk_halts C (hcan n) lm i
    have hind : MultiTapeTM.indicator (indexLang p : Set (List Bool)) (X n i) =
        @decide (p (List.replicate n true) i) (Classical.dec _) := by
      rw [indicator_eq_decide]; exact decide_eq_decide.mpr (pairEncode_mem_indexLang p _ i)
    rw [hans, ← hind] at hrun
    · refine hrun.mono fun c hc => ⟨preS_walk ⟨n, _, rfl, canon_bits i⟩ c, fun r => ?_⟩
      refine (hc r).trans ((length_encode_le_of_canonical _ (hcan n)).trans ?_)
      have h1 : (C.circuit n).size + 1 ≤ (a + 1) * (n + 1) ^ k := by
        have := hsz n
        have : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
        nlinarith
      have h2 : n ≤ (X n i).length := by
        simp [X, pairEncode_eq_dbl, length_dbl]; omega
      calc 4 * ((C.circuit n).size + 1) ^ 3 ≤ 4 * ((a + 1) * (n + 1) ^ k) ^ 3 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
        _ = 4 * (a + 1) ^ 3 * (n + 1) ^ (3 * k) := by ring
        _ ≤ 4 * (a + 1) ^ 3 * ((X n i).length + 1) ^ (3 * k) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  · have hn : MultiTapeTM.indicator (indexLang p : Set (List Bool)) y = false := by
      rw [indicator_eq_decide]
      simp only [decide_eq_false_iff_not]
      rintro ⟨x, i, rfl, hpx⟩
      exact hv ⟨x.length, _, by rw [← eq_replicate_of_descr_ne (hp x i hpx)], canon_bits i⟩
    rw [hn]
    refine ⟨1, ?_, ?_, fun t ht => ?_⟩
    · simp [arun, astep, walk, hv]
    · simp [arun, astep, walk, hv]
    · obtain rfl : t = 0 := by omega
      exact ⟨by simp [arun, PreS, walk], fun r => by simp [arun]⟩

end AdjWalk

namespace DAGCircuitFamily

/-- **Logspace-uniform families have logspace adjacency representations** [AB09, p. 112]:
`SIZE`, `TYPE` and `EDGE` are in `L`.

**Proof sketch.** Each is decided by scanning the description `encode Cₙ`, read bit by bit
through the bit language of the uniformity function (`BoolCircuit.AdjScan.lang_mem`). -/
theorem IsLogspaceUniform.hasLogspaceAdjacency {C : DAGCircuitFamily}
    (h : C.IsLogspaceUniform) : C.HasLogspaceAdjacency := by
  obtain ⟨f, hf, hC⟩ := h
  exact ⟨IsLogspaceUniform.isPolySize ⟨f, hf, hC⟩, AdjScan.lang_mem C f hf hC .size,
    fun t => AdjScan.lang_mem C f hf hC (.type t), AdjScan.lang_mem C f hf hC .edge⟩

/-- **Canonical families with logspace adjacency representations are logspace-uniform**
[AB09, p. 112].

**Proof sketch.** The function `descr C` (the description on unary inputs) has polynomial
length (`length_encode_le_of_canonical`, polynomial size), and its bit and length languages
are decided by the walk (`BoolCircuit.AdjWalk.walk_lang`), which regenerates the description
from `SIZE`, `TYPE` and `EDGE`, stopping at the requested bit. -/
theorem HasLogspaceAdjacency.isLogspaceUniform {C : DAGCircuitFamily} (hcan : C.IsCanonical)
    (h : C.HasLogspaceAdjacency) : C.IsLogspaceUniform := by
  classical
  refine ⟨AdjWalk.descr C, ⟨?_, ?_, ?_⟩, AdjWalk.descr_replicate C⟩
  · obtain ⟨a, k, hsz⟩ := h.1
    refine ⟨4 * (a + 1) ^ 3, 3 * k, fun x => ?_⟩
    unfold AdjWalk.descr
    split_ifs
    · refine (AdjWalk.length_encode_le_of_canonical _ (hcan _)).trans ?_
      have h1 : (C.circuit x.length).size + 1 ≤ (a + 1) * (x.length + 1) ^ k := by
        have := hsz x.length
        have : 1 ≤ (x.length + 1) ^ k := Nat.one_le_pow _ _ (by omega)
        nlinarith
      calc 4 * ((C.circuit x.length).size + 1) ^ 3
          ≤ 4 * ((a + 1) * (x.length + 1) ^ k) ^ 3 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
        _ = 4 * (a + 1) ^ 3 * (x.length + 1) ^ (3 * k) := by ring
    · simp
  · refine AdjWalk.walk_lang C hcan h false _ (fun x i hx he => by simp [he] at hx) fun n i => ?_
    rw [AdjWalk.descr_replicate]
    split_ifs with hi
    · simp
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
  · refine AdjWalk.walk_lang C hcan h true _ (fun x i hx he => by simp [he] at hx) fun n i => ?_
    rw [AdjWalk.descr_replicate]
    split_ifs with hi <;> simp [hi]

/-- **Robustness of logspace-uniformity** [AB09, p. 112]: a canonical family is
logspace-uniform iff its adjacency representation (`SIZE`, `TYPE`, `EDGE`) is computable in
logarithmic space (and it has polynomial size). -/
theorem isLogspaceUniform_iff {C : DAGCircuitFamily} (hcan : C.IsCanonical) :
    C.IsLogspaceUniform ↔ C.HasLogspaceAdjacency :=
  ⟨IsLogspaceUniform.hasLogspaceAdjacency, HasLogspaceAdjacency.isLogspaceUniform hcan⟩

end DAGCircuitFamily

end BoolCircuit
