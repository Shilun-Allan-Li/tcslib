/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.NPPoly
import TCSlib.Complexity.CircuitComplexity.KarpLiptonPrefix
import TCSlib.Complexity.CircuitComplexity.CircuitEval
import TCSlib.Complexity.CircuitComplexity.Uniform
import TCSlib.Complexity.PolyHierarchy.Collapse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Yap's theorem and [AB09, Exercise 7.8]

Yap's theorem, the `NP/poly` analogue of Karp–Lipton: **if `coNP ⊆ NP/poly` then
`PH = Σ₃ᵖ`**. With `Randomized.coNP_subset_NPPoly_of_compl_SAT3_mem_BPNP` it gives
[AB09, Exercise 7.8]: if `3SATᶜ ∈ BP·NP` then `PH = Σ₃ᵖ`.

We show `Π₃ᵖ ⊆ Σ₃ᵖ` and collapse ([AB09, Theorem 5.4]). Write
`x ∈ L ⟺ ∀ u ∃ v, ⟨⟨x, u⟩, v⟩ ∈ K` with `K ∈ coNP`, `z ∈ Kᶜ ⟺ ∃ r, ⟨z, r⟩ ∈ R`, `R ∈ P`,
and let `D` be `NP/poly` circuits for `K`. The `Σ₃ᵖ` formula guesses the description `U` of
`D` at the length `N(|x|)` of the `z = ⟨⟨x, u⟩, v⟩`, and checks, through `CVAL` queries,

`∃ U ∀ (u, v', w', r) ∃ (v, w)`: if `|u|` is right then `U` accepts `(⟨⟨x, u⟩, v⟩, w)` and
it is *not* the case that `U` accepts `(⟨⟨x, u⟩, v'⟩, w')` while `r` refutes `⟨⟨x, u⟩, v'⟩ ∈ K`.

The second clause makes every accepted `z` lie in `K` whatever `U` is (soundness, `sound`);
the true circuit passes both clauses when `x ∈ L` (completeness, `complete`).

## Main definitions

* `Complexity.Yap.Query` — one evaluation of the guessed circuit.
* `Complexity.Yap.Data` — the constants of the construction; `Data.Core`, `Data.Check` —
  the checks; `Data.checkLang` (`P`), `Data.badLang` (`coNP`), `Data.innerLang` (`Π₂ᵖ`).

## Main results

* `Complexity.Yap.query_append_iff` — a query to an `NP/poly` circuit's description.
* `Complexity.Yap.mem_SigmaP_succ_of_exists_le` — a length-bounded `∃` over `Πᵢᵖ` is `Σᵢ₊₁ᵖ`.
* `Complexity.Yap.Data.checkLang_mem_P` — the check is polynomial-time.
* `Complexity.Yap.sound`, `Complexity.Yap.complete`.
* `Complexity.PiP_three_subset_SigmaP_three_of_coNP_subset_NPPoly` — `Π₃ᵖ ⊆ Σ₃ᵖ`.
* `Complexity.PH_eq_SigmaP_three_of_coNP_subset_NPPoly` — Yap's theorem.
* `Randomized.PH_eq_SigmaP_three_of_compl_SAT3_mem_BPNP` — [AB09, Exercise 7.8].

## Divergences

* **Exercise 7.8's hypothesis** is `3SATᶜ ∈ BP·NP`: the overbar on `3SAT` is lost in the
  printed text, and `3SAT ∈ BP·NP` holds outright (see `Randomized/NPPoly.lean`).
* **Self-consistency instead of a correctness proof for the circuit**, as in
  `CircuitComplexity/KarpLipton.lean` ([AB09, Theorem 6.19]): the `∀` block checks that no
  accepted instance is refuted, rather than comparing the circuit with `K` on all inputs.
* **Length bounds.** The universal and existential blocks are checked against an explicit
  polynomial bound inside the verifier, so the inner languages accept only bounded blocks.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Theorem 5.4; Theorem 6.19; Exercises 7.7–7.8, p. 142.)
* [Yap83] C.-K. Yap, *Some consequences of non-uniform conditions on uniform classes*,
  Theoretical Computer Science 26 (1983), 287–300. Theorem numbering follows the standard
  citation of the result (`coNP ⊆ NP/poly ⇒ PH = Σ₃ᵖ` is cited as its Theorem 2).
-/

namespace Complexity.Yap

open Turing BoolCircuit Complexity.PolyHierarchy

/-! ### Querying a guessed circuit -/

/-- **One query to a guessed circuit**: the description `d` accepts `q`, i.e.
`⟨d, q⟩ ∈ CVAL`. -/
def Query (d q : List Bool) : Prop := pairEncode d q ∈ CVAL

/-- An accepted query is no longer than the description (the description lists the
inputs). -/
theorem length_le_of_query {d q : List Bool} (h : Query d q) : q.length ≤ d.length := by
  obtain ⟨x, C, -, -, heq⟩ := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj (pairEncode_injective (a₁ := (d, q)) (a₂ := (_, _)) heq)
  rw [h1, h2]
  exact le_trans (Nat.le_add_right _ _) C.size_le_length_encode

/-- Circuits with the same description agree on inputs with the same bits. -/
theorem eval_eq_of_encode_eq {n₁ n₂ : ℕ} {C₁ : DAGCircuit n₁} {C₂ : DAGCircuit n₂}
    (h : C₁.encode = C₂.encode) {x₁ : Fin n₁ → Bool} {x₂ : Fin n₂ → Bool}
    (hx : List.ofFn x₁ = List.ofFn x₂) : C₁.eval x₁ = C₂.eval x₂ := by
  obtain ⟨-, hg, ho⟩ := DAGCircuit.eq_of_encode_eq h
  simp only [DAGCircuit.eval, DAGCircuit.values, hg, ho, hx]

/-- **A query to a known circuit's description** is an evaluation: `C` accepts `q` iff
`q` is an input of `C` on which it outputs `1`. -/
theorem query_encode_iff {n : ℕ} (C : DAGCircuit n) (hC : C.IsFaninTwo) (q : List Bool) :
    Query C.encode q ↔ ∃ x : Fin n → Bool, List.ofFn x = q ∧ C.eval x = true := by
  constructor
  · rintro ⟨q', C', -, hev, heq⟩
    obtain ⟨h1, h2⟩ := Prod.mk.inj (pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _)) heq)
    have hn : n = q'.length := (DAGCircuit.eq_of_encode_eq h1).1
    have hq := (List.ofFn_congr hn.symm q'.get).symm
    refine ⟨fun i => q'.get (i.cast hn), by rw [h2]; exact hq.trans (List.ofFn_get q'), ?_⟩
    rw [eval_eq_of_encode_eq h1 hq]
    exact hev
  · rintro ⟨x, rfl, hev⟩
    have hn : n = (List.ofFn x).length := (List.length_ofFn).symm
    have key : ∀ (m : ℕ) (C' : DAGCircuit m) (q : List Bool) (h : m = q.length),
        C'.IsFaninTwo → C'.eval (fun i => q.get (i.cast h)) = true → Query C'.encode q := by
      intro m C' q h hC' hev'
      subst h
      exact ⟨q, C', hC', by simpa using hev', rfl⟩
    refine key n C _ hn hC ?_
    rw [eval_eq_of_encode_eq rfl ((List.ofFn_congr hn.symm _).symm.trans (List.ofFn_get _))]
    exact hev

/-- **A query to an `NP/poly` circuit**: for `|z| = N`, the description of the circuit
`D_N` (on `z` and a certificate) accepts `z ++ w` iff `w` is a certificate making
`D_{|z|}` accept `z`. -/
theorem query_append_iff {m : ℕ → ℕ} (D : (n : ℕ) → DAGCircuit (n + m n))
    (hD : ∀ n, (D n).IsFaninTwo) {N : ℕ} (z w : List Bool) (hz : z.length = N) :
    Query (D N).encode (z ++ w) ↔ ∃ y : Fin (m z.length) → Bool,
      w = List.ofFn y ∧ (D z.length).eval (Fin.append z.get y) = true := by
  subst hz
  rw [query_encode_iff _ (hD _)]
  constructor
  · rintro ⟨x, hx, hev⟩
    have hxab : x = Fin.append (fun i => x (Fin.castAdd (m z.length) i))
        (fun j => x (Fin.natAdd z.length j)) := Fin.append_castAdd_natAdd.symm
    rw [hxab, List.ofFn_fin_append] at hx
    rw [hxab] at hev
    obtain ⟨h1, h2⟩ := List.append_inj hx (by simp)
    have hz : (fun i => x (Fin.castAdd (m z.length) i)) = z.get :=
      List.ofFn_injective (h1.trans (List.ofFn_get z).symm)
    rw [hz] at hev
    exact ⟨_, h2.symm, hev⟩
  · rintro ⟨y, rfl, hev⟩
    exact ⟨_, by rw [List.ofFn_fin_append, List.ofFn_get], hev⟩

/-! ### A length-bounded existential block -/

/-- **A length-bounded `∃` over a `Πᵢᵖ` language is `Σᵢ₊₁ᵖ`**: if every `⟨x, u⟩ ∈ L'`
gives `x ∈ L`, and every `x ∈ L` has such a `u` of length at most `B (|x|+1)^b`, then
`L ∈ Σᵢ₊₁ᵖ`. The witness is padded to the exact length `(B+1)(|x|+1)^b` as `1ʳ 0 u`.

**Proof sketch.** Apply `mem_SigmaP_succ_iff` to the preimage of `L'` under
`⟨x, U⟩ ↦ ⟨x, dropMarker U⟩` (in `Πᵢᵖ` by closure under polynomial-time preimages). -/
theorem mem_SigmaP_succ_of_exists_le {i : ℕ} {L L' : Language Bool} (hL' : L' ∈ PiP i)
    (B b : ℕ) (h₁ : ∀ x u, pairEncode x u ∈ L' → x ∈ L)
    (h₂ : ∀ x ∈ L, ∃ u : List Bool, u.length ≤ B * (x.length + 1) ^ b ∧ pairEncode x u ∈ L') :
    L ∈ SigmaP (i + 1) := by
  let g : List Bool → List Bool :=
    fun z => pairEncode (pairFstD z) (KarpLipton.dropMarker (pairSndD z))
  have hgp : PolyTimeComputable g := polyTimeComputable_pairFstD.pairEncode
    (KarpLipton.polyTimeComputable_dropMarker.comp polyTimeComputable_pairSndD)
  refine mem_SigmaP_succ_iff.mpr ⟨B + 1, b, g ⁻¹' L', preimage_mem_PiP hL' hgp, fun x => ?_⟩
  have hg : ∀ U, g (pairEncode x U) = pairEncode x (KarpLipton.dropMarker U) := fun U => by
    simp [g]
  constructor
  · intro hx
    obtain ⟨u, hu, hmem⟩ := h₂ x hx
    have hone : 1 ≤ (x.length + 1) ^ b := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hsplit : (B + 1) * (x.length + 1) ^ b = B * (x.length + 1) ^ b + (x.length + 1) ^ b := by
      ring
    refine ⟨List.replicate ((B + 1) * (x.length + 1) ^ b - u.length - 1) true ++ false :: u,
      ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons]
      omega
    · show g _ ∈ L'
      rw [hg, KarpLipton.dropMarker_marker]
      exact hmem
  · rintro ⟨U, -, hU⟩
    exact h₁ x _ (by rw [Set.mem_preimage, hg] at hU; exact hU)

/-! ### The checks -/

/-- The length `N(n)` of `⟨⟨x, u⟩, v⟩` for `|x| = n`, `|u| = C₁ (n+1)^{c₁}` and
`|v| = C₂ (|⟨x, u⟩|+1)^{c₂}`. -/
def nN (C₁ c₁ C₂ c₂ n : ℕ) : ℕ :=
  2 * (2 * n + 2 + C₁ * (n + 1) ^ c₁) + 2 + C₂ * (2 * n + 2 + C₁ * (n + 1) ^ c₁ + 1) ^ c₂

/-- The constants of the construction: block lengths `C₁ (n+1)^{c₁}` (for `u`) and
`C₂ (n+1)^{c₂}` (for `v`), the refutation bound `C₃ (n+1)^{c₃}` and relation `R` of `Kᶜ`,
and the bound `B (n+1)^b` on the inner blocks. -/
structure Data where
  /-- Coefficient of the first block length. -/
  C₁ : ℕ
  /-- Degree of the first block length. -/
  c₁ : ℕ
  /-- Coefficient of the second block length. -/
  C₂ : ℕ
  /-- Degree of the second block length. -/
  c₂ : ℕ
  /-- Coefficient of the refutation length. -/
  C₃ : ℕ
  /-- Degree of the refutation length. -/
  c₃ : ℕ
  /-- Coefficient of the inner block bound. -/
  B : ℕ
  /-- Degree of the inner block bound. -/
  b : ℕ
  /-- The refutation relation: `z ∉ K ⟺ ∃ r, ⟨z, r⟩ ∈ R`. -/
  R : Language Bool

namespace Data

variable (d : Data)

/-- The length of the universal block `u` for the input `x`. -/
def M₁ (x : List Bool) : ℕ := d.C₁ * (x.length + 1) ^ d.c₁

/-- The length of the existential block `v` for `y = ⟨x, u⟩`. -/
def M₂ (y : List Bool) : ℕ := d.C₂ * (y.length + 1) ^ d.c₂

/-- The length `N(|x|)` of the instances `⟨⟨x, u⟩, v⟩` of `K`. -/
def nLen (x : List Bool) : ℕ := nN d.C₁ d.c₁ d.C₂ d.c₂ x.length

/-- **A soundness failure**: `U` accepts the well-formed instance `z = ⟨⟨x, u⟩, v⟩` with
certificate `w`, while `r` refutes `z ∈ K`. -/
def SoundFail (x U u v w r : List Bool) : Prop :=
  v.length = d.M₂ (pairEncode x u) ∧ Query U (pairEncode (pairEncode x u) v ++ w) ∧
    r.length ≤ d.C₃ * ((pairEncode (pairEncode x u) v).length + 1) ^ d.c₃ ∧
    pairEncode (pairEncode (pairEncode x u) v) r ∈ d.R

/-- **A match**: `U` accepts the well-formed instance `⟨⟨x, u⟩, v⟩` with certificate `w`. -/
def Match (x U u v w : List Bool) : Prop :=
  v.length = d.M₂ (pairEncode x u) ∧ Query U (pairEncode (pairEncode x u) v ++ w)

/-- **The core check** on `x`, the guess `U`, the universal block `t = ⟨⟨u, v'⟩, ⟨w', r⟩⟩`
and the existential block `e = ⟨v, w⟩`: `|u|` is right, and either `(v', w', r)` is a
soundness failure or `(v, w)` is not a match. -/
def Core (x U t e : List Bool) : Prop :=
  (pairFstD (pairFstD t)).length = d.M₁ x ∧
    (d.SoundFail x U (pairFstD (pairFstD t)) (pairSndD (pairFstD t)) (pairFstD (pairSndD t))
        (pairSndD (pairSndD t)) ∨
      ¬ d.Match x U (pairFstD (pairFstD t)) (pairFstD e) (pairSndD e))

/-- **The full check** on `w = ⟨x, U⟩`: the universal block is bounded, and the core check. -/
def Check (w t e : List Bool) : Prop :=
  t.length ≤ d.B * (w.length + 1) ^ d.b ∧ d.Core (pairFstD w) (pairSndD w) t e

/-- **The counterexample language** (`coNP`): pairs `p = ⟨w, t⟩` such that every bounded
existential block `e` passes the check, i.e. `t` defeats the guess. -/
def badLang : Language Bool :=
  {p | ∀ e : List Bool, e.length ≤ d.B * (p.length + 1) ^ d.b →
    d.Check (pairFstD p) (pairSndD p) e}

/-- **The inner language** (`Π₂ᵖ`): the `w = ⟨x, U⟩` admitting no counterexample. -/
def innerLang : Language Bool := {w | ∀ t : List Bool, pairEncode w t ∉ d.badLang}

/-- The check language, on `⟨⟨w, t⟩, e⟩`. -/
def checkLang : Language Bool :=
  {q | d.Check (pairFstD (pairFstD q)) (pairSndD (pairFstD q)) (pairSndD q)}

/-- Membership in the counterexample language, unfolded. -/
theorem mem_badLang {p : List Bool} : p ∈ d.badLang ↔ ∀ e : List Bool,
    e.length ≤ d.B * (p.length + 1) ^ d.b → d.Check (pairFstD p) (pairSndD p) e := Iff.rfl

/-- Membership in the inner language, unfolded. -/
theorem mem_innerLang {w : List Bool} :
    w ∈ d.innerLang ↔ ∀ t : List Bool, pairEncode w t ∉ d.badLang := Iff.rfl

/-- Membership in the check language, unfolded. -/
theorem mem_checkLang {q : List Bool} : q ∈ d.checkLang ↔
    d.Check (pairFstD (pairFstD q)) (pairSndD (pairFstD q)) (pairSndD q) := Iff.rfl

/-- The check on a well-formed `w = ⟨x, U⟩`. -/
@[simp] theorem check_pair (x U t e : List Bool) :
    d.Check (pairEncode x U) t e ↔
      t.length ≤ d.B * ((pairEncode x U).length + 1) ^ d.b ∧ d.Core x U t e := by
  simp [Check]

/-- The length of a well-formed instance `⟨⟨x, u⟩, v⟩` is `N(|x|)`. -/
theorem length_inst {x u v : List Bool} (hu : u.length = d.M₁ x)
    (hv : v.length = d.M₂ (pairEncode x u)) :
    (pairEncode (pairEncode x u) v).length = d.nLen x := by
  simp only [length_pairEncode, hv, M₂, hu, nLen, nN, M₁]

end Data

/-! ### The verifier languages -/

/-- A length test against a polynomial of another computed word is in `P`. -/
private theorem lenEq_poly_mem_P {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) (C c : ℕ) :
    {z | (f z).length = C * ((g z).length + 1) ^ c} ∈ P := by
  have h := lenEq_preimage_mem_P hf (unaryPT_poly C c hg)
  convert h using 1
  ext z
  simp

/-- A length bound by a polynomial of another computed word is in `P`. -/
private theorem lenLe_poly_mem_P {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) (C c : ℕ) :
    {z | (f z).length ≤ C * ((g z).length + 1) ^ c} ∈ P := by
  have h := lenLe_preimage_mem_P (unaryPT_poly C c hg) hf
  convert h using 1
  ext z
  simp

namespace Data

variable (d : Data)

/-- **The check language is in `P`** (when `R` is).

**Proof sketch.** The check is a Boolean combination of length tests against unary
polynomials, two `CVAL` queries and one `R` query, applied to words computed in polynomial
time from the coordinates (pair projections and re-pairings); `P` is closed under these. -/
theorem checkLang_mem_P (hR : d.R ∈ P) : d.checkLang ∈ P := by
  have hF := polyTimeComputable_pairFstD
  have hS := polyTimeComputable_pairSndD
  have hW : PolyTimeComputable fun q => pairFstD (pairFstD q) := hF.comp hF
  have hT : PolyTimeComputable fun q => pairSndD (pairFstD q) := hS.comp hF
  have hX : PolyTimeComputable fun q => pairFstD (pairFstD (pairFstD q)) := hF.comp hW
  have hU : PolyTimeComputable fun q => pairSndD (pairFstD (pairFstD q)) := hS.comp hW
  have hu : PolyTimeComputable fun q => pairFstD (pairFstD (pairSndD (pairFstD q))) :=
    hF.comp (hF.comp hT)
  have hv' : PolyTimeComputable fun q => pairSndD (pairFstD (pairSndD (pairFstD q))) :=
    hS.comp (hF.comp hT)
  have hw' : PolyTimeComputable fun q => pairFstD (pairSndD (pairSndD (pairFstD q))) :=
    hF.comp (hS.comp hT)
  have hr : PolyTimeComputable fun q => pairSndD (pairSndD (pairSndD (pairFstD q))) :=
    hS.comp (hS.comp hT)
  have hv : PolyTimeComputable fun q => pairFstD (pairSndD q) := hF.comp hS
  have hw : PolyTimeComputable fun q => pairSndD (pairSndD q) := hS.comp hS
  have hy := hX.pairEncode hu
  have hz' := hy.pairEncode hv'
  have hz := hy.pairEncode hv
  exact inter_mem_P (lenLe_poly_mem_P hT hW d.B d.b)
    (inter_mem_P (lenEq_poly_mem_P hu hX d.C₁ d.c₁)
      (union_mem_P
        (inter_mem_P (lenEq_poly_mem_P hv' hy d.C₂ d.c₂)
          (inter_mem_P (preimage_mem_P CVAL_mem_P (hU.pairEncode (hz'.append hw')))
            (inter_mem_P (lenLe_poly_mem_P hr hz' d.C₃ d.c₃)
              (preimage_mem_P hR (hz'.pairEncode hr)))))
        (compl_mem_P (inter_mem_P (lenEq_poly_mem_P hv hy d.C₂ d.c₂)
          (preimage_mem_P CVAL_mem_P (hU.pairEncode (hz.append hw)))))))

/-- **The counterexample language is in `coNP`**: its complement is "some bounded `e`
fails the check", a bounded-certificate `NP` statement over the `P` language `checkLangᶜ`. -/
theorem badLang_mem_coNP (hR : d.R ∈ P) : d.badLang ∈ coNP := by
  show d.badLangᶜ ∈ NP
  refine mem_NP_iff_exists_length_le.mpr ⟨d.B, d.b, d.checkLangᶜ,
    compl_mem_P (d.checkLang_mem_P hR), fun p => ?_⟩
  rw [Set.mem_compl_iff, mem_badLang]
  push_neg
  refine exists_congr fun e => and_congr_right fun _ => ?_
  show _ ↔ ¬ (_ ∈ d.checkLang)
  rw [mem_checkLang, pairFstD_pairEncode, pairSndD_pairEncode]

/-- **The inner language is in `Π₂ᵖ`**: its complement is a bounded `∃` (the check bounds
the universal block) over the `coNP` language `badLang`. -/
theorem innerLang_mem_PiP (hR : d.R ∈ P) : d.innerLang ∈ PiP 2 := by
  show d.innerLangᶜ ∈ SigmaP (1 + 1)
  refine mem_SigmaP_succ_of_exists_le (i := 1) (by rw [PiP_one]; exact d.badLang_mem_coNP hR)
    d.B d.b (fun w t ht hw => hw t ht) (fun w hw => ?_)
  rw [Set.mem_compl_iff, mem_innerLang] at hw
  push_neg at hw
  obtain ⟨t, ht⟩ := hw
  refine ⟨t, ?_, ht⟩
  have := ((mem_badLang d).mp ht [] (by simp)).1
  simpa using this

end Data

/-! ### Soundness and completeness -/

/-- **Soundness**: if `⟨x, U⟩` is in the inner language, then for every `u` of the right
length, `⟨x, u⟩ ∈ L₂ = ∃·K`. Nothing is assumed about `U`.

**Proof sketch.** The universal block `(u, ε, ε, ε)` must be answered by some `(v, w)`
that matches, since it is no soundness failure: `U` accepts `z = ⟨⟨x, u⟩, v⟩` with
certificate `w`. If `z ∉ K`, a refutation `r` exists, and the universal block
`(u, v, w, r)` is a soundness failure that no answer can defeat. So `z ∈ K`. -/
theorem sound {d : Data} {L₂ K : Language Bool}
    (hL₂ : ∀ y, y ∈ L₂ ↔ ∃ v : List Bool, v.length = d.M₂ y ∧ pairEncode y v ∈ K)
    (hK : ∀ z, z ∈ Kᶜ ↔
      ∃ r : List Bool, r.length ≤ d.C₃ * (z.length + 1) ^ d.c₃ ∧ pairEncode z r ∈ d.R)
    (hB : ∀ x U u v w r : List Bool, u.length = d.M₁ x → v.length ≤ d.M₂ (pairEncode x u) →
      w.length ≤ U.length → r.length ≤ d.C₃ * (d.nLen x + 1) ^ d.c₃ →
      (pairEncode (pairEncode u v) (pairEncode w r)).length ≤
        d.B * ((pairEncode x U).length + 1) ^ d.b)
    {x U : List Bool} (h : pairEncode x U ∈ d.innerLang) (u : List Bool)
    (hu : u.length = d.M₁ x) : pairEncode x u ∈ L₂ := by
  have key : ∀ t : List Bool, t.length ≤ d.B * ((pairEncode x U).length + 1) ^ d.b →
      ∃ e, ¬ d.Core x U t e := by
    intro t ht
    have h' := (d.mem_innerLang.mp h) t
    rw [Data.mem_badLang] at h'
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, Data.check_pair, not_forall] at h'
    obtain ⟨e, -, he⟩ := h'
    exact ⟨e, fun hc => he ⟨ht, hc⟩⟩
  -- the universal block `(u, ε, ε, ε)` is answered by a match
  obtain ⟨e, he⟩ := key (pairEncode (pairEncode u []) (pairEncode [] []))
    (hB x U u [] [] [] hu (by simp) (by simp) (by simp))
  simp only [Data.Core, pairFstD_pairEncode, pairSndD_pairEncode, hu, true_and, not_or,
    not_not] at he
  obtain ⟨-, hv, hq⟩ := he
  refine (hL₂ _).mpr ⟨pairFstD e, hv, ?_⟩
  -- the matched instance is in `K`: otherwise its refutation is a soundness failure
  by_contra hz
  obtain ⟨r, hr, hR⟩ := (hK _).mp hz
  have hzl := d.length_inst hu hv
  have hwl : (pairSndD e).length ≤ U.length :=
    le_trans (by simp) (length_le_of_query hq)
  obtain ⟨e₁, he₁⟩ := key (pairEncode (pairEncode u (pairFstD e)) (pairEncode (pairSndD e) r))
    (hB x U u _ _ r hu hv.le hwl (hzl ▸ hr))
  simp only [Data.Core, pairFstD_pairEncode, pairSndD_pairEncode, hu, true_and, not_or] at he₁
  exact he₁.1 ⟨hv, hq, hr, hR⟩

/-- **Completeness**: if `D` decides `K` as nondeterministic circuits and `x ∈ L`, then
`⟨x, ⌜D_{N(|x|)}⌝⟩` is in the inner language.

**Proof sketch.** Take a universal block `t` with `|u|` right (otherwise the check fails
outright). Since `⟨x, u⟩ ∈ ∃·K` there is `v` with `z = ⟨⟨x, u⟩, v⟩ ∈ K`, and a certificate
`y` with `D_{|z|}(z, y) = 1`; `|z| = N(|x|)`, so `e = ⟨v, y⟩` is a match. And `t` is no
soundness failure: an instance accepted by `D_{N(|x|)}` is in `K`, so it has no refutation. -/
theorem complete {d : Data} {L₂ K : Language Bool}
    (hL₂ : ∀ y, y ∈ L₂ ↔ ∃ v : List Bool, v.length = d.M₂ y ∧ pairEncode y v ∈ K)
    (hK : ∀ z, z ∈ Kᶜ ↔
      ∃ r : List Bool, r.length ≤ d.C₃ * (z.length + 1) ^ d.c₃ ∧ pairEncode z r ∈ d.R)
    {m : ℕ → ℕ} {D : (n : ℕ) → DAGCircuit (n + m n)} (hD : ∀ n, (D n).IsFaninTwo)
    (hKD : ∀ z : List Bool, z ∈ K ↔
      ∃ y : Fin (m z.length) → Bool, (D z.length).eval (Fin.append z.get y) = true)
    (hB : ∀ x U t v w : List Bool,
      v.length ≤ d.C₂ * (2 * x.length + 2 + d.M₁ x + 1) ^ d.c₂ → w.length ≤ U.length →
      (pairEncode v w).length ≤ d.B * ((pairEncode (pairEncode x U) t).length + 1) ^ d.b)
    {x : List Bool} (hx : ∀ u : List Bool, u.length = d.M₁ x → pairEncode x u ∈ L₂) :
    pairEncode x (D (d.nLen x)).encode ∈ d.innerLang := by
  rw [Data.mem_innerLang]
  intro t ht
  rw [Data.mem_badLang] at ht
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, Data.check_pair] at ht
  set U := (D (d.nLen x)).encode with hU
  set u := pairFstD (pairFstD t) with hu_def
  -- an instance of length `N(|x|)` accepted by `U` is in `K`
  have hqK : ∀ z w : List Bool, z.length = d.nLen x → Query U (z ++ w) → z ∈ K := by
    intro z w hz hq
    obtain ⟨y, -, hev⟩ := (query_append_iff D hD z w hz).mp hq
    exact (hKD z).mpr ⟨y, hev⟩
  by_cases hu : u.length = d.M₁ x
  · obtain ⟨v, hv, hz⟩ := (hL₂ _).mp (hx u hu)
    have hzl := d.length_inst hu hv
    obtain ⟨y, hy⟩ := (hKD _).mp hz
    have hm : (List.ofFn y).length ≤ U.length := by
      have hs := (D (pairEncode (pairEncode x u) v).length).size_le_length_encode
      simp only [DAGCircuit.size] at hs
      rw [List.length_ofFn, hU]
      rw [hzl] at hs ⊢
      omega
    have hvl : v.length ≤ d.C₂ * (2 * x.length + 2 + d.M₁ x + 1) ^ d.c₂ := by
      rw [hv, Data.M₂, length_pairEncode, hu]
    obtain ⟨-, -, hsf | hnm⟩ := ht (pairEncode v (List.ofFn y)) (hB x U t v _ hvl hm)
    · obtain ⟨hv', hq', hr', hR'⟩ := hsf
      exact (hK _).mpr ⟨_, hr', hR'⟩ (hqK _ _ (d.length_inst hu hv') hq')
    · simp only [pairFstD_pairEncode, pairSndD_pairEncode] at hnm
      exact hnm ⟨hv, (query_append_iff D hD _ _ hzl).mpr ⟨y, rfl, hy⟩⟩
  · exact hu (ht [] (by simp)).2.1

/-! ### Polynomial bounds -/

/-- Sums of polynomially bounded functions are polynomially bounded. -/
private theorem polyBound_add {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound fun n => f n + g n := by
  obtain ⟨A, α, hA⟩ := hf
  obtain ⟨B, β, hB⟩ := hg
  refine ⟨A + B, α + β, fun n => ?_⟩
  have h1 : (n + 1) ^ α ≤ (n + 1) ^ (α + β) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (n + 1) ^ β ≤ (n + 1) ^ (α + β) := Nat.pow_le_pow_right (by omega) (by omega)
  have := hA n
  have := hB n
  nlinarith

/-- A polynomial of a polynomially bounded function is polynomially bounded. -/
private theorem polyBound_comp {f : ℕ → ℕ} (hf : PolyBound f) (C c : ℕ) :
    PolyBound fun n => C * (f n + 1) ^ c := by
  obtain ⟨A, α, hA⟩ := hf
  refine ⟨C * (A + 1) ^ c, α * c, fun n => ?_⟩
  have hone : 1 ≤ (n + 1) ^ α := Nat.one_le_pow _ _ (by omega)
  have h1 : f n + 1 ≤ (A + 1) * (n + 1) ^ α := by have := hA n; nlinarith
  calc C * (f n + 1) ^ c ≤ C * ((A + 1) * (n + 1) ^ α) ^ c :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left h1 c)
    _ = C * (A + 1) ^ c * (n + 1) ^ (α * c) := by rw [mul_pow, ← pow_mul, mul_assoc]

/-- A constant multiple of a polynomially bounded function is polynomially bounded. -/
private theorem polyBound_smul (q : ℕ) {f : ℕ → ℕ} (hf : PolyBound f) :
    PolyBound fun n => q * f n := by
  obtain ⟨A, α, hA⟩ := hf
  exact ⟨q * A, α, fun n => by rw [mul_assoc]; exact Nat.mul_le_mul_left q (hA n)⟩

/-- `A (n+1)^α + 2s ≤ (A+2) W^{α+1}` when `n + 1 ≤ W` and `s ≤ W`. -/
private theorem bound_aux {A α n W s : ℕ} (hn : n + 1 ≤ W) (hs : s ≤ W) :
    A * (n + 1) ^ α + 2 * s ≤ (A + 2) * W ^ (α + 1) := by
  have hW : 1 ≤ W := by omega
  have h1 : (n + 1) ^ α ≤ W ^ (α + 1) :=
    (Nat.pow_le_pow_left hn α).trans (Nat.pow_le_pow_right hW (by omega))
  have h2 : W ≤ W ^ (α + 1) := by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ (α + 1) := Nat.pow_le_pow_right hW (by omega)
  nlinarith

end Complexity.Yap

namespace Complexity

open Turing BoolCircuit Yap

/-- **`Π₃ᵖ ⊆ Σ₃ᵖ` under `coNP ⊆ NP/poly`** (the core of [Yap83, Theorem 2]).

**Proof sketch.** Write `x ∈ L ⟺ ∀ u ∃ v, ⟨⟨x, u⟩, v⟩ ∈ K` with `K ∈ coNP` and
`z ∈ Kᶜ ⟺ ∃ r, ⟨z, r⟩ ∈ R`, and let `D` be `NP/poly` circuits for `K`. Then
`x ∈ L ⟺ ∃ U (|U| ≤ poly), ⟨x, U⟩ ∈ innerLang` with `innerLang ∈ Π₂ᵖ`: (⇐) by `sound`,
(⇒) with `U` the description of `D_{N(|x|)}` by `complete`. All lengths involved are
bounded by one polynomial `A (|x|+1)^α`, which fixes the bound constants of the checks. -/
theorem PiP_three_subset_SigmaP_three_of_coNP_subset_NPPoly
    (h : coNP ⊆ {L | L.InNPPoly}) : PiP 3 ⊆ SigmaP 3 := by
  intro L hL
  obtain ⟨C₁, c₁, L₂, hL₂S, hLx⟩ := mem_PiP_succ_iff.mp (show L ∈ PiP (2 + 1) from hL)
  obtain ⟨C₂, c₂, K, hKco, hL₂x⟩ := mem_SigmaP_two_iff.mp hL₂S
  obtain ⟨C₃, c₃, R, hR, hKc⟩ := mem_NP_iff_exists_length_le.mp (show Kᶜ ∈ NP from hKco)
  obtain ⟨a, k, m, D, hD, hDs, hKD⟩ := h hKco
  -- one polynomial bounding every length of the construction
  obtain ⟨A, α, hA⟩ : PolyBound fun n => 4 * (C₁ * (n + 1) ^ c₁) +
      2 * (C₂ * (2 * n + 2 + C₁ * (n + 1) ^ c₁ + 1) ^ c₂) + 8 +
      C₃ * (nN C₁ c₁ C₂ c₂ n + 1) ^ c₃ + 12 * (a * (nN C₁ c₁ C₂ c₂ n + 1) ^ k) ^ 2 := by
    have hP1 : PolyBound fun n => C₁ * (n + 1) ^ c₁ := ⟨C₁, c₁, fun _ => le_rfl⟩
    have hY : PolyBound fun n => 2 * n + 2 + C₁ * (n + 1) ^ c₁ :=
      polyBound_add ⟨4, 1, fun n => by nlinarith⟩ hP1
    have hM2 := polyBound_comp hY C₂ c₂
    have hN : PolyBound fun n => nN C₁ c₁ C₂ c₂ n :=
      polyBound_add (polyBound_add (polyBound_smul 2 hY) ⟨2, 0, fun n => by simp⟩) hM2
    have hsq : PolyBound fun n => (a * (nN C₁ c₁ C₂ c₂ n + 1) ^ k) ^ 2 := by
      obtain ⟨B, β, hB⟩ := polyBound_comp (polyBound_comp hN a k) 1 2
      refine ⟨B, β, fun n => (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans ?_⟩
      simpa only [one_mul] using hB n
    exact polyBound_add (polyBound_add (polyBound_add (polyBound_add (polyBound_smul 4 hP1)
      (polyBound_smul 2 hM2)) ⟨8, 0, fun n => by simp⟩) (polyBound_comp hN C₃ c₃))
      (polyBound_smul 12 hsq)
  let d : Data := ⟨C₁, c₁, C₂, c₂, C₃, c₃, A + 2, α + 1, R⟩
  have hBs : ∀ x U u v w r : List Bool, u.length = d.M₁ x → v.length ≤ d.M₂ (pairEncode x u) →
      w.length ≤ U.length → r.length ≤ d.C₃ * (d.nLen x + 1) ^ d.c₃ →
      (pairEncode (pairEncode u v) (pairEncode w r)).length ≤
        d.B * ((pairEncode x U).length + 1) ^ d.b := by
    intro x U u v w r hu hv hw hr
    have hE := hA x.length
    simp only [Data.M₁, Data.M₂, Data.nLen, length_pairEncode] at hu hv hr ⊢
    rw [hu] at hv
    have hb := bound_aux (A := A) (α := α) (n := x.length)
      (W := 2 * x.length + 2 + U.length + 1) (s := U.length) (by omega) (by omega)
    show _ ≤ (A + 2) * _
    nlinarith
  have hBc : ∀ x U t v w : List Bool,
      v.length ≤ d.C₂ * (2 * x.length + 2 + d.M₁ x + 1) ^ d.c₂ → w.length ≤ U.length →
      (pairEncode v w).length ≤ d.B * ((pairEncode (pairEncode x U) t).length + 1) ^ d.b := by
    intro x U t v w hv hw
    have hE := hA x.length
    beta_reduce at hE
    simp only [d, Data.M₁, length_pairEncode] at hv ⊢
    have hb := bound_aux (A := A) (α := α) (n := x.length)
      (W := 2 * (2 * x.length + 2 + U.length) + 2 + t.length + 1) (s := U.length)
      (by omega) (by omega)
    omega
  refine Yap.mem_SigmaP_succ_of_exists_le (i := 2) (d.innerLang_mem_PiP hR) A α
    (fun x U hU => (hLx x).mpr fun u hu => sound hL₂x hKc hBs hU u hu) (fun x hx => ?_)
  refine ⟨(D (d.nLen x)).encode, ?_, complete hL₂x hKc hD hKD hBc ((hLx x).mp hx)⟩
  have henc := (D (d.nLen x)).length_encode_le_of_isFaninTwo (hD _)
  have hsz := Nat.pow_le_pow_left (hDs (d.nLen x)) 2
  have hE := hA x.length
  beta_reduce at hE
  simp only [d, Data.nLen] at henc hsz ⊢
  omega

/-- **Yap's theorem** [Yap83, Theorem 2]: if `coNP ⊆ NP/poly` then `PH = Σ₃ᵖ`.

**Proof sketch.** `Π₃ᵖ ⊆ Σ₃ᵖ` (`PiP_three_subset_SigmaP_three_of_coNP_subset_NPPoly`) and
the collapse [AB09, Theorem 5.4] (`PH_eq_SigmaP_of_PiP_subset_SigmaP`). -/
theorem PH_eq_SigmaP_three_of_coNP_subset_NPPoly (h : coNP ⊆ {L | L.InNPPoly}) :
    PH = SigmaP 3 :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP (by norm_num)
    (PiP_three_subset_SigmaP_three_of_coNP_subset_NPPoly h)

end Complexity

namespace Randomized

open Complexity

/-- **[AB09, Exercise 7.8]**: if `3SATᶜ ∈ BP·NP` then `PH = Σ₃ᵖ`.

**Proof sketch.** `coNP ⊆ NP/poly` (`coNP_subset_NPPoly_of_compl_SAT3_mem_BPNP`, via
[AB09, Exercise 7.7]) and Yap's theorem (`PH_eq_SigmaP_three_of_coNP_subset_NPPoly`). -/
theorem PH_eq_SigmaP_three_of_compl_SAT3_mem_BPNP (h : SAT3ᶜ ∈ BPNP) : PH = SigmaP 3 :=
  PH_eq_SigmaP_three_of_coNP_subset_NPPoly (coNP_subset_NPPoly_of_compl_SAT3_mem_BPNP h)

end Randomized
