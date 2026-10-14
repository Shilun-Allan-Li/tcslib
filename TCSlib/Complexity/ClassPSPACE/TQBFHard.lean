/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassPSPACE.TQBFHardParams
import TCSlib.Complexity.ClassPSPACE.TQBFHardTseitin
import TCSlib.Complexity.CircuitComplexity.UniformTableau
import TCSlib.Complexity.CircuitComplexity.CircuitSatReduction
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.ClassNP.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `TQBF` is `PSPACE`-hard

[AB09, Theorem 4.13, hardness half]: every language in `PSPACE` reduces in polynomial time to
the true quantified Boolean formulas. Let `N` decide `L` in nondeterministic space
`d (n^c + 1)` (`Complexity.PSPACE_subset_NPSPACE`). On input `x` of length `n` the reduction
outputs the encoding of a closed formula

`∃ Z₀ A B ∃ Z_w ∀ U_w ∀ V_w ⋯ ∃ Z₁ ∀ U₁ ∀ V₁ ∃ (auxiliary) · matrix`

over blocks of `w = wCoef N d · (n + 1)^(c + 1)` variables, `w` levels deep:

* **the `ψᵢ` recursion** ([AB09]'s `∀`-folding, `TQBFHardSemantics`): truth of the prefix of
  the levels is the midpoint recursion over the one-step relation of blocks, i.e. a path of
  `2^w` steps (`Complexity.TQBFHard.prefixTruth_top`, `Complexity.TQBFHard.mid_iff_steps`);
* **the configuration graph** (`TQBFHardMachine`): blocks carry code words of the
  configuration codec `Complexity.Codec`, and an initial block reaches an accepting block in
  `2^w` steps iff `x ∈ L` (`Complexity.TQBFHard.mem_iff_mid`; `2^w` bounds the vertex count,
  `Complexity.TQBFHard.configBound_le_two_pow`);
* **the matrix** is the predicate "the block at `w` is initial, the block at `2w` is
  accepting, and the selection chain of the levels ends in a step", computed by the
  polynomial-time verifier `Complexity.TQBFHard.predB` (`TQBFHardVerifier`,
  `TQBFHardBridge`), written as a circuit — the uniform configuration tableau
  `Complexity.cfgTab` of a machine computing the verifier, with `⟨x, ·⟩` hard-wired — and
  turned into a CNF by Tseitin's transformation `BoolCircuit.DAGCircuit.toCNF`, whose gate
  variables are quantified existentially after the whole prefix
  (`Complexity.QBF.truth_exSuffix_of_pointwise` with `Complexity.TQBFHard.toCNF_extension_iff`).

**Polynomial time.** The reduction is a composition of polynomial-time maps: the unary input
`1^{3w(w+1)} 0 1^T 0 ⟨x, ⟩` of the tableau emitter (`Complexity.polyTimeComputable_tabInput`),
the emitter itself (`Complexity.UTab.polyTimeComputable_tabEmit`, [AB09, Remark 6.7]), the
CKT-SAT-to-SAT map (`BoolCircuit.polyTimeComputable_dagCktSatToSAT3`, [AB09, Lemma 6.11]),
and the prefix bits (`Complexity.TQBFHard.polyTimeComputable_levelBits`).

**Deviation from the book's route.** [AB09] writes `ψ₀` as a CNF for the adjacency of two
configurations (Claim 4.4(2)) and leaves the reduction's running time to the reader. Here the
matrix of the whole prenex formula is one polynomial-time predicate, made a CNF by the
P-uniform tableau and Tseitin, so that no configuration-specific CNF (and no emitter for one)
is needed; the configuration codec `Complexity.ConfigCodec` of `ClassPSPACE.TQBF` is not
used. The midpoints quantify over all blocks without a validity guard: the one-step
relation of blocks is "equal, or a step pair of codes", and a step pair's target is always a
code word, so junk midpoints only occur on trivial (equality) paths.

## Main definitions

* `Complexity.TQBFHard.redQuants`, `Complexity.TQBFHard.redCircuit`,
  `Complexity.TQBFHard.redQBF`, `Complexity.TQBFHard.redMap` — the reduction.

## Main results

* `Complexity.TQBFHard.truth_redQBF` — the formula is true iff `x ∈ L`.
* `Complexity.TQBFHard.polyTimeComputable_redMap` — the reduction is polynomial-time.
* `Complexity.TQBFHard.PSPACE_polyTimeReducible_TQBF` — `L ∈ PSPACE` reduces to the true
  quantified Boolean formulas. [AB09, Theorem 4.13, hardness half]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Theorem 4.13 and its proof; §6.1, Remark 6.7 and
  Lemma 6.11.)
* [SM73] L. Stockmeyer, A. Meyer, *Word problems requiring exponential time*, STOC 1973.
  (Cited through [AB09].)
-/

namespace Complexity

namespace TQBFHard

open Turing BoolCircuit Codec QBF Std.Sat

/-- **The CKT-SAT reduction map on a description** of a fan-in-two circuit is the
serialization of its Tseitin formula. -/
theorem dagCktSatToSAT3_encode {n : ℕ} (C : DAGCircuit n) (hC : C.IsFaninTwo) :
    dagCktSatToSAT3 C.encode = CNF.serialize C.toCNF := by
  simp [dagCktSatToSAT3, dagCktSatToCNF, DAGCircuit.decode_encode, hC]

variable (N : FinNDTM Bool) (d c : ℕ) (V : FinTM Bool) (CV cV : ℕ)

/-- The block width `w = wCoef N d · (n + 1)^(c + 1)`. -/
def redW (n : ℕ) : ℕ := vwid (wCoef N d) (c + 1) n

/-- The number `3w(w + 1)` of prefix variables. -/
def redM (n : ℕ) : ℕ := 3 * redW N d c n * redW N d c n + 3 * redW N d c n

/-- The constant bounding `|⟨x, σ⟩| + 1` by `K (n + 1)^(2(c + 1))`. -/
def redK : ℕ := 3 * wCoef N d * wCoef N d + 3 * wCoef N d + 3

/-- The tableau's time bound: at least the verifier's running time on `⟨x, σ⟩`, and `≥ 1`. -/
def redT (n : ℕ) : ℕ := CV * redK N d ^ cV * (n + 1) ^ (2 * (c + 1) * cV) + 1

/-- **The matrix circuit**: the uniform tableau of the verifier machine `V` for
`redT n` steps, on `3w(w + 1)` free inputs (the prefix variables) after the hard-wired word
`⟨x, ` (`pairEncode x []`). -/
noncomputable def redCircuit (x : List Bool) : DAGCircuit (redM N d c x.length) :=
  cfgTab V (redM N d c x.length) (pairEncode x []) (redT N d c CV cV x.length)

/-- **The quantifier prefix**: three existential blocks (the pad `Z₀`, the source `A`, the
target `B`), then `w` levels `∃^w ∀^w ∀^w`. -/
def redQuants (n : ℕ) : List Quant :=
  List.replicate (redW N d c n) .ex ++ (List.replicate (redW N d c n) .ex ++
    (List.replicate (redW N d c n) .ex ++ levelQuants (redW N d c n) (redW N d c n)))

/-- **The quantified formula**: the prefix, then one existential per letter of the
serialized matrix (enough for every Tseitin variable), and the Tseitin formula of the matrix
circuit. -/
noncomputable def redQBF (x : List Bool) : QBF :=
  ⟨redQuants N d c x.length ++
      List.replicate (CNF.serialize (redCircuit N d c V CV cV x).toCNF).length .ex,
    (redCircuit N d c V CV cV x).toCNF⟩

/-- **The reduction map**: the encoding of `redQBF x`. -/
noncomputable def redMap (x : List Bool) : List Bool := QBF.encode (redQBF N d c V CV cV x)

/-- The prefix has `3w(w + 1)` variables. -/
theorem length_redQuants (n : ℕ) : (redQuants N d c n).length = redM N d c n := by
  simp only [redQuants, List.length_append, List.length_replicate, length_levelQuants, redM]
  ring

/-- **The verifier runs within the tableau's time bound** on `⟨x, σ⟩`, `|σ| = 3w(w + 1)`.

**Proof sketch.** With `P = (n + 1) ^ (c + 1)` and `A = wCoef N d`, the input length is
`|⟨x, σ⟩| + 1 = 2n + 3 + 3A²P² + 3AP ≤ redK · P² = redK · (n + 1) ^ (2(c + 1))` (using
`n + 1 ≤ P ≤ P²`); raising to `cV` and multiplying by `CV` gives
`CV · redK ^ cV · (n + 1) ^ (2(c + 1) cV) ≤ redT`. -/
theorem time_le (x σ : List Bool) (hσ : σ.length = redM N d c x.length) :
    CV * ((pairEncode x σ).length + 1) ^ cV ≤ redT N d c CV cV x.length := by
  set n := x.length
  set A := wCoef N d
  set P := (n + 1) ^ (c + 1)
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hnP : n + 1 ≤ P := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hPP : P ≤ P * P := Nat.le_mul_of_pos_right _ hP1
  have hlen : (pairEncode x σ).length + 1 ≤ redK N d * (n + 1) ^ (2 * (c + 1)) := by
    rw [length_pairEncode, hσ]
    have e1 : (n + 1) ^ (2 * (c + 1)) = P * P := by rw [two_mul, pow_add]
    have e2 : redM N d c n = 3 * A * A * (P * P) + 3 * A * P := by
      simp only [redM, redW, vwid, A, P]; ring
    rw [e1, e2]
    have h1 : 3 * A * P ≤ 3 * A * (P * P) := Nat.mul_le_mul_left _ hPP
    have h2 : 2 * n + 3 ≤ 3 * (P * P) := by nlinarith
    have e3 : redK N d * (P * P) = 3 * A * A * (P * P) + 3 * A * (P * P) + 3 * (P * P) := by
      simp only [redK, A]; ring
    rw [e3]
    omega
  calc CV * ((pairEncode x σ).length + 1) ^ cV
      ≤ CV * (redK N d * (n + 1) ^ (2 * (c + 1))) ^ cV :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen _)
    _ = CV * redK N d ^ cV * (n + 1) ^ (2 * (c + 1) * cV) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ redT N d c CV cV n := Nat.le_succ _

/-- **The matrix circuit computes the verifier** on `⟨x, σ⟩`, `σ` its input assignment.

**Proof sketch.** `Complexity.cfgTab_eval`: the tableau outputs `1` iff `V` emits `1` within
`redT` steps on `⟨x, ⟩ ++ σ = ⟨x, σ⟩`; `V` computes `[predB ⟨x, σ⟩]` within that time
(`time_le`), so this is `predB ⟨x, σ⟩` (`Complexity.decide_emits_eq_of_computesInTime`). -/
theorem eval_redCircuit
    (hV : V.ComputesFunInTime (fun y => [predB N d c (wCoef N d) (c + 1) y])
      (fun m => CV * (m + 1) ^ cV))
    (x : List Bool) (τ : ℕ → Bool) :
    (redCircuit N d c V CV cV x).eval (fun i => τ i) =
      predB N d c (wCoef N d) (c + 1)
        (pairEncode x (List.ofFn fun j : Fin (redM N d c x.length) => τ j)) := by
  set σ := List.ofFn fun j : Fin (redM N d c x.length) => τ j
  have hσ : σ.length = redM N d c x.length := by simp [σ]
  have hz : pairEncode x [] ++ σ = pairEncode x σ := by
    simp [pairEncode, List.append_assoc]
  rw [redCircuit, cfgTab_eval, hz]
  exact decide_emits_eq_of_computesInTime
    ((hV (pairEncode x σ)).mono (time_le N d c CV cV x σ hσ))

variable {N d c}

/-- **The formula is true iff `x ∈ L`** ([AB09, Theorem 4.13, the proof]): for `N` deciding
`L` in space `d (n^c + 1)` and `V` computing the verifier in time `CV (m + 1)^{cV}`.

**Proof sketch.** Tseitin after the prefix (`Complexity.QBF.truth_exSuffix_of_pointwise`,
`toCNF_extension_iff`; the serialization is longer than the number of variables,
`numVars_le_length_serialize`) leaves the prefix truth of "the circuit accepts the prefix
assignment", which is the verifier (`eval_redCircuit`), i.e. the initial and accepting tests
and the flat matrix (`predB_iff`), i.e. the prenex `ψ` matrix (`levelMatrix_iff_flat`). Its
prefix truth is "some initial `A` reaches some accepting `B` in the midpoint recursion of
depth `w`" (`prefixTruth_top`), which is `x ∈ L` (`mem_iff_mid`, with the radius at least the
space bound and the width bounds `vlen_le_vwid`, `configBound_le_two_pow`). -/
theorem truth_redQBF {L : Language Bool} (hN : N.DecidesInSpace L fun n => d * (n ^ c + 1))
    (hV : V.ComputesFunInTime (fun y => [predB N d c (wCoef N d) (c + 1) y])
      (fun m => CV * (m + 1) ^ cV))
    (x : List Bool) : (redQBF N d c V CV cV x).truth ↔ x ∈ L := by
  set n := x.length
  set w := redW N d c n with hw
  set s := vrad d c n
  set Lc := vlen N d c n
  set C := redCircuit N d c V CV cV x
  have hqlen := length_redQuants N d c n
  -- Tseitin after the prefix
  rw [redQBF, truth_exSuffix_of_pointwise (redQuants N d c n) C.toCNF _
    (fun σ => C.eval (fun i => σ i) = true)
    ((numVars_le_length_serialize _).trans (Nat.le_add_left _ _))
    (fun σ => by rw [hqlen]; exact toCNF_extension_iff C (cfgTab_isFaninTwo _ _ _ _).2 σ)]
  -- the circuit is the prenex matrix
  have hleaf : ∀ τ : ℕ → Bool, C.eval (fun i => τ i) = true ↔
      blockInit N x s Lc (readBlock τ w w) ∧ blockAcc N x s Lc (readBlock τ (2 * w) w) ∧
        levelMatrix w (blockStep N x s Lc) w (3 * w) (readBlock τ w w)
          (readBlock τ (2 * w) w) τ := by
    intro τ
    rw [eval_redCircuit N d c V CV cV hV x τ]
    have hflat := levelMatrix_iff_flat w (blockStep N x s Lc) τ w 0
    simp only [Nat.zero_add, Nat.mul_one, uRec, vRec, Nat.mul_zero] at hflat
    rw [hflat]
    exact predB_iff N d c (wCoef N d) (c + 1) x τ (vlen_le_vwid N d c n)
  rw [prefixTruth_congr hleaf]
  rw [redQuants, prefixTruth_top]
  have hs : d * (n ^ c + 1) ≤ s := by
    have h1 : n ^ c ≤ (n + 1) ^ c := Nat.pow_le_pow_left (by omega) _
    have h2 : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
    have : d * (n ^ c + 1) ≤ d * (2 * (n + 1) ^ c) := Nat.mul_le_mul_left _ (by omega)
    simp only [s, vrad]
    linarith
  exact (mem_iff_mid N hN x s w hs (vlen_le_vwid N d c n) (configBound_le_two_pow N d c n)).symm

variable (N d c)

/-- The unary number of prefix variables is polynomial-time. -/
theorem pt_redM : PolyTimeComputable fun x => List.replicate (redM N d c x.length) true := by
  have h := (polyTimeComputable_polyUnary (3 * wCoef N d * wCoef N d) (2 * (c + 1))).append
    (polyTimeComputable_polyUnary (3 * wCoef N d) (c + 1))
  convert h using 1
  funext x
  rw [← List.replicate_add]
  congr 1
  simp only [redM, redW, vwid, two_mul, pow_add]
  ring

/-- **The reduction is polynomial-time** ([AB09, Theorem 4.13]: "the formula can be computed
in polynomial time").

**Proof sketch.** `redMap x` is the pair of the prefix bits and the serialized Tseitin
formula. The formula is the CKT-SAT map (`BoolCircuit.polyTimeComputable_dagCktSatToSAT3`)
of the tableau emitter's output (`Complexity.UTab.polyTimeComputable_tabEmit`,
`Complexity.UTab.tabEmit_eq`) on the polynomial-time input `1^M 0 1^T 0 ⟨x, ⟩`
(`Complexity.polyTimeComputable_tabInput`); the prefix bits are `1^{3w}`, the level bits
(`polyTimeComputable_levelBits`), and one `1` per letter of the formula. -/
theorem polyTimeComputable_redMap : PolyTimeComputable (redMap N d c V CV cV) := by
  have hT : PolyTimeComputable fun x =>
      List.replicate (redT N d c CV cV x.length) true := by
    have := (polyTimeComputable_polyUnary (CV * redK N d ^ cV) (2 * (c + 1) * cV)).append
      (polyTimeComputable_const [true])
    convert this using 1
    funext x
    simp [redT, List.replicate_add]
  have hinp := polyTimeComputable_tabInput (pt_redM N d c) hT
    (polyTimeComputable_id.pairEncode (polyTimeComputable_const []))
  have hser := polyTimeComputable_dagCktSatToSAT3.comp
    ((UTab.polyTimeComputable_tabEmit V).comp hinp)
  have hser_eq : ∀ x, (dagCktSatToSAT3 ∘ UTab.tabEmit V ∘ fun x =>
      List.replicate (redM N d c x.length) true ++ false ::
        (List.replicate (redT N d c CV cV x.length) true ++ false :: pairEncode (id x) [])) x =
      CNF.serialize (redCircuit N d c V CV cV x).toCNF := by
    intro x
    simp only [Function.comp, id]
    rw [UTab.tabEmit_eq V _ _ _ (by simp [redT]), dagCktSatToSAT3_encode _
      (cfgTab_isFaninTwo _ _ _ _)]
    rfl
  have h3w : PolyTimeComputable fun x =>
      List.replicate (3 * redW N d c x.length) true := by
    have := polyTimeComputable_polyUnary (3 * wCoef N d) (c + 1)
    convert this using 1
    funext x
    simp only [redW, vwid]
    ring_nf
  have hlev := polyTimeComputable_levelBits (w := fun x => redW N d c x.length)
    (polyTimeComputable_polyUnary (wCoef N d) (c + 1))
  have hall := ((h3w.append hlev).append (polyTimeComputable_unary.comp hser)).pairEncode hser
  convert hall using 1
  funext x
  have hs : dagCktSatToSAT3 (UTab.tabEmit V (List.replicate (redM N d c x.length) true ++
      false :: (List.replicate (redT N d c CV cV x.length) true ++ false :: pairEncode x []))) =
      CNF.serialize (redCircuit N d c V CV cV x).toCNF := by
    simpa using hser_eq x
  simp only [Function.comp, id, hs]
  simp only [redMap, QBF.encode, redQBF, redQuants, List.map_append, List.map_replicate,
    map_quantBit_levelQuants, quantBit]
  congr 1
  rw [show 3 * redW N d c x.length =
      redW N d c x.length + redW N d c x.length + redW N d c x.length by ring,
    List.replicate_add, List.replicate_add]
  simp only [List.append_assoc]

/-- **`PSPACE` reduces to `TQBF`** ([AB09, Theorem 4.13, hardness half]): every language in
`PSPACE` Karp-reduces in polynomial time to the set of strings whose decoded quantified
Boolean formula is true.

**Proof sketch.** `L ∈ NPSPACE` (`Complexity.PSPACE_subset_NPSPACE`): some `N` decides `L` in
space `d (n^c + 1)`. The verifier of the reduction is polynomial-time
(`polyTimeComputable_predB`); take a machine `V` computing it. The map `redMap` is
polynomial-time (`polyTimeComputable_redMap`) and decodes to `redQBF x`
(`Complexity.QBF.decode_encode`), which is true iff `x ∈ L` (`truth_redQBF`). -/
theorem PSPACE_polyTimeReducible_TQBF {L : Language Bool} (hL : L ∈ PSPACE) :
    L ≤ₚ {x | (QBF.decode x).truth} := by
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (PSPACE_subset_NPSPACE hL)
  obtain ⟨d, N, hN⟩ := hc
  obtain ⟨V, CV, cV, hV⟩ := polyTimeComputable_predB N d c (wCoef N d) (c + 1)
  refine ⟨redMap N d c V CV cV, polyTimeComputable_redMap N d c V CV cV, fun x => ?_⟩
  show x ∈ L ↔ (QBF.decode (QBF.encode (redQBF N d c V CV cV x))).truth
  rw [QBF.decode_encode]
  exact (truth_redQBF V CV cV hN hV x).symm

end TQBFHard

end Complexity
