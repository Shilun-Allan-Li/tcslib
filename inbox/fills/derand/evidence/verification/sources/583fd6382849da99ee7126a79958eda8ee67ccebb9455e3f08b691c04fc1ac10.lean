/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `NP/poly` and `BP·NP ⊆ NP/poly`

Nondeterministic polynomial-size circuits and [AB09, Exercise 7.7]: every language randomly
reducible to `3SAT` has them, by fixing good reduction coins as advice (Adleman's argument).
The first step of [AB09, Exercise 7.8] follows.

## Main definitions

* `Language.InNPPoly` — `NP/poly`, polynomial-size nondeterministic circuits
  [AB09, Exercise 7.7].
* `Randomized.wireVal` — the value carried by a circuit wire (free bit or constant).

## Main results

* `Randomized.BPNP_subset_NPPoly` — `BP·NP ⊆ NP/poly` [AB09, Exercise 7.7].
* `Randomized.NP_subset_NPPoly` — `NP ⊆ NP/poly`.
* `Randomized.coNP_subset_NPPoly_of_compl_SAT3_mem_BPNP` — `3SATᶜ ∈ BP·NP ⇒ coNP ⊆ NP/poly`,
  the first step of [AB09, Exercise 7.8].
* `Randomized.exists_good_coins` — coins good for every input of a length (by the union bound
  `Randomized.exists_forall_not_of_randProb_le`); `Randomized.inNPPoly_of_wiring` — circuits
  from `P` by wiring.

## Divergences

* **`NP/poly`.** A nondeterministic circuit on `x ∈ {0,1}ⁿ`, `y ∈ {0,1}^{m(n)}` is a fan-in-two
  `DAGCircuit (n + m n)` read on `Fin.append x y`; "polynomial size" is `a(n+1)^k`, the repair
  of `Language.InPPoly`. The certificate length is bounded by the size, which counts inputs.
* **Exercise 7.8.** Its hypothesis is `3SATᶜ ∈ BP·NP` (the overbar is lost in the printed
  text: `3SAT ∈ BP·NP` holds outright). This file derives `coNP ⊆ NP/poly`; the collapse
  `PH = Σ₃ᵖ` follows by Yap's theorem in `TCSlib.Complexity.Randomized.Yap`
  (`Randomized.PH_eq_SigmaP_three_of_compl_SAT3_mem_BPNP`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Complexity Turing

/-! ### Fixing good coins for every input of a length -/

open Classical in
/-- **Good coins for the amplified reduction** (the Adleman step of [AB09, Exercise 7.7]):
at every length `n`, some string of `K = 36(n+1)` blocks of reduction coins makes the
majority of the `K` reduced instances correct for *every* input of length `n`.

**Proof sketch.** For a fixed input the `K` blocks are independent runs of the reduction,
each wrong with probability at most `1/3`, so the binomial tail bound (`randProb_tail_le`)
bounds the probability that at least half are wrong by `2(8/9)^{18(n+1)} ≤ 2^{-(n+1)}`; the
union bound over the `2^n` inputs (`exists_forall_not_of_randProb_le`) leaves a string good
for all of them. For a good string, the correct blocks are a strict majority, so `x ∈ L`
exactly when a strict majority of the reduced instances lie in `C`. -/
theorem exists_good_coins {L C : Language Bool} {f : List Bool → List Bool} {a k : ℕ}
    (hprob : ∀ x : List Bool,
      2/3 ≤ randProb (polyLen a k x.length) fun r => (f (Turing.pairEncode x r) ∈ C ↔ x ∈ L))
    (n : ℕ) : ∃ ρ : Fin (polyLen 36 1 n * polyLen a k n) → Bool, ∀ v : Fin n → Bool,
      (List.ofFn v ∈ L ↔ polyLen 36 1 n < 2 * (List.range (polyLen 36 1 n)).countP fun i =>
        decide (f (Turing.pairEncode (List.ofFn v)
          (((List.ofFn ρ).drop (i * polyLen a k n)).take (polyLen a k n))) ∈ C)) := by
  set q := polyLen a k n
  set K := polyLen 36 1 n
  let Bx : (Fin n → Bool) → List Bool → Bool := fun v r =>
    decide (f (Turing.pairEncode (List.ofFn v) r) ∈ C ↔ List.ofFn v ∈ L)
  have hK : K / 2 = 18 * (n + 1) := by
    simp only [K, polyLen, pow_one]
    omega
  have hbad : ∀ v, randProb (K * q) (fun l => K ≤ 2 * blockCount q K (fun r => !Bx v r) l) ≤
      (1/2 : ℚ) ^ (n + 1) := by
    intro v
    have h1 : 2/3 ≤ randProb q (fun r => Bx v r = true) := by
      have := hprob (List.ofFn v)
      rw [List.length_ofFn] at this
      exact this.trans_eq (randProb_congr fun r => by simp [Bx])
    have h2 : randProb q (fun r => (!Bx v r) = true) = 1 - randProb q (fun r => Bx v r = true) := by
      rw [← randProb_bool_false]
      exact randProb_congr fun r => by simp
    have ht := randProb_tail_le q K (fun r => !Bx v r) (ε := 1/6) (by norm_num) (by linarith)
    have hpow : (1 - 1/9 : ℚ) ^ (K / 2) ≤ (1/2) ^ (n + 2) :=
      one_sub_pow_le_half_pow (m := 9) (by norm_num) (by norm_num) (by norm_num) (by omega)
    calc randProb (K * q) (fun l => K ≤ 2 * blockCount q K (fun r => !Bx v r) l)
        ≤ 2 * (1 - 4 * (1/6 : ℚ) ^ 2) ^ (K / 2) := ht
      _ = 2 * (1 - 1/9 : ℚ) ^ (K / 2) := by norm_num
      _ ≤ 2 * (1/2 : ℚ) ^ (n + 2) := by linarith
      _ = (1/2 : ℚ) ^ (n + 1) := by ring
  have hδ : (2 : ℚ) ^ n * (1/2) ^ (n + 1) < 1 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num
  obtain ⟨ρ, hρ⟩ := exists_forall_not_of_randProb_le _ hbad hδ
  refine ⟨ρ, fun v => ?_⟩
  have hgood := hρ v
  -- the correct and the wrong blocks are all the blocks
  have hsum := blockCount_add_not q K (Bx v) (List.ofFn ρ)
  by_cases hx : List.ofFn v ∈ L
  · have hS : blockCount q K (Bx v) (List.ofFn ρ) = (List.range K).countP fun i =>
        decide (f (Turing.pairEncode (List.ofFn v) (((List.ofFn ρ).drop (i * q)).take q)) ∈ C) :=
      List.countP_congr fun i _ => by simp [Bx, hx]
    simp only [hx, true_iff]
    omega
  · have hS : blockCount q K (fun r => !Bx v r) (List.ofFn ρ) = (List.range K).countP fun i =>
        decide (f (Turing.pairEncode (List.ofFn v) (((List.ofFn ρ).drop (i * q)).take q)) ∈ C) :=
      List.countP_congr fun i _ => by simp [Bx, hx]
    simp only [hx, false_iff, not_lt]
    omega

/-! ### `NP/poly` -/

/-- **`NP/poly`** [AB09, Exercise 7.7]: `L` is decided by polynomial-size nondeterministic
circuits — fan-in-two circuits `Cₙ` on an input `x ∈ {0,1}ⁿ` and a certificate
`y ∈ {0,1}^{m(n)}`, of size at most `a(n+1)^k`, with `x ∈ L ↔ ∃ y, C_{|x|}(x, y) = 1`. -/
def _root_.Language.InNPPoly (L : Language Bool) : Prop :=
  ∃ (a k : ℕ) (m : ℕ → ℕ) (C : (n : ℕ) → BoolCircuit.DAGCircuit (n + m n)),
    (∀ n, (C n).IsFaninTwo) ∧ (∀ n, (C n).size ≤ a * (n + 1) ^ k) ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ y : Fin (m x.length) → Bool, (C x.length).eval (Fin.append x.get y) = true

/-- The value carried by a wire: a free input bit or a constant. -/
def wireVal {N : ℕ} (v : Fin N → Bool) : Fin N ⊕ Bool → Bool :=
  Sum.elim v id

/-- Reading a circuit's buffered inputs back as a word evaluates the wire list. -/
theorem ofFn_inputValues_vectorOfList {N : ℕ} (w : List (Fin N ⊕ Bool)) (v : Fin N → Bool) :
    List.ofFn (BoolCircuit.inputValues (BoolCircuit.vectorOfList w rfl) v) =
      w.map (wireVal v) := by
  have e1 : List.ofFn (BoolCircuit.inputValues (BoolCircuit.vectorOfList w rfl) v) =
      (List.ofFn (BoolCircuit.vectorOfList w rfl)).map (wireVal v) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [BoolCircuit.inputValues, Function.comp_apply, wireVal]
    rcases BoolCircuit.vectorOfList w rfl i with j | b <;> rfl
  rw [e1, BoolCircuit.vectorOfList_ofFn]

/-- **Nondeterministic circuits from a `P`-language and a wiring.** If membership in `L` is
"some certificate `y ∈ {0,1}^{m(|x|)}` makes the word read off the wire list `wire |x|`
(free bits from `(x, y)`, the rest constants) land in `W ∈ P`", and the wire lists and
certificates are polynomially long, then `L ∈ NP/poly`.

**Proof sketch.** `P ⊆ P/poly` gives a fan-in-two family for `W`; feed the circuit for the
wire list's length through one buffer gate per wire (`BoolCircuit.DAGCircuit.bufferInputs`),
which copies the selected free input or supplies the constant. Size is the free inputs plus
the old circuit, polynomial in `n`. -/
theorem inNPPoly_of_wiring {L W : Language Bool} (hW : W ∈ P) (m : ℕ → ℕ)
    (wire : (n : ℕ) → List (Fin (n + m n) ⊕ Bool)) (b j : ℕ)
    (hlen : ∀ n, (wire n).length + 1 ≤ b * (n + 1) ^ j) (hm : ∀ n, n + m n ≤ b * (n + 1) ^ j)
    (hL : ∀ x : List Bool, x ∈ L ↔ ∃ y : Fin (m x.length) → Bool,
      (wire x.length).map (wireVal (Fin.append x.get y)) ∈ W) : L.InNPPoly := by
  have hPoly : W.InPPoly := P_subset_PPoly hW
  obtain ⟨bF, jF, F, hF, hSize, hLang⟩ := hPoly
  refine ⟨b + bF * b ^ jF, j * (jF + 1), m,
    fun n => (F.circuit (wire n).length).bufferInputs (BoolCircuit.vectorOfList (wire n) rfl),
    fun n => ((F.circuit _).bufferInputs_structure _ (hF _)).2.1, fun n => ?_, fun x => ?_⟩
  · rw [((F.circuit _).bufferInputs_structure _ (hF _)).2.2]
    have hN : 0 < n + 1 := Nat.succ_pos n
    have hj1 : (n + 1) ^ j ≤ (n + 1) ^ (j * (jF + 1)) :=
      Nat.pow_le_pow_right hN (Nat.le_mul_of_pos_right j (Nat.succ_pos jF))
    have hj2 : (n + 1) ^ (j * jF) ≤ (n + 1) ^ (j * (jF + 1)) :=
      Nat.pow_le_pow_right hN (Nat.mul_le_mul_left j (Nat.le_succ jF))
    calc n + m n + (F.circuit (wire n).length).size
        ≤ b * (n + 1) ^ j + bF * (b * (n + 1) ^ j) ^ jF :=
          Nat.add_le_add (hm n) ((hSize _).trans
            (Nat.mul_le_mul_left bF (Nat.pow_le_pow_left (hlen n) jF)))
      _ = b * (n + 1) ^ j + bF * b ^ jF * (n + 1) ^ (j * jF) := by
          rw [mul_pow, ← pow_mul]
          ring
      _ ≤ b * (n + 1) ^ (j * (jF + 1)) + bF * b ^ jF * (n + 1) ^ (j * (jF + 1)) :=
          Nat.add_le_add (Nat.mul_le_mul_left b hj1) (Nat.mul_le_mul_left _ hj2)
      _ = (b + bF * b ^ jF) * (n + 1) ^ (j * (jF + 1)) := by ring
  · rw [hL x]
    refine exists_congr fun y => ?_
    rw [BoolCircuit.DAGCircuit.bufferInputs_eval, ← BoolCircuit.DAGCircuitFamily.mem_language_ofFn,
      ofFn_inputValues_vectorOfList, hLang]

/-! ### Block bookkeeping -/

/-- Doubling every entry doubles the length. -/
private theorem length_flatMap_dup {α : Type*} (l : List α) :
    (l.flatMap fun s => [s, s]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    ring

/-- Doubling the images is doubling, then mapping. -/
private theorem flatMap_dup_map {α β : Type*} (g : α → β) (l : List α) :
    l.flatMap (fun a => [g a, g a]) = (l.map g).flatMap fun b => [b, b] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.map_cons, ih]

/-- Concatenating `K` chunks of length `c` gives length `K · c`. -/
private theorem length_flatMap_range {α : Type*} (g : ℕ → List α) {c : ℕ} :
    ∀ K : ℕ, (∀ j < K, (g j).length = c) → ((List.range K).flatMap g).length = K * c
  | 0, _ => by simp
  | K + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.length_append,
      length_flatMap_range g K fun j hj => h j (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, h K (by omega)]
    ring

/-- Chunk `i` of a concatenation of `K` chunks of length `c` is recovered by slicing. -/
private theorem flatMap_range_drop_take {α : Type*} (g : ℕ → List α) {c : ℕ} :
    ∀ K i : ℕ, (∀ j < K, (g j).length = c) → i < K →
      (((List.range K).flatMap g).drop (i * c)).take c = g i
  | 0, i, _, hi => absurd hi (Nat.not_lt_zero _)
  | K + 1, i, h, hi => by
    have hA := length_flatMap_range g K fun j hj => h j (by omega)
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have hle : i * c + c ≤ K * c := by
        have := Nat.mul_le_mul_right c (Nat.succ_le_of_lt hi)
        rwa [Nat.succ_mul] at this
      rw [List.drop_append_of_le_length (by rw [hA]; omega),
        List.take_append_of_le_length (by rw [List.length_drop, hA]; omega)]
      exact flatMap_range_drop_take g K i (fun j hj => h j (by omega)) hi
    · rw [List.drop_left' hA, List.take_of_length_le (by rw [h i (by omega)])]

/-- Block `i < K` of a string of `K` blocks of length `c` has length `c`. -/
private theorem length_block {α : Type*} {l : List α} {K c i : ℕ} (hl : l.length = K * c)
    (hi : i < K) :
    ((l.drop (i * c)).take c).length = c := by
  have hle : i * c + c ≤ K * c := by
    have := Nat.mul_le_mul_right c (Nat.succ_le_of_lt hi)
    rwa [Nat.succ_mul] at this
  rw [List.length_take, List.length_drop, hl]
  omega

/-! ### `BP·NP ⊆ NP/poly` -/

open Classical in
/-- **`BP·NP ⊆ NP/poly`** [AB09, Exercise 7.7].

**Proof sketch.** Let `L ≤ᵣ 3SAT` via `f` with `q = polyLen a₁ k₁ |x|` coins. Fix, for every
length `n`, a string `ρ` of `K = 36(n+1)` coin blocks such that for every `x ∈ {0,1}ⁿ`,
`x ∈ L` iff a strict majority of the formulas `f(x, ρᵢ)` is satisfiable
(`exists_good_coins`, the Adleman argument). This majority of `NP`-statements is itself an
`NP`-statement: the certificate supplies, per block, a padded `3SAT` certificate for `f(x, ρᵢ)`,
and the verifier counts the blocks whose certificate checks — a satisfiable formula can
always be certified, an unsatisfiable one never. Interleaving `ρᵢ` with the certificate
blocks, this count is the block-majority test `Complexity.mem_P_of_blockMajority` of a
`P`-language (the reduction followed by the `3SAT` verifier, via `composeMap`). The
interleaving is done by wiring (`inNPPoly_of_wiring`): the coin bits of `ρ` become constants
and the certificate bits become the nondeterministic inputs of the circuit. -/
theorem BPNP_subset_NPPoly : BPNP ⊆ {L | L.InNPPoly} := by
  intro L hL
  obtain ⟨f, a₁, k₁, hf, hprob⟩ := hL
  obtain ⟨Cf, cf, hCf⟩ := hf.output_length_le
  obtain ⟨C₃, c₃, V₃, hV₃, hSAT⟩ := SAT3_mem_NP
  choose ρ hρ using exists_good_coins hprob
  set A := C₃ * ((Cf + 1) * (a₁ + 3) ^ cf) ^ c₃ with hA
  set Ke := (k₁ + 1) * cf * c₃ with hKe
  set ab := a₁ + A with hab
  set kb := k₁ + Ke with hkb
  have hqb : ∀ n, polyLen a₁ k₁ n + polyLen A Ke n ≤ polyLen ab kb n := by
    intro n
    have h1 : (n + 1) ^ k₁ ≤ (n + 1) ^ kb := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
    have h2 : (n + 1) ^ Ke ≤ (n + 1) ^ kb := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
    simp only [polyLen, hab]
    nlinarith [Nat.mul_le_mul_left a₁ h1, Nat.mul_le_mul_left A h2]
  -- slot length for one `3SAT` certificate, and the certificate length
  let u : ℕ → ℕ := fun n => polyLen ab kb n - polyLen a₁ k₁ n
  let m : ℕ → ℕ := fun n => polyLen 36 1 n * u n
  have hwit : ∀ (x r : List Bool), r.length = polyLen a₁ k₁ x.length →
      C₃ * ((f (Turing.pairEncode x r)).length + 1) ^ c₃ ≤ u x.length := by
    intro x r hr
    have h := polyLen_length_pairEncode_le hCf a₁ k₁ C₃ c₃ hr
    rw [← hA, ← hKe] at h
    have h' := hqb x.length
    show polyLen C₃ c₃ (f (Turing.pairEncode x r)).length ≤
      polyLen ab kb x.length - polyLen a₁ k₁ x.length
    omega
  -- the per-block `P`-language and the block-majority language
  let cm := composeMap a₁ k₁ C₃ c₃ f
  have hcm : PolyTimeComputable cm := polyTimeComputable_composeMap _ _ _ _ hf
  let V₁ : Language Bool := (fun z => pairFstD (cm z) ++ pairSndD (cm z)) ⁻¹' V₃
  have hV₁ : V₁ ∈ P := preimage_mem_P hV₃
    ((polyTimeComputable_pairFstD.comp hcm).append (polyTimeComputable_pairSndD.comp hcm))
  have hV₁iff : ∀ x t : List Bool, Turing.pairEncode x t ∈ V₁ ↔
      f (Turing.pairEncode x (t.take (polyLen a₁ k₁ x.length))) ++
        (t.drop (polyLen a₁ k₁ x.length)).take (C₃ * ((f (Turing.pairEncode x
          (t.take (polyLen a₁ k₁ x.length)))).length + 1) ^ c₃) ∈ V₃ := by
    intro x t
    show pairFstD (cm _) ++ pairSndD (cm _) ∈ V₃ ↔ _
    simp only [cm, composeMap_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode, polyLen]
  -- the coin blocks interleaved with certificate blocks
  let ρb : ℕ → ℕ → List Bool := fun n i =>
    ((List.ofFn (ρ n)).drop (i * polyLen a₁ k₁ n)).take (polyLen a₁ k₁ n)
  let Yb : ℕ → List Bool → ℕ → List Bool := fun n Y i => (Y.drop (i * u n)).take (u n)
  let sb : ℕ → List Bool → List Bool := fun n Y =>
    (List.range (polyLen 36 1 n)).flatMap fun i => ρb n i ++ Yb n Y i
  have hρl : ∀ n, (List.ofFn (ρ n)).length = polyLen 36 1 n * polyLen a₁ k₁ n :=
    fun n => List.length_ofFn
  have hqu : ∀ n, polyLen a₁ k₁ n + u n = polyLen ab kb n := fun n => by
    have := hqb n
    simp only [u]
    omega
  let Wset : Language Bool := {z | 36 * ((pairFstD z).length + 1) ^ 1 <
    2 * (List.range (36 * ((pairFstD z).length + 1) ^ 1)).countP
      (fun i => MultiTapeTM.indicator V₁ (Turing.pairEncode (pairFstD z) (blockAt ab kb z i)))}
  have hW : Wset ∈ P := mem_P_of_blockMajority hV₁ ab kb 36 1
  -- `x ∈ L` iff some certificate string puts the interleaving into `Wset`
  have hchar : ∀ x : List Bool, x ∈ L ↔ ∃ Y : List Bool, Y.length = m x.length ∧
      Turing.pairEncode x (sb x.length Y) ∈ Wset := by
    intro x
    set n := x.length with hn
    have hL' := hρ n x.get
    rw [List.ofFn_get] at hL'
    -- the number of satisfiable reduced instances, and of certified blocks
    let S : ℕ := (List.range (polyLen 36 1 n)).countP fun i =>
      decide (f (Turing.pairEncode x (ρb n i)) ∈ SAT3)
    let T : List Bool → ℕ := fun Y => (List.range (polyLen 36 1 n)).countP fun i =>
      decide (f (Turing.pairEncode x (ρb n i)) ++ (Yb n Y i).take
        (C₃ * ((f (Turing.pairEncode x (ρb n i))).length + 1) ^ c₃) ∈ V₃)
    have hLS : x ∈ L ↔ polyLen 36 1 n < 2 * S := hL'
    have hwit' : ∀ i < polyLen 36 1 n,
        C₃ * ((f (Turing.pairEncode x (ρb n i))).length + 1) ^ c₃ ≤ u n :=
      fun i hi => hwit x _ (length_block (hρl n) hi)
    have hWiff : ∀ Y : List Bool, Y.length = polyLen 36 1 n * u n →
        (Turing.pairEncode x (sb n Y) ∈ Wset ↔ polyLen 36 1 n < 2 * T Y) := by
      intro Y hY
      have hblk : ∀ i < polyLen 36 1 n,
          blockAt ab kb (Turing.pairEncode x (sb n Y)) i = ρb n i ++ Yb n Y i := by
        intro i hi
        unfold blockAt
        simp only [pairFstD_pairEncode, pairSndD_pairEncode]
        show ((sb n Y).drop (i * polyLen ab kb n)).take (polyLen ab kb n) = _
        rw [← hqu n]
        exact flatMap_range_drop_take (fun i => ρb n i ++ Yb n Y i) (polyLen 36 1 n) i
          (fun j hj => by
            rw [List.length_append, length_block (hρl n) hj, length_block hY hj]) hi
      have hcount : (List.range (polyLen 36 1 n)).countP (fun i => MultiTapeTM.indicator V₁
          (Turing.pairEncode x (blockAt ab kb (Turing.pairEncode x (sb n Y)) i))) = T Y := by
        refine List.countP_congr fun i hi => ?_
        have hi' := List.mem_range.mp hi
        have ht1 : (ρb n i ++ Yb n Y i).take (polyLen a₁ k₁ n) = ρb n i :=
          List.take_left' (length_block (hρl n) hi')
        have ht2 : (ρb n i ++ Yb n Y i).drop (polyLen a₁ k₁ n) = Yb n Y i :=
          List.drop_left' (length_block (hρl n) hi')
        have hind : ∀ z, MultiTapeTM.indicator V₁ z = decide (z ∈ V₁) := fun z => by
          unfold MultiTapeTM.indicator
          split_ifs with h <;> simp [h]
        rw [hblk i hi', hind, decide_eq_true_iff, decide_eq_true_iff, hV₁iff, ht1, ht2]
      have hmem : Turing.pairEncode x (sb n Y) ∈ Wset ↔
          36 * ((pairFstD (Turing.pairEncode x (sb n Y))).length + 1) ^ 1 <
            2 * (List.range
              (36 * ((pairFstD (Turing.pairEncode x (sb n Y))).length + 1) ^ 1)).countP
              (fun i => MultiTapeTM.indicator V₁ (Turing.pairEncode
                (pairFstD (Turing.pairEncode x (sb n Y)))
                (blockAt ab kb (Turing.pairEncode x (sb n Y)) i))) := Iff.rfl
      rw [hmem, pairFstD_pairEncode]
      show polyLen 36 1 n < 2 * (List.range (polyLen 36 1 n)).countP (fun i =>
        MultiTapeTM.indicator V₁ (Turing.pairEncode x
          (blockAt ab kb (Turing.pairEncode x (sb n Y)) i))) ↔ _
      rw [hcount]
    -- a certified block has a satisfiable instance
    have hTS : ∀ Y : List Bool, Y.length = polyLen 36 1 n * u n → T Y ≤ S := by
      intro Y hY
      refine List.countP_mono_left fun i hi h => ?_
      have hi' := List.mem_range.mp hi
      rw [decide_eq_true_iff] at h ⊢
      refine (hSAT _).mpr ⟨_, ?_, h⟩
      rw [List.length_take, length_block hY hi']
      exact min_eq_left (hwit' i hi')
    -- every satisfiable instance can be certified in its slot
    have hST : ∃ Y : List Bool, Y.length = polyLen 36 1 n * u n ∧ S ≤ T Y := by
      classical
      let w : ℕ → List Bool := fun i =>
        if h : f (Turing.pairEncode x (ρb n i)) ∈ SAT3 then Classical.choose ((hSAT _).mp h)
        else []
      have hw : ∀ i, f (Turing.pairEncode x (ρb n i)) ∈ SAT3 →
          (w i).length = C₃ * ((f (Turing.pairEncode x (ρb n i))).length + 1) ^ c₃ ∧
            f (Turing.pairEncode x (ρb n i)) ++ w i ∈ V₃ := fun i h => by
        simp only [w, dif_pos h]
        exact Classical.choose_spec ((hSAT _).mp h)
      have hwl : ∀ i < polyLen 36 1 n, (w i).length ≤ u n := fun i hi => by
        by_cases h : f (Turing.pairEncode x (ρb n i)) ∈ SAT3
        · rw [(hw i h).1]
          exact hwit' i hi
        · simp only [w, dif_neg h, List.length_nil]
          exact Nat.zero_le _
      let Yc : ℕ → List Bool := fun i => w i ++ List.replicate (u n - (w i).length) false
      have hYc : ∀ i < polyLen 36 1 n, (Yc i).length = u n := fun i hi => by
        simp only [Yc, List.length_append, List.length_replicate]
        have := hwl i hi
        omega
      refine ⟨(List.range (polyLen 36 1 n)).flatMap Yc,
        length_flatMap_range Yc _ hYc, List.countP_mono_left fun i hi h => ?_⟩
      have hi' := List.mem_range.mp hi
      rw [decide_eq_true_iff] at h ⊢
      have hblk : Yb n ((List.range (polyLen 36 1 n)).flatMap Yc) i = Yc i :=
        flatMap_range_drop_take Yc _ i hYc hi'
      rw [hblk, List.take_left' (hw i h).1]
      exact (hw i h).2
    constructor
    · intro hx
      obtain ⟨Y, hY, hle⟩ := hST
      have := hLS.mp hx
      exact ⟨Y, hY, (hWiff Y hY).mpr (by omega)⟩
    · rintro ⟨Y, hY, hYW⟩
      have h1 := (hWiff Y hY).mp hYW
      have h2 := hTS Y hY
      exact hLS.mpr (by omega)
  -- the circuits: coin bits as constants, certificate bits as nondeterministic inputs
  let wire : (n : ℕ) → List (Fin (n + m n) ⊕ Bool) := fun n =>
    (List.ofFn fun j : Fin n => (Sum.inl (Fin.castAdd (m n) j) : Fin (n + m n) ⊕ Bool)).flatMap
        (fun s => [s, s]) ++ [Sum.inr false, Sum.inr true] ++
      (List.range (polyLen 36 1 n)).flatMap fun i => (ρb n i).map Sum.inr ++
        (((List.ofFn fun j : Fin (m n) => (Sum.inl (Fin.natAdd n j) : Fin (n + m n) ⊕ Bool)).drop
          (i * u n)).take (u n))
  have hwire : ∀ n (v : Fin n → Bool) (y : Fin (m n) → Bool),
      (wire n).map (wireVal (Fin.append v y)) =
        Turing.pairEncode (List.ofFn v) (sb n (List.ofFn y)) := by
    intro n v y
    simp [wire, sb, Yb, wireVal, Turing.pairEncode, flatMap_dup_map, List.map_flatMap,
      Function.comp_def]
  have hK : ∀ n, polyLen 36 1 n * polyLen ab kb n = 36 * ab * (n + 1) ^ (kb + 1) := fun n => by
    simp only [polyLen]
    ring
  have hwlen : ∀ n, (wire n).length = 2 * n + 2 + polyLen 36 1 n * polyLen ab kb n := by
    intro n
    simp only [wire, List.length_append, length_flatMap_dup, List.length_ofFn, List.length_cons,
      List.length_nil]
    rw [length_flatMap_range _ (polyLen 36 1 n) (c := polyLen ab kb n) fun j hj => by
      rw [List.length_append, List.length_map, length_block (hρl n) hj,
        length_block (l := List.ofFn fun j : Fin (m n) =>
          (Sum.inl (Fin.natAdd n j) : Fin (n + m n) ⊕ Bool)) List.length_ofFn hj]
      exact hqu n]
  refine inNPPoly_of_wiring hW m wire (3 + 36 * ab) (kb + 1) (fun n => ?_) (fun n => ?_)
    (fun x => ?_)
  · rw [hwlen, hK]
    have h1 : n + 1 ≤ (n + 1) ^ (kb + 1) := Nat.le_self_pow (Nat.succ_ne_zero kb) _
    nlinarith
  · have h0 : m n ≤ polyLen 36 1 n * polyLen ab kb n :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    rw [hK] at h0
    have h1 : n + 1 ≤ (n + 1) ^ (kb + 1) := Nat.le_self_pow (Nat.succ_ne_zero kb) _
    nlinarith
  · rw [hchar x]
    constructor
    · rintro ⟨Y, hY, hYW⟩
      obtain ⟨y, rfl⟩ := exists_ofFn_eq hY
      exact ⟨y, by rw [hwire, List.ofFn_get]; exact hYW⟩
    · rintro ⟨y, hy⟩
      rw [hwire, List.ofFn_get] at hy
      exact ⟨List.ofFn y, List.length_ofFn, hy⟩

/-- `NP ⊆ NP/poly`; follows from [AB09, Exercise 7.7] and `NP ⊆ BP·NP`. -/
theorem NP_subset_NPPoly : NP ⊆ {L | L.InNPPoly} :=
  fun _ hL => BPNP_subset_NPPoly (NP_subset_BPNP hL)

/-- **The first step of [AB09, Exercise 7.8]**: if `3SATᶜ ∈ BP·NP` then `coNP ⊆ NP/poly`.
(The exercise's conclusion `PH = Σ₃ᵖ` is `Randomized.PH_eq_SigmaP_three_of_compl_SAT3_mem_BPNP`
in `TCSlib.Complexity.Randomized.Yap`, by Yap's theorem.)

**Proof sketch.** A `coNP` language Karp-reduces to `3SATᶜ` by the Cook–Levin reduction of
its complement; compose with the randomized reduction `3SATᶜ ≤ᵣ 3SAT`
(`RandReducible.of_polyTimeReducible_left`) and apply `BPNP_subset_NPPoly`. -/
theorem coNP_subset_NPPoly_of_compl_SAT3_mem_BPNP (h : SAT3ᶜ ∈ BPNP) :
    coNP ⊆ {L | L.InNPPoly} := by
  intro L hL
  obtain ⟨g, hg, hgL⟩ := SAT3_NPHard Lᶜ hL
  have hred : L ≤ₚ SAT3ᶜ := ⟨g, hg, fun x => by
    rw [Set.mem_compl_iff, ← hgL x, Set.mem_compl_iff, not_not]⟩
  exact BPNP_subset_NPPoly (RandReducible.of_polyTimeReducible_left hred h)

end Randomized
