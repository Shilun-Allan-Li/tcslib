/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Word
import TCSlib.Complexity.SpaceComplexity.Codec.Scan
import Mathlib.Data.Fintype.Option

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Recognizing code words by a finite-state scan

A word is the code of a window-bounded configuration exactly when it has the right length,
its position field holds a value at most `|x| + 1`, it ends with `1`, and its chunk region
passes a finite-state scan (`Complexity.Codec.vScan`): every chunk is a chunk of some cell
value, the header occurs in the leftmost chunk only, and every work tape has exactly one
head flag. The same scan collects what a logspace checker needs about the configuration —
the header (control state and output summary) and the symbols under the work heads — and a
flag recognizing the blank, heads-together shape of the initial configuration.

Configuration-graph infrastructure for the codec checkers; not a result of [AB09].

## Main definitions

* `Complexity.Codec.decChunk` — the cell value of a chunk, if any.
* `Complexity.Codec.vStep`, `Complexity.Codec.vScan` — the validity scan.
* `Complexity.Codec.ValidChk` — the validity test on words.

## Main results

* `Complexity.Codec.foldl_vStep` — the scan in closed form.
* `Complexity.Codec.validChk_iff` — a word passes the test iff it is a code word.
* `Complexity.Codec.vScan_cfgWord` — what the scan reports on a code word.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1.)
-/

namespace Complexity.Codec

open Turing LogProg

variable (N : FinNDTM Bool)

/-! ## Decoding chunks -/

open Classical in
/-- The cell value whose chunk is `ch`, if there is one. -/
noncomputable def decChunk (ch : List Bool) : Option (CellV N) :=
  if h : ∃ cv, encChunk N cv = ch then some (Classical.choose h) else none

/-- Decoding inverts the chunk encoding. -/
@[simp] lemma decChunk_encChunk (cv : CellV N) : decChunk N (encChunk N cv) = some cv := by
  classical
  unfold decChunk
  rw [dif_pos ⟨cv, rfl⟩]
  exact congrArg some (encChunk_injective N (Classical.choose_spec (⟨cv, rfl⟩ :
    ∃ c, encChunk N c = encChunk N cv)))

/-- A decoded chunk is the chunk of its value. -/
lemma encChunk_of_decChunk {ch : List Bool} {cv : CellV N} (h : decChunk N ch = some cv) :
    encChunk N cv = ch := by
  classical
  unfold decChunk at h
  split_ifs at h with hex
  cases h
  exact Classical.choose_spec hex

/-! ## The validity scan -/

/-- The state of the validity scan: at the first chunk, the header read, which tapes have
shown a head, the symbols under the heads, the validity verdict, and the initial-shape
verdict. -/
abbrev VSt := Bool × Option (Hd N) × (Fin N.k → Bool) × (Fin N.k → Option Bool) × Bool × Bool

set_option synthInstance.maxSize 1000 in
/-- Validity-scan states are finitely many. -/
instance VSt.instFintype : Fintype (VSt N) := inferInstance

set_option synthInstance.maxSize 1000 in
/-- Validity-scan states have decidable equality. -/
instance VSt.instDecidableEq : DecidableEq (VSt N) := inferInstance

/-- A cell value of the initial shape: blank on every tape, and either every head or none. -/
def BlankTogether (cv : CellV N) : Prop :=
  (∀ i, (cv.2 i).1 = none) ∧ ((∀ i, (cv.2 i).2 = true) ∨ ∀ i, (cv.2 i).2 = false)

instance (cv : CellV N) : Decidable (BlankTogether N cv) := by
  unfold BlankTogether; infer_instance

/-- The initial state of the validity scan. -/
def vInit : VSt N := (true, none, fun _ => false, fun _ => none, true, true)

/-- **One chunk of the validity scan**: record the header at the first chunk; check that
the header occurs exactly there; record head flags and the symbols under them, rejecting a
second head on a tape; track the initial shape. -/
def vStep (st : VSt N) (cv : CellV N) : VSt N :=
  (false, (if st.1 then cv.1 else st.2.1), (fun i => st.2.2.1 i || (cv.2 i).2),
    (fun i => if (cv.2 i).2 then (cv.2 i).1 else st.2.2.2.1 i),
    st.2.2.2.2.1 && (if st.1 then cv.1.isSome else cv.1.isNone) &&
      decide (∀ i, ¬ (st.2.2.1 i = true ∧ (cv.2 i).2 = true)),
    st.2.2.2.2.2 && decide (BlankTogether N cv))

/-- The validity scan on a possibly undecodable chunk: undecodable chunks reject. -/
def vStepO (st : VSt N) : Option (CellV N) → VSt N
  | none => (st.1, st.2.1, st.2.2.1, st.2.2.2.1, false, st.2.2.2.2.2)
  | some cv => vStep N st cv

/-- The validity scan on a raw chunk of letter pairs (the first letters are the chunk). -/
noncomputable def vChunk (st : VSt N) (ch : List (Bool × Bool)) : VSt N :=
  vStepO N st (decChunk N (ch.map Prod.fst))

/-- **The validity scan of a chunk region** `u`, letter by letter through the chunk
adaptor. -/
noncomputable def vScan (u : List Bool) : VSt N :=
  ((List.zip u u).foldl (adStep (w := hH N + 3 * N.k) (vChunk N))
    (vInit N, 0, fun _ => (false, false))).1

/-- The validity verdict of a scan state: valid so far, and every tape has a head. -/
def VAcc (st : VSt N) : Prop := st.2.2.2.2.1 = true ∧ ∀ i, st.2.2.1 i = true

instance (st : VSt N) : Decidable (VAcc N st) := by unfold VAcc; infer_instance

/-- **The validity scan in closed form**: after the chunks `f 0, …, f (J - 1)`, the scan
holds the header of `f 0`, the head flags seen, the symbol under the last head flag of each
tape, and the verdicts "the header occurs exactly in the first chunk and no tape has two
head flags" and "every chunk has the initial shape".

**Proof sketch.** Induction on `J`, unfolding one `vStep`; each component is the
corresponding statement about one more chunk. -/
theorem foldl_vStep (f : ℕ → CellV N) (J : ℕ) :
    let st := ((List.range J).map f).foldl (vStep N) (vInit N)
    st.1 = decide (J = 0) ∧ st.2.1 = (if J = 0 then none else (f 0).1) ∧
      (∀ i, st.2.2.1 i = decide (∃ j < J, ((f j).2 i).2 = true)) ∧
      (∀ i, (∀ j < J, ((f j).2 i).2 = false) → st.2.2.2.1 i = none) ∧
      (∀ i j, j < J → ((f j).2 i).2 = true → (∀ j', j < j' → j' < J → ((f j').2 i).2 = false) →
        st.2.2.2.1 i = ((f j).2 i).1) ∧
      st.2.2.2.2.1 = decide ((∀ j < J, ((f j).1.isSome ↔ j = 0)) ∧
        ∀ i, ∀ j₁ < J, ∀ j₂ < J, ((f j₁).2 i).2 = true → ((f j₂).2 i).2 = true → j₁ = j₂) ∧
      st.2.2.2.2.2 = decide (∀ j < J, BlankTogether N (f j)) := by
  induction J with
  | zero =>
    dsimp only
    simp only [List.range_zero, List.map_nil, List.foldl_nil]
    exact ⟨by simp [vInit], by simp [vInit], fun i => by simp [vInit], fun i _ => by simp [vInit],
      fun i j hj => by omega, by simp [vInit], by simp [vInit]⟩
  | succ J ih =>
    simp only at ih ⊢
    rw [List.range_succ, List.map_append, List.foldl_append]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih
    set st := ((List.range J).map f).foldl (vStep N) (vInit N)
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, vStep]
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1, h2]
      rcases Nat.eq_zero_or_pos J with rfl | hJ
      · simp
      · simp [show J ≠ 0 by omega]
    · intro i
      rw [h3 i, Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨j, hj, hh⟩ | hh)
        · exact ⟨j, by omega, hh⟩
        · exact ⟨J, by omega, hh⟩
      · rintro ⟨j, hj, hh⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact Or.inl ⟨j, hj, hh⟩
        · exact Or.inr hh
    · intro i hall
      rw [if_neg (by simp [hall J (by omega)])]
      exact h4 i fun j hj => hall j (by omega)
    · intro i j hj hh hlast
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [if_neg (by simp [hlast J hj (by omega)])]
        exact h5 i j hj hh fun j' h1 h2 => hlast j' h1 (by omega)
      · rw [if_pos hh]
    · simp only [h6, h1, h3]
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      have slot : ((if J = 0 then (f J).1.isSome else (f J).1.isNone) = true) ↔
          ((f J).1.isSome ↔ J = 0) := by
        by_cases hJ : J = 0 <;> simp [hJ, Option.isNone_iff_eq_none, Option.isSome_iff_ne_none]
      simp only [slot]
      constructor
      · rintro ⟨⟨⟨hs, hu⟩, hJ⟩, hd⟩
        refine ⟨fun j hj => ?_, fun i j₁ hj₁ j₂ hj₂ a b => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact hs j hj
          · exact hJ
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj₁ with hj₁ | rfl <;>
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj₂ with hj₂ | rfl
          · exact hu i j₁ hj₁ j₂ hj₂ a b
          · exact absurd ⟨by simpa using ⟨j₁, hj₁, a⟩, b⟩ (hd i)
          · exact absurd ⟨by simpa using ⟨j₂, hj₂, b⟩, a⟩ (hd i)
          · rfl
      · rintro ⟨hs, hu⟩
        refine ⟨⟨⟨fun j hj => hs j (by omega), fun i j₁ hj₁ j₂ hj₂ =>
          hu i j₁ (by omega) j₂ (by omega)⟩, hs J (by omega)⟩, fun i ⟨a, b⟩ => ?_⟩
        obtain ⟨j, hj, hh⟩ := a
        exact absurd (hu i j (by omega) J (by omega) hh b) (by omega)
    · rw [h7, Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨h, hJ⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h j hj
        · exact hJ
      · intro h
        exact ⟨fun j hj => h j (by omega), h J (by omega)⟩

/-- An undecodable chunk makes the verdict reject, and a rejecting verdict persists. -/
lemma vStepO_ok_false (st : VSt N) (o : Option (CellV N)) (h : st.2.2.2.2.1 = false) :
    (vStepO N st o).2.2.2.2.1 = false := by
  cases o with
  | none => rfl
  | some cv => simp [vStepO, vStep, h]

/-- A fold of the scan from a rejecting state stays rejecting. -/
lemma foldl_vStepO_ok_false (L : List (Option (CellV N))) (st : VSt N)
    (h : st.2.2.2.2.1 = false) : (L.foldl (vStepO N) st).2.2.2.2.1 = false := by
  induction L generalizing st with
  | nil => exact h
  | cons o L ih => exact ih _ (vStepO_ok_false N st o h)

/-- On decodable chunks the scan is the cell-level scan. -/
lemma foldl_vStepO_some (L : List (CellV N)) (st : VSt N) :
    (L.map some).foldl (vStepO N) st = L.foldl (vStep N) st := by
  induction L generalizing st with
  | nil => rfl
  | cons cv L ih => exact ih _

/-- A word of `w · m` letters is the concatenation of its `m` blocks of `w` letters. -/
lemma eq_flatten_blocks {α : Type} (u : List α) (w m : ℕ) (h : u.length = w * m) :
    u = (List.ofFn fun j : Fin m => (u.drop (w * j)).take w).flatten := by
  induction m generalizing u with
  | zero => simp_all
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    have e := ih (u.drop w) (by simp [h, Nat.mul_succ])
    have blocks : (List.ofFn fun j : Fin m => (u.drop (w * (j.succ : ℕ))).take w) =
        List.ofFn fun j : Fin m => ((u.drop w).drop (w * j)).take w := by
      congr 1
      funext j
      rw [List.drop_drop]
      congr 2
      simp only [Fin.val_succ]
      ring
    simp only [Fin.val_zero, Nat.mul_zero, List.drop_zero]
    rw [blocks, ← e, List.take_append_drop]

/-- An `ofFn` list over `Fin m` of a function of the index is a map over `range m`. -/
lemma ofFn_eq_map_range {β : Type} (g : ℕ → β) (m : ℕ) :
    (List.ofFn fun j : Fin m => g j) = (List.range m).map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- **The scan of a chunk region is the chunk-level scan** of its decoded blocks.

**Proof sketch.** Split the region into its blocks (`eq_flatten_blocks`); zipping the
region with itself zips block by block (`zip_flatten`); the adaptor folds block by block
(`foldl_adStep_flatten`), and the first letters of a self-zipped block are the block. -/
theorem vScan_eq (u : List Bool) (m : ℕ) (h : u.length = W N * m) :
    vScan N u = ((List.range m).map fun j => decChunk N ((u.drop (W N * j)).take (W N))).foldl
      (vStepO N) (vInit N) := by
  have hu := eq_flatten_blocks u (W N) m h
  set blocks := List.ofFn fun j : Fin m => (u.drop (W N * j)).take (W N) with hb
  have hlen : ∀ b ∈ blocks, b.length = W N := by
    intro b hbm
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hbm
    have := j.isLt
    have : W N * j + W N ≤ u.length := by
      rw [h, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
    simp; omega
  have hz : List.zip u u = (List.zipWith List.zip blocks blocks).flatten := by
    conv_lhs => rw [hu]
    exact zip_flatten blocks blocks rfl (fun _ _ _ => rfl)
  unfold vScan
  rw [hz]
  obtain ⟨buf, e⟩ := foldl_adStep_flatten (w := hH N + 3 * N.k) (vChunk N) (vInit N)
    (List.zipWith List.zip blocks blocks)
    (by
      intro ch hch
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hch
      simp only [List.getElem_zipWith, List.length_zip, min_self]
      exact hlen _ (List.getElem_mem _))
    (fun _ => (false, false))
  rw [e]
  simp only
  have : List.zipWith List.zip blocks blocks = blocks.map fun b => List.zip b b := by
    induction blocks with
    | nil => rfl
    | cons b bs ih => simp
  rw [this, List.foldl_map]
  have hfst : ∀ b : List Bool, (List.zip b b).map Prod.fst = b := by
    intro b; induction b with
    | nil => rfl
    | cons a b ih => simp [ih]
  simp only [vChunk, hfst, hb, ofFn_eq_map_range (fun j => (u.drop (W N * j)).take (W N)),
    List.foldl_map]

/-! ## The validity test -/

/-- The output word of a summary index: `[]`, `[true]`, `[false]`. -/
def outOf : Fin 3 → List Bool
  | 0 => []
  | 1 => [true]
  | 2 => [false]

/-- The summary index of `outOf o` is `o`. -/
@[simp] lemma sumIdx_outOf (o : Fin 3) : sumIdx (outSummary (outOf o)) = o := by
  fin_cases o <;> rfl

/-- Block `j` (of `W N` letters) of a chunk region. -/
def block (u : List Bool) (j : ℕ) : List Bool := (u.drop (W N * j)).take (W N)

/-- Blocks of a chunk word are the chunks. -/
lemma block_chunksWord (f : ℕ → CellV N) (m j : ℕ) (hj : j < m) :
    block N (chunksWord N f m) j = encChunk N (f j) := by
  unfold block chunksWord
  rw [take_drop_flatten _ (W N) (by simp) j (by simpa using hj)]
  simp

variable {N}

/-- The cell function of a window-`s` region read back as a configuration: the header of
the leftmost cell gives the state and an output word with that summary, cell `j` gives the
tape symbols at position `j - s`, and the head of a tape is at its (first) flagged cell. -/
noncomputable def mkCfg (x : List Bool) (s : ℕ) (f : ℕ → CellV N) (pos : Fin (x.length + 2)) :
    Cfg N.k Bool N.State x := by
  classical exact
  ⟨((f 0).1.map Prod.fst).getD none, pos,
    fun i z => if |z| ≤ s then ((f (z + s).toNat).2 i).1 else none,
    fun i => if h : ∃ j, j < 2 * s + 1 ∧ ((f j).2 i).2 = true then (Nat.find h : ℤ) - s else 0,
    outOf (((f 0).1.map Prod.snd).getD 0)⟩

/-- **Reading back a well-formed region**: if the header occurs exactly in the leftmost of
the `2s + 1` cells and every tape has exactly one head flag, the configuration read back is
window-bounded and has exactly these cells.

**Proof sketch.** The leftmost header gives the state and an output with the recorded
summary (`sumIdx_outOf`); cell `j` lists the tape symbols at `j - s` by construction; the
head of each tape is placed at its unique flagged cell (`Nat.find`), so the head flags agree,
and all heads and nonblank cells lie in `[-s, s]`. -/
theorem cellOf_mkCfg (x : List Bool) (s : ℕ) (f : ℕ → CellV N) (pos : Fin (x.length + 2))
    (hslot : ∀ j < 2 * s + 1, ((f j).1.isSome ↔ j = 0))
    (huniq : ∀ i, ∀ j₁ < 2 * s + 1, ∀ j₂ < 2 * s + 1,
      ((f j₁).2 i).2 = true → ((f j₂).2 i).2 = true → j₁ = j₂)
    (hex : ∀ i, ∃ j < 2 * s + 1, ((f j).2 i).2 = true) :
    Cfg.InWindow s (mkCfg x s f pos) ∧ ∀ j < 2 * s + 1, cellOf s (mkCfg x s f pos) j = f j := by
  classical
  have hpos : ∀ i, ∃ j < 2 * s + 1, ((f j).2 i).2 = true ∧
      (mkCfg x s f pos).workTapePos i = (j : ℤ) - s := by
    intro i
    have h : ∃ j, j < 2 * s + 1 ∧ ((f j).2 i).2 = true := by
      obtain ⟨j, hj, hh⟩ := hex i; exact ⟨j, hj, hh⟩
    refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, ?_⟩
    simp only [mkCfg, dif_pos h]
  refine ⟨⟨fun i => ?_, fun i z hz => ?_⟩, fun j hj => ?_⟩
  · obtain ⟨j, hj, -, e⟩ := hpos i
    rw [e, abs_le]; constructor <;> omega
  · simp only [mkCfg]
    exact if_neg (not_le.mpr hz)
  · have h0 : (f 0).1.isSome := (hslot 0 (by omega)).mpr rfl
    obtain ⟨hd, hhd⟩ := Option.isSome_iff_exists.mp h0
    simp only [cellOf]
    refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_)
    · by_cases hj0 : j = 0
      · subst hj0
        simp [mkCfg, hhd]
      · rw [if_neg hj0]
        have := (hslot j hj).not.mpr hj0
        simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at this
        exact this.symm
    · simp only [mkCfg]
      rw [if_pos (by rw [abs_le]; constructor <;> omega)]
      have e : ((j : ℤ) - s + s).toNat = j := by omega
      rw [e]
    · obtain ⟨j₀, hj₀, hh₀, e⟩ := hpos i
      simp only [e]
      by_cases hjj : j = j₀
      · subst hjj; simp [hh₀]
      · have : ((f j).2 i).2 = false := by
          by_contra hne
          exact hjj (huniq i j hj j₀ hj₀ (by simpa using hne) hh₀)
        rw [this]
        simp only [decide_eq_false_iff_not]
        omega

/-- **The validity test** on a word `w`, for inputs of length `n` and window `s`: the
length is right, the chunk region passes the validity scan, the position field holds a value
at most `n + 1`, and the last letter is `1`. -/
def ValidChk (n s : ℕ) (w : List Bool) : Prop :=
  w.length = W N * (2 * s + 1) + wP n + 1 ∧ VAcc N (vScan N (w.take (W N * (2 * s + 1)))) ∧
    bitsVal ((w.drop (W N * (2 * s + 1))).take (wP n)) ≤ n + 1 ∧
    w.getD (W N * (2 * s + 1) + wP n) false = true

/-- The chunk region of a code word. -/
lemma cfgWord_take (s : ℕ) {x : List Bool} (C : Cfg N.k Bool N.State x) :
    (cfgWord s C).take (W N * (2 * s + 1)) = chunksWord N (cellOf s C) (2 * s + 1) := by
  simp only [cfgWord, List.append_assoc]
  rw [List.take_left' (by simp [length_chunksWord])]

/-- The position field of a code word. -/
lemma cfgWord_pos (s : ℕ) {x : List Bool} (C : Cfg N.k Bool N.State x) :
    ((cfgWord s C).drop (W N * (2 * s + 1))).take (wP x.length) =
      padBits (wP x.length) C.inputPos.val := by
  have := C.inputPos.isLt
  simp only [cfgWord, List.append_assoc]
  rw [List.drop_left' (by simp [length_chunksWord]),
    List.take_left' (length_padBits (length_bits_pos_le _ _ (by omega)))]

/-- The last letter of a code word. -/
lemma cfgWord_last (s : ℕ) {x : List Bool} (C : Cfg N.k Bool N.State x) :
    (cfgWord s C).getD (W N * (2 * s + 1) + wP x.length) false = true := by
  have := C.inputPos.isLt
  have hl : (chunksWord N (cellOf s C) (2 * s + 1) ++ padBits (wP x.length) C.inputPos.val).length
      = W N * (2 * s + 1) + wP x.length := by
    simp [length_chunksWord, length_padBits (length_bits_pos_le _ _ (by omega :
      C.inputPos.val ≤ x.length + 1))]
  simp only [cfgWord]
  rw [← hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

/-- The validity scan of a code word, by the closed form. -/
lemma vScan_cfgWord_eq (s : ℕ) {x : List Bool} (C : Cfg N.k Bool N.State x) :
    vScan N ((cfgWord s C).take (W N * (2 * s + 1))) =
      ((List.range (2 * s + 1)).map (cellOf s C)).foldl (vStep N) (vInit N) := by
  rw [vScan_eq N _ (2 * s + 1) (by simp [length_cfgWord]; omega)]
  have : (List.range (2 * s + 1)).map (fun j => decChunk N
      (((cfgWord s C).take (W N * (2 * s + 1))).drop (W N * j) |>.take (W N))) =
      ((List.range (2 * s + 1)).map (cellOf s C)).map some := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    rw [cfgWord_take]
    have := block_chunksWord N (cellOf s C) (2 * s + 1) j (List.mem_range.mp hj)
    simp only [block] at this
    simp [this]
  rw [this, foldl_vStepO_some]

/-- **What the scan reports on a code word**: the header of the configuration, a valid
verdict with every tape's head seen, the symbols under the heads, and the initial-shape
verdict of its cells.

**Proof sketch.** The closed form of the scan (`foldl_vStep`) on the cells of a
window-bounded configuration: the header is in cell `0` only, the head of tape `i` is
flagged exactly in cell `pos i + s`, which is therefore the last flagged cell. -/
theorem vScan_cfgWord (s : ℕ) {x : List Bool} (C : Cfg N.k Bool N.State x) (hC : Cfg.InWindow s C) :
    let st := vScan N ((cfgWord s C).take (W N * (2 * s + 1)))
    st.2.1 = some (C.state, sumIdx (outSummary C.output)) ∧ VAcc N st ∧
      (∀ i, st.2.2.2.1 i = C.workTapes i (C.workTapePos i)) ∧
      st.2.2.2.2.2 = decide (∀ j < 2 * s + 1, BlankTogether N (cellOf s C j)) := by
  intro st
  have hst : st = ((List.range (2 * s + 1)).map (cellOf s C)).foldl (vStep N) (vInit N) :=
    vScan_cfgWord_eq s C
  obtain ⟨-, h2, h3, -, h5, h6, h7⟩ := foldl_vStep N (cellOf s C) (2 * s + 1)
  rw [← hst] at h2 h3 h5 h6 h7
  have head : ∀ i (j : ℕ), ((cellOf s C j).2 i).2 = true ↔ (j : ℤ) - s = C.workTapePos i := by
    intro i j; simp [cellOf, eq_comm]
  have j0 : ∀ i, ((C.workTapePos i + s).toNat < 2 * s + 1) ∧
      (((C.workTapePos i + s).toNat : ℕ) : ℤ) - s = C.workTapePos i := by
    intro i
    have := hC.1 i
    rw [abs_le] at this
    constructor <;> omega
  refine ⟨by rw [h2]; simp [cellOf], ⟨?_, fun i => ?_⟩, fun i => ?_, h7⟩
  · rw [h6, decide_eq_true_eq]
    refine ⟨fun j hj => by simp [cellOf], fun i j₁ _ j₂ _ a b => ?_⟩
    rw [head] at a b
    omega
  · rw [h3, decide_eq_true_eq]
    exact ⟨_, (j0 i).1, (head i _).mpr (j0 i).2⟩
  · rw [h5 i _ (j0 i).1 ((head i _).mpr (j0 i).2) (fun j' h1 _ => by
      cases hh : ((cellOf s C j').2 i).2
      · rfl
      · rw [head] at hh; have := (j0 i).2; omega)]
    simp only [cellOf]
    rw [(j0 i).2]

/-- An undecodable block anywhere makes the scan reject.

**Proof sketch.** Induction on the number of blocks: a rejection is kept by every later
block (`vStepO_ok_false`). -/
lemma foldl_vStepO_none (d : ℕ → Option (CellV N)) (m : ℕ) (h : ∃ j < m, d j = none) :
    (((List.range m).map d).foldl (vStepO N) (vInit N)).2.2.2.2.1 = false := by
  induction m with
  | zero => obtain ⟨j, hj, -⟩ := h; omega
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    by_cases hm : d m = none
    · rw [hm]; rfl
    · obtain ⟨j, hj, hd⟩ := h
      have hj' : j < m := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact h
        · exact absurd hd hm
      exact vStepO_ok_false N _ _ (ih ⟨j, hj', hd⟩)

/-- **The validity test recognizes exactly the code words**: a word passes `ValidChk` for
the input length of `x` and window `s` iff it is the code word of some window-bounded
configuration of `N` on `x`.

**Proof sketch.** (⇐) The length, position field and last letter are read off the layout
(`length_cfgWord`, `cfgWord_pos`, `cfgWord_last`), and the scan accepts
(`vScan_cfgWord`). (⇒) The scan runs block by block (`vScan_eq`); an undecodable block
would reject (`foldl_vStepO_none`), so every block is the chunk of a cell value, and the
closed form (`foldl_vStep`) says the header is in the first cell only and every tape has
exactly one head flag. Reading the cells back (`cellOf_mkCfg`), with the position field's
value as input position, gives a window-bounded configuration whose chunks are the blocks;
the position field is the padding of its value (`eq_padBits`) and the last letter is `1`,
so its code word is the given word. -/
theorem validChk_iff (x : List Bool) (s : ℕ) (w : List Bool) :
    ValidChk (N := N) x.length s w ↔
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgWord s C = w := by
  constructor
  · rintro ⟨hlen, hacc, hpos, hlast⟩
    set m := 2 * s + 1 with hm
    set A := w.take (W N * m) with hAdef
    have hA : A.length = W N * m := by simp only [hAdef, List.length_take]; omega
    have hv := vScan_eq N A m hA
    have hdec : ∀ j < m, ∃ cv, decChunk N (block N A j) = some cv := by
      intro j hj
      by_contra hno
      push_neg at hno
      have hnone : decChunk N (block N A j) = none := by
        cases h : decChunk N (block N A j) with
        | none => rfl
        | some cv => exact absurd h (hno cv)
      have := foldl_vStepO_none (N := N) (fun j => decChunk N (block N A j)) m ⟨j, hj, hnone⟩
      simp only [block] at this
      rw [← hv] at this
      rw [hacc.1] at this
      exact Bool.noConfusion this
    set f : ℕ → CellV N := fun j => (decChunk N (block N A j)).getD (none, fun _ => (none, false))
      with hfdef
    have hf : ∀ j < m, decChunk N (block N A j) = some (f j) := by
      intro j hj
      obtain ⟨cv, hcv⟩ := hdec j hj
      simp [hfdef, hcv]
    have hmap : (List.range m).map (fun j => decChunk N ((A.drop (W N * j)).take (W N))) =
        ((List.range m).map f).map some := by
      rw [List.map_map]
      apply List.map_congr_left
      intro j hj
      exact hf j (List.mem_range.mp hj)
    rw [hmap, foldl_vStepO_some] at hv
    obtain ⟨-, -, h3, -, -, h6, -⟩ := foldl_vStep N f m
    rw [← hv] at h3 h6
    have hok := hacc.1
    rw [h6, decide_eq_true_eq] at hok
    have hseen : ∀ i, ∃ j < m, ((f j).2 i).2 = true := by
      intro i
      have := hacc.2 i
      rw [h3, decide_eq_true_eq] at this
      exact this
    set P := (w.drop (W N * m)).take (wP x.length) with hP
    have hPlen : P.length = wP x.length := by
      simp only [hP, List.length_take, List.length_drop]; omega
    let C : Cfg N.k Bool N.State x := mkCfg x s f ⟨bitsVal P, by omega⟩
    obtain ⟨hwin, hcells⟩ := cellOf_mkCfg x s f ⟨bitsVal P, by omega⟩ hok.1 hok.2 hseen
    refine ⟨C, hwin, ?_⟩
    have hch : chunksWord N (cellOf s C) m = A := by
      calc chunksWord N (cellOf s C) m = (List.ofFn fun j : Fin m => block N A j).flatten := by
            unfold chunksWord
            congr 1
            apply List.ofFn_inj.mpr
            funext j
            rw [hcells j j.isLt]
            exact encChunk_of_decChunk N (hf j j.isLt)
        _ = A := (eq_flatten_blocks A (W N) m hA).symm
    have hpad : padBits (wP x.length) C.inputPos.val = P := by
      show padBits (wP x.length) (bitsVal P) = P
      rw [← hPlen]; exact (eq_padBits P).symm
    have htail : w.drop (W N * m + wP x.length) = [true] := by
      have hl : (w.drop (W N * m + wP x.length)).length = 1 := by simp; omega
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hl
      rw [hb]
      have h0 := congrArg (fun l : List Bool => l[0]?) hb
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at h0
      rw [List.getD_eq_getElem?_getD, h0] at hlast
      simp only [Option.getD_some] at hlast
      rw [hlast]
    show chunksWord N (cellOf s C) (2 * s + 1) ++ padBits (wP x.length) C.inputPos.val ++ [true]
      = w
    rw [← hm, hch, hpad, ← htail, hP, List.append_assoc, ← List.drop_drop,
      List.take_append_drop, hAdef, List.take_append_drop]
  · rintro ⟨C, hC, rfl⟩
    refine ⟨length_cfgWord s C, (vScan_cfgWord s C hC).2.1, ?_, cfgWord_last s C⟩
    rw [cfgWord_pos, bitsVal_padBits]
    have := C.inputPos.isLt
    omega

end Complexity.Codec
