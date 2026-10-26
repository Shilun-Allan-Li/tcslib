/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TuringMachine.Build.InputLength
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.SpaceComplexity.Machines.Bin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space-constructible functions

[AB09, §4.1, p. 79]: `S : ℕ → ℕ` is space-constructible when some machine
computes `S(|x|)` from `x` within `O(S(|x|))` space, and the book's standing
convention is `S(n) > log n`. The definition mirrors
`Complexity.TimeConstructible` — output in binary (`Nat.bits`), constant slack
`c · S n`, which implements the book's own asymptotic space convention
([AB09, p. 79]: "computes `S(|x|)` in `O(S(|x|))` space"); whether an
exact-space variant is also satisfiable is a separate question this campaign
does not pose (the chapter-1 exact-**time** refutation does not transfer: a
space deadline forces no premature halt — round-1 audit, finding 3) — and
carries the book's
convention as the conjunct `∀ n, logSpace n ≤ S n`, so that downstream
statements (the space hierarchy, Savitch) can draw on it without restating it;
results needing only weaker hypotheses must say so (seeded to the P4.1 audit).

## Main definitions

* `Complexity.SpaceConstructible` — the binary-output, constant-slack,
  above-log form. [AB09, §4.1, p. 79]

## Main results (proved)

* `Complexity.spaceConstructible_iff` — the definition as an equivalence.
* `Complexity.spaceConstructible_logSpace` — `log` is space-constructible.
* `Complexity.spaceConstructible_linear` — `n + 1` is space-constructible.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, p. 79.)
-/

namespace Complexity

open Turing

/-- A function `S` is **space-constructible** when it dominates the logarithm
(`Complexity.logSpace`, the book's standing `S(n) > log n` convention carried as
data) and some machine computes the binary representation of `S (|x|)` from `x`
within `c · S (|x|)` visited work-tape cells. Mirrors
`Complexity.TimeConstructible` (binary output via `Nat.bits`, constant slack).
[AB09, §4.1, p. 79] -/
def SpaceConstructible (S : ℕ → ℕ) : Prop :=
  (∀ n, logSpace n ≤ S n) ∧
  ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool,
    M.ComputesInSpace (fun x => (S x.length).bits) fun n => c * S n

/-- **Space constructibility, unfolded**: `S` is space constructible exactly when
`logSpace n ≤ S n` for every `n` and, for some constant `c > 0`, some machine computes
`x ↦ (S |x|).bits` in space `c · S` (`Turing.FinTM.ComputesInSpace`). -/
theorem spaceConstructible_iff (S : ℕ → ℕ) :
    SpaceConstructible S ↔
      (∀ n, logSpace n ≤ S n) ∧ ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool,
        M.ComputesInSpace (fun x => (S x.length).bits) fun n => c * S n :=
  Iff.rfl

/-- Positive binary words have exactly the normalized logarithmic width. -/
private lemma b3a_bits_length {n : ℕ} (hn : n ≠ 0) :
    n.bits.length = logSpace n := by
  have lower := Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn)
  have upper := LogProg.length_bits_le_log n
  rw [← Nat.size_eq_bits_len] at lower
  unfold logSpace
  omega

/-- The counter word with its first cell overwritten by `true`. -/
private def b3a_word (n : ℕ) : List Bool := true :: n.bits.tail

/-- The overwrite handles zero while preserving every positive counter width. -/
private lemma b3a_word_length (n : ℕ) : (b3a_word n).length = logSpace n := by
  by_cases hn : n = 0
  · subst n
    simp [b3a_word, logSpace, Nat.bits]
  · simp only [b3a_word, List.length_cons, List.length_tail, b3a_bits_length hn]
    unfold logSpace
    omega

/-- Restricting a buffer to its occupied nonnegative interval does not change it. -/
private lemma b3a_buffer_restrict (w : List Bool) (z : ℤ) :
    (if 0 ≤ z ∧ z < (w.length : ℤ) then FinTM.bufferTape w z else none) =
      FinTM.bufferTape w z := by
  by_cases hzero : 0 ≤ z
  · by_cases hlast : z < (w.length : ℤ)
    · simp [hzero, hlast]
    · have out : w.length ≤ z.toNat := by omega
      simp [hzero, hlast, FinTM.bufferTape]
  · simp [hzero, FinTM.bufferTape]

/-- Setting the first buffered cell yields `true :: tail`, including an empty buffer. -/
private lemma b3a_buffer_overwrite (w : List Bool) (z : ℤ) :
    (if z = 0 then some true else FinTM.bufferTape w z) =
      FinTM.bufferTape (true :: w.tail) z := by
  by_cases hz : z = 0
  · subst z
    simp [FinTM.bufferTape]
  · by_cases hp : 0 ≤ z
    · have ht : z.toNat ≠ 0 := by omega
      simp only [if_neg hz, FinTM.bufferTape, if_pos hp, List.getElem?_cons,
        if_neg ht, List.getElem?_tail]
      congr 1
      omega
    · simp [hz, FinTM.bufferTape, hp]

/-- A live phase seam: its word is on tape zero and all heads are at the origin. -/
private def b3a_cfg {k : ℕ} [NeZero k] {S : Type} (s : S)
    (x w : List Bool) : Cfg k Bool S x :=
  { Cfg.init s x with
    workTapes := fun j => if j = 0 then FinTM.bufferTape w else fun _ => none }

/-- Map only the control field of a canonical phase seam. -/
private lemma b3a_cfg_map {k : ℕ} [NeZero k] {S T : Type} (f : S → T)
    (s : S) (x w : List Bool) :
    (b3a_cfg (k := k) s x w).mapState f = b3a_cfg (f s) x w := rfl

/-- Relocate a single-buffer seam along a selection preserving tape zero.
**Proof sketch.** Selected tapes use the public configuration projections;
other tapes use the frame theorem at time zero. All unused cells and heads are blank. -/
private lemma b3a_embed_cfg {m k : ℕ} [NeZero m] [NeZero k] {S : Type}
    (R : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k) (hzero : ι 0 = 0)
    (s : S) (x w : List Bool) :
    embedEmitCfg ι (fun _ _ => none) (fun _ => 0) [] (b3a_cfg s x w) =
      b3a_cfg (k := k) s x w := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    by_cases chosen : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := chosen
      rw [embedEmitCfg_selected_tape]
      have hz : ι i = 0 ↔ i = 0 := by rw [← hzero, ι.injective.eq_iff]
      simp only [b3a_cfg, hz]
    · have frame := (embedEmitTM_frame ι R (fun _ _ => none) (fun _ => 0)
        [] (b3a_cfg s x w) 0).1 j chosen
      have hj : j ≠ 0 := fun eq => chosen ⟨0, hzero.trans eq.symm⟩
      simpa [b3a_cfg, hj] using frame.1
  · funext j
    by_cases chosen : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := chosen
      rw [embedEmitCfg_selected_pos]
      rfl
    · exact (embedEmitTM_frame ι R (fun _ _ => none) (fun _ => 0)
        [] (b3a_cfg s x w) 0).1 j chosen |>.2
  · rfl

/-- A coarse constant-factor space bound for tape relocation.
**Proof sketch.** Every selected tape is bounded by the source's total space;
each unused tape contributes one cell. Sum this common bound over the host bank. -/
private lemma b3a_embed_space {m k : ℕ} {S : Type} {x : List Bool}
    (R : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k)
    (d : Cfg m Bool S x) (t : ℕ) :
    (embedEmitTM ι R).spaceUsed
        (embedEmitCfg ι (fun _ _ => none) (fun _ => 0) [] d) t ≤
      k * (R.spaceUsed d t + 1) := by
  unfold MultiTapeTM.spaceUsed
  calc
    _ ≤ ∑ _j : Fin k, (R.spaceUsed d t + 1) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases chosen : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := chosen
        rw [(embedEmitTM_visitedByTapeHead ι R (fun _ _ => none) (fun _ => 0) [] d t i).2]
        exact (R.spaceUsedByTape_le_spaceUsed d t i).trans (Nat.le_succ _)
      · rw [(embedEmitTM_visitedByTapeHead_frame ι R (fun _ _ => none)
          (fun _ => 0) [] d t j chosen).2]
        omega
    _ = _ := by simp [MultiTapeTM.spaceUsed]

/-- The additive space ledger for an arbitrary live-exit seam.
**Proof sketch.** Apply the public visited-set inclusion on each tape, bound
the cardinality of its union by the sum, and sum over the bank. -/
private lemma b3a_seam_space {k : ℕ} {S T : Type} [DecidableEq S] {x : List Bool}
    (R : MultiTapeTM k Bool S) (exit : S) (Q : MultiTapeTM k Bool T) (entry : T)
    {d e : Cfg k Bool S x} {a b : ℕ} (run : R.runFrom d a = e)
    (live : e.state = some exit) (cut : ∀ u < a, (R.runFrom d u).state ≠ some exit) :
    (seamCompTM R exit Q entry).spaceUsed (d.mapState Sum.inl) (a + 1 + b) ≤
      R.spaceUsed d a + Q.spaceUsed (e.mapState fun _ => entry) b := by
  calc
    _ ≤ ∑ i : Fin k, (R.spaceUsedByTape d a i +
        Q.spaceUsedByTape (e.mapState fun _ => entry) b i) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ (R.visitedByTapeHead d a i ∪
            Q.visitedByTapeHead (e.mapState fun _ => entry) b i).card := by
          apply Finset.card_le_card
          exact seamCompTM_visitedByTapeHead_ofCfg R exit Q entry run live cut i
        _ ≤ _ := Finset.card_union_le _ _
    _ = _ := Finset.sum_add_distrib

/-- The public native counter, specialized to blank origin tapes with a cardinality ledger.
**Proof sketch.** Instantiate R8.5c at its entry, identify the globally blank frame
with the buffer layout, and enclose each head's visited set in the promised interval.
The first-exit clause is retained for the subsequent dispatch. -/
private theorem b3a_counter :
    ∃ (K : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (R : MultiTapeTM (K + 1) Bool S) (entry exit : S) (B : ℕ),
      ∀ x : List Bool, ∃ t,
        R.runFrom (b3a_cfg entry x []) t = b3a_cfg exit x x.length.bits ∧
        (∀ u < t, (R.runFrom (b3a_cfg entry x []) u).state ≠ some exit) ∧
        R.spaceUsed (b3a_cfg entry x []) t ≤ B * (x.length.bits.length + 1) := by
  obtain ⟨K, S, fs, ds, R, entry, exit, C, contract⟩ := exists_inputLengthTM
  letI := fs
  letI := ds
  refine ⟨K, S, fs, ds, R, entry, exit, (K + 1) * (2 * C + 1), ?_⟩
  intro x
  obtain ⟨t, _, cut, heads, finished⟩ := contract (b3a_cfg entry x []) rfl rfl
    (by intros; simp [b3a_cfg]) (by intros; simp [b3a_cfg])
  refine ⟨t, ?_, cut, ?_⟩
  · rw [finished]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      by_cases hj : j = 0
      · simp [b3a_cfg, hj, b3a_buffer_restrict]
      · simp [b3a_cfg, hj]
    · rfl
    · rfl
  · have perTape (j : Fin (K + 1)) : R.spaceUsedByTape (b3a_cfg entry x []) t j ≤
        2 * (C * (x.length.bits.length + 1)) + 1 := by
      calc
        _ ≤ (Finset.Icc (-((C * (x.length.bits.length + 1) : ℕ) : ℤ))
            ((C * (x.length.bits.length + 1) : ℕ) : ℤ)).card := by
          apply Finset.card_le_card
          intro z hz
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
          have bound := heads u (Nat.le_of_lt_succ (Finset.mem_range.mp hu)) j
          simpa [b3a_cfg, Finset.mem_Icc, abs_le] using bound
        _ = _ := by rw [Int.card_Icc]; omega
    calc
      _ ≤ ∑ _j : Fin (K + 1), (2 * (C * (x.length.bits.length + 1)) + 1) :=
        Finset.sum_le_sum fun j _ => perTape j
      _ = (K + 1) * (2 * (C * (x.length.bits.length + 1)) + 1) := by simp
      _ ≤ (K + 1) * ((2 * C + 1) * (x.length.bits.length + 1)) := by
        apply Nat.mul_le_mul_left
        ring_nf; omega
      _ = _ := by ring

/-- The public constant writer overwrites cell zero and returns to its origin.
**Proof sketch.** Use R8.4 with `[true]`. Its four-step trace supplies the exact
exit cut and two-cell head interval; the buffer update is the tail identity above. -/
private theorem b3a_overwrite (x w : List Bool) :
    (writeConstTM 1 0 [true]).runFrom (b3a_cfg (.wr 0) x w) 4 =
        b3a_cfg .done x (true :: w.tail) ∧
      (∀ u < 4, ((writeConstTM 1 0 [true]).runFrom
        (b3a_cfg (.wr 0) x w) u).state ≠ some .done) ∧
      (writeConstTM 1 0 [true]).spaceUsed (b3a_cfg (.wr 0) x w) 4 ≤ 2 := by
  obtain ⟨run, cut, heads⟩ := writeConstTM_run_ofCfg (0 : Fin 1) [true]
    (b3a_cfg (.wr 0) x w) rfl
  norm_num only [List.length_singleton] at run
  refine ⟨?_, cut, ?_⟩
  · rw [run]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      have hj : j = 0 := Subsingleton.elim _ _
      simp only [b3a_cfg, Cfg.init, hj, if_pos, List.length_singleton,
        zero_add, sub_zero]
      simp only [true_and, show (0 ≤ z ∧ z < 1) ↔ z = 0 by omega]
      by_cases hz : z = 0
      · simp [hz, FinTM.bufferTape]
      · simpa [hz] using b3a_buffer_overwrite w z
    · rfl
    · rfl
  · change ∑ j : Fin 1, _ ≤ 2
    rw [Fintype.sum_subsingleton _ (0 : Fin 1)]
    calc
      _ ≤ (Finset.Icc (0 : ℤ) 1).card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        simpa [b3a_cfg] using heads 0 u (Nat.le_of_lt_succ (Finset.mem_range.mp hu))
      _ = 2 := by decide

/-- The emitting phase shares tape zero and places its bank after the native counter bank. -/
private def b3a_virtualSelect (K m : ℕ) : Fin (1 + m) ↪ Fin (K + 1 + m) where
  toFun i := ⟨if i.val = 0 then 0 else K + i.val, by split_ifs <;> omega⟩
  inj' := by
    intro i j eq
    apply Fin.ext
    have vals := congrArg Fin.val eq
    dsimp at vals
    split_ifs at vals <;> omega

/-- The initial virtual-input layout is the single-buffer phase seam.
**Proof sketch.** Split the host tapes into its buffer and source bank. The source
starts at input position one, with blank work tapes and all heads at zero. -/
private lemma b3a_virtual_cfg (L : FinTM Bool) (x y : List Bool) :
    vhostCfg (L.tm.initCfg y) true (1 : Fin (x.length + 2)) [] =
      b3a_cfg (L.tm.q₀, true) x y := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j z
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have zero : Fin.castAdd L.k (0 : Fin 1) = 0 := rfl
      change FinTM.bufferTape y z =
        (if Fin.castAdd L.k (0 : Fin 1) = 0 then FinTM.bufferTape y else fun _ => none) z
      rw [if_pos zero]
    · have nonzero : Fin.natAdd 1 i ≠ (0 : Fin (1 + L.k)) := by
        intro eq
        have vals := congrArg Fin.val eq
        simp only [Fin.coe_natAdd, Fin.val_zero] at vals
        omega
      simp only [vhostCfg, Fin.addCases_right, b3a_cfg, if_neg nonzero,
        MultiTapeTM.initCfg, Cfg.init]
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [vhostCfg, b3a_cfg, MultiTapeTM.initCfg, Cfg.init]
    · simp [vhostCfg, b3a_cfg, MultiTapeTM.initCfg, Cfg.init]
  · rfl

/-- Assemble the three public phases with an explicit boundary-inclusive space allowance.
**Proof sketch.** Count on a native bank, overwrite its first cell, then host the
length counter on that word. Both seams dispatch at their first exits. The public
relocation and seam ledgers bound total space by a fixed multiple of the normalized
logarithm plus one; the final virtual-input halt emits the full binary answer. -/
private theorem b3a_log_machine :
    ∃ (A : ℕ), 0 < A ∧ ∃ M : FinTM Bool,
      M.ComputesInSpace (fun x => (logSpace x.length).bits)
        (fun n => A * (logSpace n + 1)) := by
  obtain ⟨K, S, fs, ds, R, entry, exit, B, counter⟩ := b3a_counter
  letI := fs
  letI := ds
  obtain ⟨L, b, computes, space⟩ := FinTM.computesFunInTime_lengthBits_spaceUsed
  let k := K + 1 + L.k
  let ic : Fin (K + 1) ↪ Fin k := Fin.castAddEmb L.k
  let iw : Fin 1 ↪ Fin k := Fin.castLEEmb (by dsimp [k]; omega)
  let iv := b3a_virtualSelect K L.k
  have ic0 : ic 0 = 0 := rfl
  have iw0 : iw 0 = 0 := rfl
  have iv0 : iv 0 = 0 := by apply Fin.ext; simp [iv, b3a_virtualSelect]
  let C := embedEmitTM ic R
  let W := embedEmitTM iw (writeConstTM 1 0 [true])
  let E := embedEmitTM iv (vhostEmitTM L.tm)
  let CW := seamCompTM C exit W (.wr 0)
  let H := seamCompTM CW (Sum.inr .done) E (L.tm.q₀, true)
  let M : FinTM Bool :=
    { k := k
      State := (S ⊕ WritePhase 1) ⊕ (L.State × Bool)
      tm := {H with q₀ := Sum.inl (Sum.inl entry)} }
  refine ⟨k * (B + b + 8) + 1, by omega, M, ?_⟩
  intro x
  let y := b3a_word x.length
  obtain ⟨t, counted, countCut, countSpace⟩ := counter x
  obtain ⟨written, writeCut, writeSpace⟩ := b3a_overwrite x x.length.bits
  -- Count and overwrite share the buffer; their first-exit cuts justify both dispatches.
  have countRun : C.runFrom (b3a_cfg entry x []) t =
      b3a_cfg exit x x.length.bits := by
    rw [← b3a_embed_cfg R ic ic0 entry x [], embedEmitTM_runFrom, counted,
      b3a_embed_cfg R ic ic0]
  have countFirst : ∀ u < t, (C.runFrom (b3a_cfg entry x []) u).state ≠ some exit := by
    intro u hu
    rw [← b3a_embed_cfg R ic ic0 entry x [], embedEmitTM_runFrom]
    exact countCut u hu
  have writeRun : W.runFrom (b3a_cfg (.wr 0) x x.length.bits) 4 =
      b3a_cfg .done x y := by
    rw [← b3a_embed_cfg (writeConstTM 1 0 [true]) iw iw0 (.wr 0) x x.length.bits,
      embedEmitTM_runFrom, written, b3a_embed_cfg (writeConstTM 1 0 [true]) iw iw0]
    rfl
  have writeFirst : ∀ u < 4,
      (W.runFrom (b3a_cfg (.wr 0) x x.length.bits) u).state ≠ some .done := by
    intro u hu
    rw [← b3a_embed_cfg (writeConstTM 1 0 [true]) iw iw0 (.wr 0) x x.length.bits,
      embedEmitTM_runFrom]
    exact writeCut u hu
  have cwRun : CW.runFrom (b3a_cfg (Sum.inl entry) x []) (t + 1 + 4) =
      b3a_cfg (Sum.inr .done) x y := by
    simpa only [b3a_cfg_map] using seamCompTM_run_ofCfg C exit W (.wr 0)
      countRun rfl countFirst (by simpa only [b3a_cfg_map] using writeRun)
  have cwFirst : ∀ u < t + 1 + 4,
      (CW.runFrom (b3a_cfg (Sum.inl entry) x []) u).state ≠ some (Sum.inr .done) := by
    simpa only [b3a_cfg_map] using seamCompTM_firstReturn_ofCfg C exit W (.wr 0) .done
      countRun rfl countFirst (by simpa only [b3a_cfg_map] using writeRun) rfl
      (by simpa only [b3a_cfg_map] using writeFirst)
  -- The last phase forwards the hosted counter's full output, including its halting step.
  let u := b * (y.length + 1)
  have tag : FinTM.VirtualTag (L.tm.initCfg y).inputPos true := by
    simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]
  obtain ⟨tagEnd, _, hosted⟩ := vhostEmitTM_runFrom L.tm (L.tm.initCfg y) true tag
    (1 : Fin (x.length + 2)) [] u
  have emitted : E.runFrom (b3a_cfg (L.tm.q₀, true) x y) u =
      embedEmitCfg iv (fun _ _ => none) (fun _ => 0) []
        (vhostCfg (L.tm.runFrom (L.tm.initCfg y) u) tagEnd (1 : Fin (x.length + 2)) []) := by
    rw [← b3a_embed_cfg (vhostEmitTM L.tm) iv iv0 (L.tm.q₀, true) x y,
      ← b3a_virtual_cfg, embedEmitTM_runFrom, hosted]
  have fullRun := seamCompTM_run_ofCfg CW (Sum.inr .done) E (L.tm.q₀, true)
    cwRun rfl cwFirst (by simpa only [b3a_cfg_map] using emitted)
  have start : M.tm.initCfg x = b3a_cfg (Sum.inl (Sum.inl entry)) x [] := by
    apply Cfg.ext <;> simp [M, MultiTapeTM.initCfg, b3a_cfg, Cfg.init]
  refine ⟨(t + 1 + 4) + 1 + u, ?_, ?_⟩
  · apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [start]
    change (H.runFrom _ _).state = none ∧ (H.runFrom _ _).output = _
    rw [show b3a_cfg (Sum.inl (Sum.inl entry)) x [] =
      (b3a_cfg (Sum.inl entry) x []).mapState Sum.inl from rfl, fullRun]
    obtain ⟨halted, output⟩ := (FinTM.computesInTime_iff L y _ u).mp (computes y)
    simp only [Cfg.mapState, embedEmitCfg, vhostCfg, List.nil_append,
      halted, output, Option.map_none, y, b3a_word_length, and_self]
  · rw [start]
    change H.spaceUsed _ _ ≤ _
    -- Add the three boundary-inclusive ledgers before absorbing the constant slack.
    have firstLedger := b3a_seam_space C exit W (.wr 0) (b := 4)
      countRun rfl countFirst
    have lastLedger := b3a_seam_space CW (Sum.inr .done) E (L.tm.q₀, true) (b := u)
      cwRun rfl cwFirst
    simp only [b3a_cfg_map] at firstLedger lastLedger
    have cSpace := b3a_embed_space R ic (b3a_cfg entry x []) t
    rw [b3a_embed_cfg R ic ic0] at cSpace
    have wSpace := b3a_embed_space (writeConstTM 1 0 [true]) iw
      (b3a_cfg (.wr 0) x x.length.bits) 4
    rw [b3a_embed_cfg (writeConstTM 1 0 [true]) iw iw0] at wSpace
    have eSpace := b3a_embed_space (vhostEmitTM L.tm) iv
      (vhostCfg (L.tm.initCfg y) true (1 : Fin (x.length + 2)) []) u
    rw [b3a_virtual_cfg, b3a_embed_cfg (vhostEmitTM L.tm) iv iv0] at eSpace
    have eSource := vhostEmitTM_spaceUsed_le L.tm (L.tm.initCfg y) true tag
      (1 : Fin (x.length + 2)) [] u
    rw [b3a_virtual_cfg] at eSource
    have sizeBound : Nat.size y.length ≤ y.length := by
      rw [← Nat.size_eq_bits_len]
      exact length_bits_le_self _
    have width := LogProg.length_bits_le_log x.length
    have yLength : y.length = logSpace x.length := b3a_word_length _
    have nativeBound : C.spaceUsed (b3a_cfg entry x []) t ≤
        k * (B * (logSpace x.length + 1) + 1) := by
      apply cSpace.trans
      apply Nat.mul_le_mul_left
      apply Nat.add_le_add_right
      exact countSpace.trans (Nat.mul_le_mul_left B (Nat.add_le_add_right width 1))
    have writerBound : W.spaceUsed (b3a_cfg (.wr 0) x x.length.bits) 4 ≤ k * 3 := by
      exact wSpace.trans (Nat.mul_le_mul_left _ (by omega))
    have emitterBound : E.spaceUsed (b3a_cfg (L.tm.q₀, true) x y) u ≤
        k * (b * (logSpace x.length + 1) + logSpace x.length + 3) := by
      apply eSpace.trans
      apply Nat.mul_le_mul_left
      have ls := space y u
      have bound := (Nat.mul_le_mul_left b (Nat.add_le_add_right sizeBound 1))
      rw [yLength] at bound eSource ls
      omega
    calc
      _ ≤ C.spaceUsed (b3a_cfg entry x []) t +
          W.spaceUsed (b3a_cfg (.wr 0) x x.length.bits) 4 +
          E.spaceUsed (b3a_cfg (L.tm.q₀, true) x y) u :=
        lastLedger.trans (Nat.add_le_add_right firstLedger _)
      _ ≤ k * (B * (logSpace x.length + 1) + 1) + k * 3 +
          k * (b * (logSpace x.length + 1) + logSpace x.length + 3) := by
        exact Nat.add_le_add (Nat.add_le_add nativeBound writerBound) emitterBound
      _ ≤ (k * (B + b + 8) + 1) * (logSpace x.length + 1) := by
        ring_nf; omega

/-- **The logarithm is space-constructible.** [AB09, p. 79: "all functions of
interest, including `log n`, …, are space-constructible"]

**Proof sketch.** Fill obligations: a machine that (i) counts the input length
in binary on a work tape by one left-to-right input scan with a binary
increment at each step (the `Turing.counterTM`/`incrementTM` idiom — P11 of
`machine-library-design.md` §4, space-annotated per §12 R3) — the counter word
has `|Nat.bits n| = logSpace n` cells **for `n > 0` only** (`Nat.bits 0 = []`
has length `0 ≠ logSpace 0 = 1`; round-1 audit, finding 1), so (ii) the empty
input is special-cased to emit `(logSpace 0).bits = [true]` directly, and
otherwise the machine computes the counter word's bit-length by a second count
and emits its bits. Space: the counters and markers fit in
`A·(logSpace n + 1) ≤ 2A·logSpace n` visited cells (boundary cells included
before absorbing, since `logSpace n ≥ 1`); the dominance conjunct is `le_refl`
at `S = logSpace`.

**Fill appendix.** The empty-input special case is realized uniformly: after
R8.5c counts the native input, the constant writer sets the first buffered cell
to `true`. The resulting word has length `logSpace n`, including at zero. A
Z1-hosted Catalog length counter emits its binary length and genuinely halts.
Both live exits are intercepted at their first visits. The space ledger includes
the native head intervals, the overwrite boundary, the virtual-input boundary
cells and the fresh bank, giving `A * (logSpace n + 1)` before absorption. -/
theorem spaceConstructible_logSpace : SpaceConstructible logSpace := by
  obtain ⟨A, hA, M, hM⟩ := b3a_log_machine
  refine ⟨fun _ => le_rfl, 2 * A, by omega, M, ?_⟩
  intro x
  obtain ⟨t, ht, hs⟩ := hM x
  refine ⟨t, ht, hs.trans ?_⟩
  have hlog : logSpace x.length + 1 ≤ 2 * logSpace x.length := by
    unfold logSpace
    omega
  calc
    A * (logSpace x.length + 1) ≤ A * (2 * logSpace x.length) :=
      Nat.mul_le_mul_left _ hlog
    _ = (2 * A) * logSpace x.length := by ring

/-- **Linear space is constructible**: `n ↦ n + 1` is space-constructible (the
`+ 1` prevents the inherited zero-bound collapse at `n = 0` — the P0
convention, `SpaceComplexity/ZeroSpace.lean` — and satisfies the dominance
conjunct; zero-space classes are nonempty, so this is about collapse, not
vacuity).

**Proof sketch.** The input-scan counter of
`Complexity.spaceConstructible_logSpace`, **initialized at `1`** so that after
`n` consumed symbols it holds `n + 1` (an uncorrected length counter holds `n`
and emits the wrong word — round-1 audit, finding 2); emit its bits. Space:
the counter's binary width plus fixed administrative cells fit in
`A·(n + 2) ≤ 2A·(n + 1)` visited cells; dominance is `logSpace n ≤ n + 1`
(`1 ≤ 1` at `n = 0`; a small arithmetic lemma otherwise).

**Fill appendix.** The counter initialized at `1` is realized by the Catalog
length counter on `true :: x`, using the proved prepend and buffered-composition
rows. Its linear running time bounds all visited work-tape cells, including
the counter width and boundary cells. -/
theorem spaceConstructible_linear : SpaceConstructible fun n => n + 1 := by
  refine ⟨fun n => Nat.succ_le_succ (Nat.log_le_self 2 n), ?_⟩
  obtain ⟨P, a, hp, _⟩ := FinTM.computesFunInTime_prepend_spaceUsed [true]
  obtain ⟨L, b, hl, _⟩ := FinTM.computesFunInTime_lengthBits_spaceUsed
  let M := FinTM.bufferedCompTM P L
  refine ⟨M.k * (a + 2 * b + 4) + 1, by omega, M, ?_⟩
  intro x
  let t := a * (x.length + 1) + (x.length + 1) + 2 + b * (x.length + 2)
  refine ⟨t, ?_, ?_⟩
  · simpa [M, t] using FinTM.bufferedCompTM_computesInTime P L (hp x) (hl ([true] ++ x))
  · have ht : t + 1 ≤ (a + 2 * b + 4) * (x.length + 1) := by
      dsimp [t]
      ring_nf; omega
    calc
      M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (t + 1) :=
        M.tm.spaceUsed_le_mul_succ _ _
      _ ≤ M.k * ((a + 2 * b + 4) * (x.length + 1)) := Nat.mul_le_mul_left _ ht
      _ ≤ (M.k * (a + 2 * b + 4) + 1) * (x.length + 1) := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.le_succ _)

end Complexity
