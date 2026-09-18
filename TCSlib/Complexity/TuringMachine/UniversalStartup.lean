/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Universal machine: startup infrastructure

Prefix-local startup layer of the universal machine: parsing the doubled-bit
code region of `pairEncode α x`, running the scheme's canonizer on the
extracted code, embedding the virtual input head into the paired input's
verbatim `x` region, and capturing the canonical table on a dedicated work
tape before control transfers to the table interpreter. This file was split
out mechanically from `Universal.lean` at the epoch-3→4 merge; its contents
are the epoch-3 fill, batches B (WIP) and B2 (completion), unchanged.

## Main definitions / Main results

* `Turing.universalCanonTM` — prefix extraction composed with the scheme's canonizer.
* `Turing.universalCaptureTM` — output capture onto a table tape, then transfer
  to a four-tape interpreter.
* `Turing.universalCanon_complete` — the canonical serialization is produced at
  a suffix-independent time.
* `Turing.universalCapture_start` — every completed source computation reaches
  the interpreter with the table captured.
* `Turing.universalInput_read` / `Turing.universalInput_move` — virtual
  input-head emulation over the verbatim `x` region.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9, pp. 20-21.)
-/

namespace Turing

/-! ### Private prefix-local startup infrastructure

Implementation notes (epoch 3B). The extraction machine stops immediately after
reading the aligned separator. Buffered composition then serves the canonizer's
input from the extracted word and keeps the physical suffix head stationary.

**Incomplete implementation (epoch 3B).** The startup, virtual-boundary lemmas,
and conditional block-simulation assembly below are proved. The live-source
serialized-table block obligation in `universal` remains admitted. The concrete
interpreter is a candidate, not a completed proof of the headline theorem.

**Completion (epoch 3B2).** The preceding paragraph records the delivered WIP.
The live serialized-table block is now proved below, including exact phase costs,
record selection, action application, and the original code-only block bound.
The controller and all startup and assembly constructions are unchanged.
-/

open FinTM

/-- Doubling the code and appending its delimiter has suffix-independent length. -/
lemma universal_pair_length (α x : List Bool) :
    (pairEncode α x).length = 2 * α.length + 2 + x.length := by
  induction α with
  | nil => simp [pairEncode]; omega
  | cons b α ih =>
    simp only [pairEncode, List.flatMap_cons, List.cons_append, List.nil_append,
      List.length_cons] at *
    omega

/-- Both cells of a doubled code bit are read before the separator. -/
private lemma universal_pair_get (α x : List Bool) (j : ℕ) (hj : j < α.length) :
    (pairEncode α x)[2 * j]? = some α[j] ∧
      (pairEncode α x)[2 * j + 1]? = some α[j] := by
  induction α generalizing j with
  | nil => simp at hj
  | cons b α ih =>
    cases j with
    | zero => simp [pairEncode]
    | succ j =>
      have h := ih j (by simpa using hj)
      simpa only [pairEncode, List.flatMap_cons, List.cons_append,
        List.nil_append, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
        List.getElem?_cons_succ, List.getElem_cons_succ] using h

/-- The delimiter begins immediately after the doubled code. -/
private lemma universal_pair_separator (α x : List Bool) :
    (pairEncode α x)[2 * α.length]? = some false ∧
      (pairEncode α x)[2 * α.length + 1]? = some true := by
  induction α with
  | nil => simp [pairEncode]
  | cons b α ih =>
    simpa only [pairEncode, List.flatMap_cons, List.cons_append,
      List.nil_append, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
      List.getElem?_cons_succ] using ih

/-- Two-state-register parser. The outer optional state of a configuration is
halting; `none` inside the finite control means that the first half of a pair is
next. On a valid pair, the second half emits its undoubled bit; on the separator
it moves to the suffix and halts without emitting. -/
private def universalPrefixTM : FinTM Bool where
  k := 0
  State := Option Bool
  tm :=
    { q₀ := none
      tr := fun q inp _ => match q with
        | none => ⟨.pos, fun i => i.elim0, none, inp.map some⟩
        | some b =>
          if inp = some b then
            ⟨.pos, fun i => i.elim0, some b, some none⟩
          else
            ⟨.pos, fun i => i.elim0, none, none⟩ }

/-- The prefix parser carries no work tapes. -/
private def universalPrefixCfg (α x : List Bool) (q : Option (Option Bool))
    (p : Fin ((pairEncode α x).length + 2)) (out : List Bool) :
    Cfg 0 Bool (Option Bool) (pairEncode α x) :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- A single parser transition, with its input read supplied explicitly. -/
private lemma universalPrefix_step (α x : List Bool) (q : Option Bool)
    (p : Fin ((pairEncode α x).length + 2)) (out : List Bool) (b : Option Bool)
    (hb : (universalPrefixCfg α x (some q) p out).inputSymbol = b) :
    universalPrefixTM.tm.step (universalPrefixCfg α x (some q) p out) =
      let a := universalPrefixTM.tm.tr q b (fun i => i.elim0)
      universalPrefixCfg α x a.state (moveInputPos p a.inputTape)
        (out ++ a.output.toList) := by
  change (universalPrefixTM.tm.tr q
    (universalPrefixCfg α x (some q) p out).inputSymbol
    (universalPrefixCfg α x (some q) p out).workTapeSymbols).apply _ = _
  rw [hb]
  exact Cfg.ext_zero_tapes rfl rfl rfl

/-- After `2j` steps exactly `j` code bits have been consumed and emitted.

**Proof sketch.** The aligned cells at offsets `2j` and `2j+1` contain the same
code bit. The first transition remembers it, and the second emits it. Neither
transition can reach the suffix, and the work-tape fields are vacuous. -/
private lemma universalPrefix_bits (α x : List Bool) : ∀ j, (hj : j ≤ α.length) →
    universalPrefixTM.tm.runFrom (universalPrefixTM.tm.initCfg (pairEncode α x))
      (2 * j) =
    universalPrefixCfg α x (some none)
      ⟨2 * j + 1, by rw [universal_pair_length]; omega⟩ (α.take j) := by
  intro j
  induction j with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> rfl
  | succ j ih =>
    intro hj
    have hl := universal_pair_length α x
    have hg := universal_pair_get α x j (by omega)
    conv_lhs => rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      ih (by omega)]
    rw [universalPrefix_step _ _ _ _ _ (some α[j]) (by
      rw [inputSymbol_at _ (2 * j) (by omega) (by rfl)]; exact hg.1)]
    simp only [universalPrefixTM, Option.map_some, Option.toList_none, List.append_nil]
    rw [moveInputPos_pos_of_ne_right _ (by simp only [Fin.val_mk]; omega)]
    rw [universalPrefix_step _ _ _ _ _ (some α[j]) (by
      rw [inputSymbol_at _ (2 * j + 1) (by omega) (by rfl)]; exact hg.2)]
    simp only [universalPrefixTM, ↓reduceIte, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by simp only [Fin.val_mk]; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · apply Fin.ext; simp only [universalPrefixCfg, Fin.val_mk]; omega
    · rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      rfl

/-- Prefix-only extraction takes exactly `2|α|+2` steps, emits `α`, and parks
at `2|α|+3`. This includes empty code and empty suffix; no suffix cell is read.

**Proof sketch.** Apply the doubled-prefix induction to the whole code, then
execute the two separator transitions. The last transition moves onto, but does
not read, the suffix's first cell (the right blank when the suffix is empty). -/
private lemma universalPrefix_start (α x : List Bool) :
    universalPrefixTM.tm.runFrom (universalPrefixTM.tm.initCfg (pairEncode α x))
      (2 * α.length + 2) =
    universalPrefixCfg α x none
      ⟨2 * α.length + 3, by rw [universal_pair_length]; omega⟩ α := by
  have hl := universal_pair_length α x
  have hg := universal_pair_separator α x
  conv_lhs => rw [show 2 * α.length + 2 = 2 * α.length + 1 + 1 by omega]
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    universalPrefix_bits α x α.length (le_refl _), List.take_length]
  rw [universalPrefix_step _ _ _ _ _ (some false) (by
    rw [inputSymbol_at _ (2 * α.length) (by omega) (by rfl)]; exact hg.1)]
  simp only [universalPrefixTM, Option.map_some, Option.toList_none, List.append_nil]
  rw [moveInputPos_pos_of_ne_right _ (by simp only [Fin.val_mk]; omega)]
  rw [universalPrefix_step _ _ _ _ _ (some true) (by
    rw [inputSymbol_at _ (2 * α.length + 1) (by omega) (by rfl)]; exact hg.2)]
  simp only [universalPrefixTM, Bool.true_eq_false, Option.some.injEq, ↓reduceIte,
    Option.toList_none, List.append_nil]
  apply Cfg.ext_zero_tapes
  · rfl
  · rw [moveInputPos_pos_of_ne_right _ (by simp only [Fin.val_mk]; omega)]
  · rfl



/-- One transition remains after the doubled code and the delimiter's first bit. -/
private lemma universalPrefix_penultimate (α x : List Bool) :
    universalPrefixTM.tm.runFrom (universalPrefixTM.tm.initCfg (pairEncode α x))
      (2 * α.length + 1) =
    universalPrefixCfg α x (some (some false))
      ⟨2 * α.length + 2, by rw [universal_pair_length]; omega⟩ α := by
  have hl := universal_pair_length α x
  rw [MultiTapeTM.runFrom_succ_eq_step',
    universalPrefix_bits α x α.length (le_refl _), List.take_length]
  rw [universalPrefix_step _ _ _ _ _ (some false) (by
    rw [inputSymbol_at _ (2 * α.length) (by omega) (by rfl)]
    exact (universal_pair_separator α x).1)]
  simp only [universalPrefixTM, Option.map_some, Option.toList_none, List.append_nil]
  rw [moveInputPos_pos_of_ne_right _ (by simp only [Fin.val_mk]; omega)]

/-- A live later configuration excludes all earlier halts, since halting is
absorbing. This is used for administrative phases, independently of outputs. -/
private lemma universal_live_before {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) {s t : ℕ}
    (hst : s ≤ t) (ht : (tm.runFrom cfg t).state ≠ none) :
    (tm.runFrom cfg s).state ≠ none := by
  intro hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs] at ht
  exact ht hs

/-- No prefix extraction step before the separator's second bit can halt. -/
private lemma universalPrefix_live (α x : List Bool) (s : ℕ)
    (hs : s < 2 * α.length + 2) :
    (universalPrefixTM.tm.runFrom
      (universalPrefixTM.tm.initCfg (pairEncode α x)) s).state ≠ none := by
  apply universal_live_before universalPrefixTM.tm _ (show s ≤ 2 * α.length + 1 by omega)
  rw [universalPrefix_penultimate]
  exact Option.some_ne_none _

/-- Extract the code prefix, then run the given canonizer on the code buffer. -/
def universalCanonTM (c : EffectiveMachineCode) : FinTM Bool :=
  bufferedCompTM universalPrefixTM c.canonizer

/-- Exact prefix-local canonizer start: `3|α|+4` transitions suffice, regardless
of the suffix, and its first symbol has not been read.

**Proof sketch.** Extraction takes `2|α|+2` transitions and is live until its
last transition. The existing buffered first-phase invariant captures precisely
`α`. Its unconditional first left move and rewind use `|α|+2` further transitions,
including when `α` is empty. The resulting second-phase configuration starts the
canonizer on virtual input `α`, while the real head remains at the suffix start. -/
private lemma universalCanon_start (c : EffectiveMachineCode) (α x : List Bool) :
    (universalCanonTM c).tm.runFrom
      ((universalCanonTM c).tm.initCfg (pairEncode α x)) (3 * α.length + 4) =
    bufferedSecondCfg universalPrefixTM c.canonizer (c.canonizer.tm.initCfg α) true
      ⟨2 * α.length + 3, by rw [universal_pair_length]; omega⟩
      (fun i => i.elim0) (fun i => i.elim0) := by
  change (bufferedCompTM universalPrefixTM c.canonizer).tm.runFrom _ _ = _
  rw [show 3 * α.length + 4 = (2 * α.length + 2) + (α.length + 2) by omega,
    MultiTapeTM.runFrom_add, bufferedFirstCfg_init,
    bufferedFirstCfg_run universalPrefixTM c.canonizer _ _
      (fun s hs => universalPrefix_live α x s hs), universalPrefix_start]
  exact bufferedFirstCfg_rewind universalPrefixTM c.canonizer _ rfl

/-- The entire canonizer run serves input from the code tape and leaves the
physical suffix head fixed. Its bound depends on the code alone. -/
private lemma universalCanon_run (c : EffectiveMachineCode) (α x : List Bool) (t : ℕ) :
    ∃ b, (universalCanonTM c).tm.runFrom
      ((universalCanonTM c).tm.initCfg (pairEncode α x)) (3 * α.length + 4 + t) =
    bufferedSecondCfg universalPrefixTM c.canonizer
      (c.canonizer.tm.runFrom (c.canonizer.tm.initCfg α) t) b
      ⟨2 * α.length + 3, by rw [universal_pair_length]; omega⟩
      (fun i => i.elim0) (fun i => i.elim0) := by
  rw [MultiTapeTM.runFrom_add, universalCanon_start]
  obtain ⟨b, -, he⟩ := bufferedSecondCfg_run universalPrefixTM c.canonizer
    (c.canonizer.tm.initCfg α) true
    (by constructor <;> intro h <;> simp_all [VirtualTag])
    (x := pairEncode α x)
    (⟨2 * α.length + 3, by rw [universal_pair_length]; omega⟩)
    (fun i => i.elim0) (fun i => i.elim0) t
  exact ⟨b, he⟩

/-- Exact canonical-table correspondence at a suffix-independent time.
The chosen scheme is a parameter; this uses only its canonizer contract, never
`exists_effectiveMachineCode`.

**Proof sketch.** The virtual canonizer run ends with precisely the contracted
serialization. Project state, output, and input position from the complete
configuration equality. Absorbing halting permits using the supplied time bound. -/
lemma universalCanon_complete (c : EffectiveMachineCode) (α x : List Bool) :
    let cfg := (universalCanonTM c).tm.runFrom
      ((universalCanonTM c).tm.initCfg (pairEncode α x))
      (3 * α.length + 4 + c.canonizerTime α.length)
    cfg.state = none ∧ cfg.output = (c.decode α).serialize ∧
      cfg.inputPos.val = 2 * α.length + 3 := by
  dsimp only
  obtain ⟨b, he⟩ := universalCanon_run c α x (c.canonizerTime α.length)
  rw [he]
  have hc := (computesInTime_iff _ _ _ _).mp (c.canonizer_computes α)
  exact ⟨by simp only [bufferedSecondCfg, hc.1, Option.map_none], hc.2, rfl⟩


/-- Suffix lookups use the code-prefix offset and do not change the suffix. -/
private lemma universal_pair_suffix (α x : List Bool) (j : ℕ) :
    (pairEncode α x)[2 * α.length + 2 + j]? = x[j]? := by
  have hl : (α.flatMap fun b => [b, b]).length = 2 * α.length := by
    have h := universal_pair_length α []
    simp only [pairEncode, List.length_append, List.length_cons, List.length_nil] at h
    omega
  simp only [pairEncode, List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  rw [hl, show 2 * α.length + 2 + j - 2 * α.length = j + 1 + 1 by omega]
  rfl

/-- Embed a virtual suffix head, including both boundaries, into the physical
paired input. Virtual position zero lies on the delimiter's last cell. -/
def universalInputPos (α x : List Bool) (p : Fin (x.length + 2)) :
    Fin ((pairEncode α x).length + 2) :=
  ⟨2 * α.length + 2 + p.val, by rw [universal_pair_length]; omega⟩

/-- Only the physical input position changes in this configuration embedding. -/
private def universalInputCfg {k : ℕ} {S : Type} (α : List Bool) {x : List Bool}
    (cfg : Cfg k Bool S x) : Cfg k Bool S (pairEncode α x) :=
  ⟨cfg.state, universalInputPos α x cfg.inputPos, cfg.workTapes, cfg.workTapePos,
    cfg.output⟩

/-- A permanent marker at coordinate zero identifies exactly the virtual left
boundary. The marker tape's head follows the virtual position, not the physical
delimiter coordinate. -/
private lemma universal_marker (p : ℕ) :
    bufferTape [true] (p : ℤ) = if p = 0 then some true else none := by
  rw [bufferTape_nat]
  cases p <;> simp

/-- Masking the delimiter by the left marker yields the native input symbol,
including the adjacent left and right boundaries of an empty suffix.

**Proof sketch.** At virtual zero the explicit marker supplies blank. At every
positive virtual position, the physical lookup is the suffix lookup at position
minus one. The optional lookup formulation also covers the right blank. -/
lemma universalInput_read {k : ℕ} {S : Type} (α : List Bool) {x : List Bool}
    (cfg : Cfg k Bool S x) :
    (if bufferTape [true] (cfg.inputPos.val : ℤ) = some true then none
      else (universalInputCfg α cfg).inputSymbol) = cfg.inputSymbol := by
  rw [universal_marker]
  by_cases h0 : cfg.inputPos.val = 0
  · have hp : cfg.inputPos = 0 := Fin.ext h0
    simp [hp, Cfg.inputSymbol]
  · simp only [if_neg h0, reduceCtorEq, ↓reduceIte]
    have hp := cfg.inputPos.isLt
    have hi : cfg.inputPos.val - 1 ≤ x.length := by omega
    have he : cfg.inputPos.val = (cfg.inputPos.val - 1) + 1 := by omega
    rw [inputSymbol_at cfg _ hi he]
    rw [inputSymbol_at _ (2 * α.length + 2 + (cfg.inputPos.val - 1))
      (by rw [universal_pair_length]; omega)
      (by simp only [universalInputCfg, universalInputPos, Fin.val_mk]; omega)]
    exact universal_pair_suffix α x _

/-- The marker-derived boundary tag satisfies the existing virtual-movement
contract. At the right blank the marker is absent, including on empty input. -/
private lemma universalInput_tag {n : ℕ} (p : Fin (n + 2)) :
    VirtualTag p (decide (bufferTape [true] (p.val : ℤ) ≠ some true)) := by
  rw [universal_marker]
  constructor
  · intro h; simp [h]
  · intro h; simp [h]

/-- Clamped virtual motion commutes with the physical suffix embedding, and
moving the marker head by the same amount preserves its coordinate invariant.

**Proof sketch.** The established buffer-motion lemma gives the integer equation
for the virtual head. Both its old and new positions lie in the virtual input's
closed boundary interval. Adding the prefix offset puts this whole interval
inside the physical tape, so the same clamped move realizes the shifted equation.
In particular, a left move at virtual zero is suppressed. -/
lemma universalInput_move {k : ℕ} {S : Type} (α : List Bool) {x : List Bool}
    (cfg : Cfg k Bool S x) (d : SignType) :
    let b := decide (bufferTape [true] (cfg.inputPos.val : ℤ) ≠ some true)
    let m := virtualMove b cfg.inputSymbol d
    moveInputPos (universalInputPos α x cfg.inputPos) m =
      universalInputPos α x (moveInputPos cfg.inputPos d) ∧
    (cfg.inputPos.val : ℤ) + (m : ℤ) = ((moveInputPos cfg.inputPos d).val : ℤ) := by
  dsimp only
  have hm := (virtualMove_correct cfg _ (universalInput_tag cfg.inputPos) d).1
  have hl := universal_pair_length α x
  have hn := (moveInputPos cfg.inputPos d).isLt
  constructor
  · apply Fin.ext
    have hpos : (cfg.inputPos.val : ℤ) +
        (virtualMove (decide (bufferTape [true] (cfg.inputPos.val : ℤ) ≠ some true))
          cfg.inputSymbol d : ℤ) = ((moveInputPos cfg.inputPos d).val : ℤ) := by omega
    have he : (((universalInputPos α x cfg.inputPos).val : ℤ) +
        (virtualMove (decide (bufferTape [true] (cfg.inputPos.val : ℤ) ≠ some true))
          cfg.inputSymbol d : ℤ)).toNat =
        2 * α.length + 2 + (moveInputPos cfg.inputPos d).val := by
      simp only [universalInputPos, Fin.val_mk]
      omega
    unfold moveInputPos
    simp only [he]
    rw [dif_pos (by omega)]
    rfl
  · omega


/-- Capture a machine's emissions on an additional table tape, then transfer
control to a four-tape interpreter. The interpreter sees the original physical
input, not a virtual copy of it. Its other three tapes initially remain blank. -/
def universalCaptureTM {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) : FinTM Bool where
  k := M.k + (1 + 3)
  State := Option M.State ⊕ S
  tm :=
    { q₀ := .inl (some M.tm.q₀)
      tr := fun q inp work => match q with
        | .inl (some q) =>
          let a := M.tm.tr q inp (fun i => work (Fin.castAdd 4 i))
          ⟨a.inputTape, tapeBlocks a.workTapes
            (a.output.map some, if a.output = none then 0 else .pos)
            (fun _ => (none, 0)), none, some (.inl a.state)⟩
        | .inl none => controlAction 0 (some (.inr D.q₀))
        | .inr q => rightAction M.k Sum.inr
            (D.tr q inp (fun i => work (Fin.natAdd M.k i))) }

/-- Complete first-phase configuration of the output-capture wrapper. -/
def universalCaptureCfg {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) :
    Cfg (universalCaptureTM M D).k Bool (universalCaptureTM M D).State x where
  state := some (.inl cfg.state)
  inputPos := cfg.inputPos
  workTapes := tapeBlocks cfg.workTapes (bufferTape cfg.output) (fun _ _ => none)
  workTapePos := tapeBlocks cfg.workTapePos cfg.output.length (fun _ => 0)
  output := []

/-- The capture wrapper starts with a blank table and blank interpreter tapes. -/
private lemma universalCapture_init {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) (x : List Bool) :
    (universalCaptureTM M D).tm.initCfg x =
      universalCaptureCfg M D (M.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [universalCaptureCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [universalCaptureCfg, tapeBlocks]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [universalCaptureCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [universalCaptureCfg, tapeBlocks]

/-- One live transition captures every emitted bit, including a bit emitted on
the source machine's halting transition. Administrative states remain live.

**Proof sketch.** The original work block and physical input move in lockstep.
An emission writes precisely the table's right blank and advances its head; the
buffer-append identity gives its new contents. No real output is emitted, and
the three later simulation tapes remain untouched. -/
private lemma universalCapture_step {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (hs : cfg.state ≠ none) :
    (universalCaptureTM M D).tm.step (universalCaptureCfg M D cfg) =
      universalCaptureCfg M D (M.tm.step cfg) := by
  unfold MultiTapeTM.step
  cases hq : cfg.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (universalCaptureCfg M D cfg).state = some (.inl (some q)) := by
      simp [universalCaptureCfg, hq]
    rw [hs']
    dsimp only [universalCaptureTM]
    have hr : (fun i => (universalCaptureCfg M D cfg).workTapeSymbols
        (Fin.castAdd 4 i)) = cfg.workTapeSymbols := by
      funext i
      simp [universalCaptureCfg, Cfg.workTapeSymbols, tapeBlocks]
    have hi : (universalCaptureCfg M D cfg).inputSymbol = cfg.inputSymbol := rfl
    rw [hr, hi]
    let a := M.tm.tr q cfg.inputSymbol cfg.workTapeSymbols
    change (⟨a.inputTape, tapeBlocks a.workTapes
      (a.output.map some, if a.output = none then 0 else .pos)
      (fun _ => (none, 0)), none, some (.inl a.state)⟩ :
      Action (M.k + (1 + 3)) Bool _).apply _ = universalCaptureCfg M D (a.apply cfg)
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [universalCaptureCfg, tapeBlocks, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;>
            simp [universalCaptureCfg, tapeBlocks, Action.apply, ho, bufferTape_append]
        · intro j; simp [universalCaptureCfg, tapeBlocks, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [universalCaptureCfg, tapeBlocks, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [universalCaptureCfg, tapeBlocks, Action.apply, ho]
        · intro j; simp [universalCaptureCfg, tapeBlocks, Action.apply]
    · simp [universalCaptureCfg, tapeBlocks, Action.apply]

/-- Lockstep capture through the first halting transition. -/
private lemma universalCapture_run {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (t : ℕ)
    (h : ∀ s, s < t → (M.tm.runFrom cfg s).state ≠ none) :
    (universalCaptureTM M D).tm.runFrom (universalCaptureCfg M D cfg) t =
      universalCaptureCfg M D (M.tm.runFrom cfg t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      universalCapture_step M D _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Capture and interpreter entry preserve the entire halted source configuration
as inactive data, except that its output is now on the table tape. -/
def universalCapturedCfg {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) :
    Cfg (universalCaptureTM M D).k Bool (universalCaptureTM M D).State x :=
  { universalCaptureCfg M D cfg with state := some (.inr D.q₀) }

/-- A halted source configuration transfers to the live interpreter entry state. -/
private lemma universalCapture_transfer {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (h : cfg.state = none) :
    (universalCaptureTM M D).tm.step (universalCaptureCfg M D cfg) =
      universalCapturedCfg M D cfg := by
  unfold MultiTapeTM.step
  simp only [universalCaptureCfg, h]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · rfl
  · funext i; exact add_zero _
  · rfl

/-- Every completed source computation reaches the interpreter with the table
captured in at most one extra transition.

**Proof sketch.** Choose the first source halting time. Lockstep capture holds
through that transition; one live administrative transition enters the interpreter.
Absorbing source halting identifies this first halted configuration with the one
at the supplied time bound, so all its fields (including parked input position)
are retained, not merely its completed output. -/
lemma universalCapture_start {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) (x : List Bool) (T : ℕ)
    (h : (M.tm.runFrom (M.tm.initCfg x) T).state = none) :
    ∃ t, t ≤ T + 1 ∧
      (universalCaptureTM M D).tm.runFrom ((universalCaptureTM M D).tm.initCfg x) t =
        universalCapturedCfg M D (M.tm.runFrom (M.tm.initCfg x) T) := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none := ⟨T, h⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh h
  have hs : (M.tm.runFrom (M.tm.initCfg x) t).state = none := Nat.find_spec hh
  have he : M.tm.runFrom (M.tm.initCfg x) T = M.tm.runFrom (M.tm.initCfg x) t := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
    rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs]
  refine ⟨t + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', universalCapture_init,
    universalCapture_run M D _ t (fun s hs => Nat.find_min hh hs),
    universalCapture_transfer M D _ hs, he]

/-- Prefix-only startup with the actual canonical table on a work tape. The
input suffix stays in place, unread during startup, and the interpreter receives
three blank work tapes for state, simulated work, and the virtual-left marker.

**Proof sketch.** Compose the configuration-level prefix/canonizer run with the
capture theorem. The bound `3|α|+5+canonizerTime |α|` is independent of the suffix.
The equality is of full configurations, and the three projections explicitly
identify the completed table, the parked physical head, and the still-empty output. -/
private lemma universal_captured_table {S : Type} [Fintype S] [DecidableEq S]
    (c : EffectiveMachineCode) (D : MultiTapeTM 4 Bool S) (α x : List Bool) :
    ∃ t, t ≤ 3 * α.length + 5 + c.canonizerTime α.length ∧
      let cfg := (universalCaptureTM (universalCanonTM c) D).tm.runFrom
        ((universalCaptureTM (universalCanonTM c) D).tm.initCfg (pairEncode α x)) t
      cfg.state = some (.inr D.q₀) ∧
      cfg.inputPos.val = 2 * α.length + 3 ∧
      cfg.workTapes (Fin.natAdd (universalCanonTM c).k (0 : Fin 4)) =
        bufferTape (c.decode α).serialize ∧ cfg.output = [] := by
  have hc := universalCanon_complete c α x
  obtain ⟨t, ht, he⟩ := universalCapture_start (universalCanonTM c) D (pairEncode α x)
    (3 * α.length + 4 + c.canonizerTime α.length) hc.1
  refine ⟨t, by omega, ?_⟩
  dsimp only
  rw [he]
  refine ⟨rfl, hc.2.2, ?_, rfl⟩
  change tapeBlocks _ _ _
    (Fin.natAdd (universalCanonTM c).k (Fin.castAdd 3 (0 : Fin 1))) = _
  rw [tapeBlocks_buffer, hc.2.1]

end Turing
