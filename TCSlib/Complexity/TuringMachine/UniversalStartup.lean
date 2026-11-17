/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Build.Embed

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
are the epoch-3 fill, batches B (WIP) and B2 (completion), except that the capture
phase is now the bank-embedding library's returning silent embedding
(`Turing.embedSilentRetTM`).

## Main definitions / Main results

* `Turing.universalPrefixTM` — the prefix parser of the doubled code region.
* `Turing.prefixCanonTM` — prefix extraction composed with any canonizer, by buffered
  composition (`Turing.prefixCanon_start`, `Turing.prefixCanon_run`,
  `Turing.prefixCanon_complete`); promoted, generic in the canonizer, for the `k`-generic
  startup `Turing.exists_selfStartupTMK` (user, 2026-10-15).
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

/-- **The prefix parser** of the doubled code region of `pairEncode α x` (public, since the
prefix canonizer's run lemmas `Turing.prefixCanon_start` and `Turing.prefixCanon_run` name it;
user 2026-10-15). A two-state register: the outer optional
state of a configuration is halting; `none` inside the finite control means that the first
half of a pair is next. On a valid pair, the second half emits its undoubled bit; on the
separator it moves to the suffix and halts without emitting. [AB09, §1.4.1, proof of
Theorem 1.9: the universal machine reads the code of `M` first] -/
def universalPrefixTM : FinTM Bool where
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

/-! The prefix parser's tape count (`0`) and state type (`Option Bool`), as equations (the
specification API, the briefs' pre-ship inventories, 2026-10-16), generated by `simps` without the
`simp` attribute. -/
attribute [simps (config := { isSimp := false }) k State] universalPrefixTM

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
  exact MultiTapeTM.runFrom_state_ne_none_of_le tm cfg t ht s hst

/-- No prefix extraction step before the separator's second bit can halt. -/
private lemma universalPrefix_live (α x : List Bool) (s : ℕ)
    (hs : s < 2 * α.length + 2) :
    (universalPrefixTM.tm.runFrom
      (universalPrefixTM.tm.initCfg (pairEncode α x)) s).state ≠ none := by
  apply universal_live_before universalPrefixTM.tm _ (show s ≤ 2 * α.length + 1 by omega)
  rw [universalPrefix_penultimate]
  exact Option.some_ne_none _

/-- **The prefix canonizer** (generic in the canonizer; promoted for
`Turing.exists_selfStartupTMK`, user 2026-10-15): extract the code prefix of `pairEncode α x`,
then run the canonizer `F` on the extracted code from a buffer (`Turing.bufferedCompTM`).
`Turing.universalCanonTM` is its instance at a one-tape scheme's canonizer. [AB09, §1.4.1,
proof of Theorem 1.9] -/
def prefixCanonTM (F : FinTM Bool) : FinTM Bool :=
  bufferedCompTM universalPrefixTM F

/-- The prefix canonizer is the buffered composite of the prefix parser and the canonizer:
`prefixCanonTM F = bufferedCompTM universalPrefixTM F` (the specification API, the briefs' pre-ship
inventories, 2026-10-16). With `bufferedCompTM_k` and `universalPrefixTM_k` it has `0 + (1 + F.k)`
tapes. -/
theorem prefixCanonTM_eq (F : FinTM Bool) : prefixCanonTM F = bufferedCompTM universalPrefixTM F :=
  rfl

/-- Extract the code prefix, then run the scheme's canonizer on the code buffer: the prefix
canonizer `Turing.prefixCanonTM` at `c.canonizer`. -/
def universalCanonTM (c : EffectiveMachineCode) : FinTM Bool :=
  prefixCanonTM c.canonizer

/-- **The prefix canonizer's start** (promoted, generic in the canonizer): `3|α|+4`
transitions suffice, regardless of the suffix, and its first symbol has not been read.

**Proof sketch.** Extraction takes `2|α|+2` transitions and is live until its
last transition. The existing buffered first-phase invariant captures precisely
`α`. Its unconditional first left move and rewind use `|α|+2` further transitions,
including when `α` is empty. The resulting second-phase configuration starts the
canonizer on virtual input `α`, while the real head remains at the suffix start. -/
theorem prefixCanon_start (F : FinTM Bool) (α x : List Bool) :
    (prefixCanonTM F).tm.runFrom
      ((prefixCanonTM F).tm.initCfg (pairEncode α x)) (3 * α.length + 4) =
    bufferedSecondCfg universalPrefixTM F (F.tm.initCfg α) true
      ⟨2 * α.length + 3, by rw [universal_pair_length]; omega⟩
      (fun i => i.elim0) (fun i => i.elim0) := by
  change (bufferedCompTM universalPrefixTM F).tm.runFrom _ _ = _
  rw [show 3 * α.length + 4 = (2 * α.length + 2) + (α.length + 2) by omega,
    MultiTapeTM.runFrom_add, bufferedFirstCfg_init,
    bufferedFirstCfg_run universalPrefixTM F _ _
      (fun s hs => universalPrefix_live α x s hs), universalPrefix_start]
  exact bufferedFirstCfg_rewind universalPrefixTM F _ rfl

/-- **The prefix canonizer's run** (promoted, generic in the canonizer): the entire canonizer
run serves input from the code tape and leaves the physical suffix head fixed. Its bound depends
on the code alone.

**Proof sketch.** The start (`Turing.prefixCanon_start`), then the buffered second phase
(`Turing.bufferedSecondCfg_run`). -/
theorem prefixCanon_run (F : FinTM Bool) (α x : List Bool) (t : ℕ) :
    ∃ b, (prefixCanonTM F).tm.runFrom
      ((prefixCanonTM F).tm.initCfg (pairEncode α x)) (3 * α.length + 4 + t) =
    bufferedSecondCfg universalPrefixTM F
      (F.tm.runFrom (F.tm.initCfg α) t) b
      ⟨2 * α.length + 3, by rw [universal_pair_length]; omega⟩
      (fun i => i.elim0) (fun i => i.elim0) := by
  rw [MultiTapeTM.runFrom_add, prefixCanon_start]
  obtain ⟨b, -, he⟩ := bufferedSecondCfg_run universalPrefixTM F
    (F.tm.initCfg α) true
    (by constructor <;> intro h <;> simp_all [VirtualTag])
    (x := pairEncode α x)
    (⟨2 * α.length + 3, by rw [universal_pair_length]; omega⟩)
    (fun i => i.elim0) (fun i => i.elim0) t
  exact ⟨b, he⟩

/-- **The prefix canonizer's result** (promoted, generic in the canonizer): if `F` computes `f`
in time `τ`, the prefix canonizer on `pairEncode α x` has halted at the suffix-independent time
`3|α| + 4 + τ |α|` with output `f α` and the input head at `2|α| + 3`. [AB09, §1.4.1, proof of
Theorem 1.9]

**Proof sketch.** The virtual canonizer run ends with precisely the contracted
serialization. Project state, output, and input position from the complete
configuration equality. Absorbing halting permits using the supplied time bound. -/
theorem prefixCanon_complete (F : FinTM Bool) (f : List Bool → List Bool) (τ : ℕ → ℕ)
    (hF : F.ComputesFunInTime f τ) (α x : List Bool) :
    let cfg := (prefixCanonTM F).tm.runFrom
      ((prefixCanonTM F).tm.initCfg (pairEncode α x)) (3 * α.length + 4 + τ α.length)
    cfg.state = none ∧ cfg.output = f α ∧ cfg.inputPos.val = 2 * α.length + 3 := by
  dsimp only
  obtain ⟨b, he⟩ := prefixCanon_run F α x (τ α.length)
  rw [he]
  have hc := (computesInTime_iff _ _ _ _).mp (hF α)
  exact ⟨by simp only [bufferedSecondCfg, hc.1, Option.map_none], hc.2, rfl⟩

/-- Exact canonical-table correspondence at a suffix-independent time.
The chosen scheme is a parameter; this uses only its canonizer contract, never
`exists_effectiveMachineCode`.

**Proof sketch.** The prefix canonizer's result (`Turing.prefixCanon_complete`) at the scheme's
canonizer and its contract. -/
lemma universalCanon_complete (c : EffectiveMachineCode) (α x : List Bool) :
    let cfg := (universalCanonTM c).tm.runFrom
      ((universalCanonTM c).tm.initCfg (pairEncode α x))
      (3 * α.length + 4 + c.canonizerTime α.length)
    cfg.state = none ∧ cfg.output = (c.decode α).serialize ∧
      cfg.inputPos.val = 2 * α.length + 3 :=
  prefixCanon_complete c.canonizer _ c.canonizerTime c.canonizer_computes α x


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


/-- The capture phase's tape selection: the source machine's work tapes are the host's first
`n` tapes. -/
private def universalCaptureSel (n : ℕ) : Fin n ↪ Fin (n + (1 + 3)) :=
  ⟨Fin.castAdd (1 + 3), Fin.castAdd_injective _ _⟩

/-- The capture phase's states inside the wrapper's: a live source state `q` is `.inl (some q)`,
and the return anchor after the source halts is the live administrative state `.inl none`. -/
private def universalCaptureTag (Q S : Type) : Q ⊕ Unit ↪ Option Q ⊕ S :=
  (Equiv.optionEquivSumPUnit Q).symm.toEmbedding.trans Function.Embedding.inl

/-- Capture a machine's emissions on an additional table tape, then transfer
control to a four-tape interpreter. The interpreter sees the original physical
input, not a virtual copy of it. Its other three tapes initially remain blank.
The capture phase is the returning silent embedding `Turing.embedSilentRetTM` of the source
on the first `M.k` tapes, with the table tape as its capture tape. -/
def universalCaptureTM {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) : FinTM Bool where
  k := M.k + (1 + 3)
  State := Option M.State ⊕ S
  tm :=
    { q₀ := .inl (some M.tm.q₀)
      tr := fun q inp work => match q with
        | .inl (some q) =>
          ((embedSilentRetTM (universalCaptureSel M.k) (Fin.natAdd M.k (Fin.castAdd 3 0))
            M.tm).tr (.inl q) inp work).mapState (universalCaptureTag M.State S)
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

/-- A host tape that is neither a source tape nor the table tape is outside the selection. -/
private lemma universalCapture_off (n : ℕ) (j : Fin (n + (1 + 3))) (hj : n ≤ j.val) :
    j ∉ Set.range (universalCaptureSel n) := by
  rintro ⟨i, rfl⟩
  exact absurd hj (Nat.not_le.mpr i.isLt)

/-- A source configuration on the capture wrapper's tapes: the silent embedding with a blank
frame, an empty table prefix and an empty output. -/
private abbrev universalCaptureEmb (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) : Cfg (M.k + (1 + 3)) Bool M.State x :=
  embedSilentCfg (universalCaptureSel M.k) (Fin.natAdd M.k (Fin.castAdd 3 0)) (fun _ _ => none)
    (fun _ => 0) [] [] cfg

/-- **The capture configuration is the renamed embedded one.** A configuration with the data
fields of the embedding of `cfg`, whose renamed state is `.inl cfg.state`, is the capture
configuration of `cfg`.

**Proof sketch.** Compare the five fields. On the work tapes and heads, split the host tapes into
the three blocks of `Turing.tapeBlocks`: the source block is the embedding's selected tapes
(`Turing.embedSilentCfg_selected_tape`), the table tape its capture tape
(`Turing.embedSilentCfg_cap`), and the interpreter block its blank frame
(`Turing.embedSilentCfg_unselected`). -/
private lemma universalCapture_embed {S T : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (d : Cfg (M.k + (1 + 3)) Bool T x)
    (f : T → Option M.State ⊕ S) (hs : d.state.map f = some (.inl cfg.state))
    (hi : d.inputPos = (universalCaptureEmb M cfg).inputPos)
    (hw : ∀ j, d.workTapes j = (universalCaptureEmb M cfg).workTapes j)
    (hp : ∀ j, d.workTapePos j = (universalCaptureEmb M cfg).workTapePos j)
    (ho : d.output = (universalCaptureEmb M cfg).output) :
    d.mapState f = universalCaptureCfg M D cfg := by
  have hcap := embedSilentCfg_cap (universalCaptureSel M.k) (Fin.natAdd M.k (Fin.castAdd 3 0))
    (universalCapture_off M.k _ (Nat.le_add_right _ _)) (fun _ _ => none) (fun _ => 0) [] [] cfg
  have hframe (j : Fin 3) := embedSilentCfg_unselected (universalCaptureSel M.k)
    (Fin.natAdd M.k (Fin.castAdd 3 0)) (fun _ _ => none) (fun _ => 0) [] [] cfg
    (Fin.natAdd M.k (Fin.natAdd 1 j)) (universalCapture_off M.k _ (Nat.le_add_right _ _))
    (fun h => by have := congrArg Fin.val h; simp at this)
  refine Cfg.ext (by rw [Cfg.mapState_state, hs]; rfl)
    (by rw [Cfg.mapState_inputPos, hi, embedSilentCfg_inputPos]; rfl) ?_ ?_
    (by rw [Cfg.mapState_output, ho, embedSilentCfg_output]; rfl)
  · funext i z
    rw [Cfg.mapState_workTapes, hw]
    refine Fin.addCases (fun j => ?_) (fun j => Fin.addCases (fun j => ?_) (fun j => ?_) j) i
    · exact (congrFun (embedSilentCfg_selected_tape _ _ _ _ _ _ cfg j) z).trans
        (congrFun (tapeBlocks_left _ _ _ j) z).symm
    · rw [Subsingleton.elim j 0, hcap.1, List.nil_append]
      exact (congrFun (tapeBlocks_buffer _ _ _ 0) z).symm
    · exact (congrFun (hframe j).1 z).trans
        (congrFun (tapeBlocks_right _ _ (fun _ _ => none) j) z).symm
  · funext i
    rw [Cfg.mapState_workTapePos, hp]
    refine Fin.addCases (fun j => ?_) (fun j => Fin.addCases (fun j => ?_) (fun j => ?_) j) i
    · exact (embedSilentCfg_selected_pos _ _ _ _ _ _ cfg j).trans (tapeBlocks_left _ _ _ j).symm
    · rw [Subsingleton.elim j 0, hcap.2, List.nil_append]
      exact (tapeBlocks_buffer _ _ (fun _ => (0 : ℤ)) 0).symm
    · exact (hframe j).2.trans (tapeBlocks_right _ _ (fun _ => (0 : ℤ)) j).symm

/-- Capture and interpreter entry preserve the entire halted source configuration
as inactive data, except that its output is now on the table tape. -/
def universalCapturedCfg {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) :
    Cfg (universalCaptureTM M D).k Bool (universalCaptureTM M D).State x :=
  { universalCaptureCfg M D cfg with state := some (.inr D.q₀) }

/-- Every completed source computation reaches the interpreter with the table
captured in at most one extra transition.

**Proof sketch.** Choose the first source halting time `t`. The capture phase is the returning
silent embedding of the source (`Turing.embedSilentRetTM`) with its states renamed into the
wrapper's; the two tables agree on every live embedded state, so the renamed contract
`Turing.embedSilentRetTM_run` transports through time `t`
(`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`), ending at the return anchor `.inl none` over
the halted source's capture configuration. One administrative transition enters the
interpreter. Absorbing source halting identifies this first halted configuration with the one
at the supplied time bound, so all its fields (including parked input position)
are retained, not merely its completed output. -/
lemma universalCapture_start {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) (x : List Bool) (T : ℕ)
    (h : (M.tm.runFrom (M.tm.initCfg x) T).state = none) :
    ∃ t, t ≤ T + 1 ∧
      (universalCaptureTM M D).tm.runFrom ((universalCaptureTM M D).tm.initCfg x) t =
        universalCapturedCfg M D (M.tm.runFrom (M.tm.initCfg x) T) := by
  classical
  obtain ⟨t, ht, hlive, hcut⟩ := MultiTapeTM.exists_first_halt M.tm (M.tm.initCfg x) h
  have hs : (M.tm.runFrom (M.tm.initCfg x) t).state = none :=
    (congrArg Cfg.state hcut).trans h
  have hq₀ : (M.tm.initCfg x).state = some M.tm.q₀ := by
    rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
  obtain ⟨-, hend, hfirst⟩ := embedSilentRetTM_run (universalCaptureSel M.k)
    (Fin.natAdd M.k (Fin.castAdd 3 0)) (universalCapture_off M.k _ (Nat.le_add_right _ _)) M.tm
    (fun _ _ => none) (fun _ => 0) [] [] (M.tm.initCfg x) t
    (by rw [hq₀]; exact Option.some_ne_none _) hlive hs
  have hrun := MultiTapeTM.runFrom_mapState_of_agreeOn _ (universalCaptureTM M D).tm
    (universalCaptureTag M.State S) (· ≠ Sum.inr ())
    (by rintro (q | ⟨⟩) hq inp work; exacts [rfl, absurd rfl hq]) _ t
    (fun u hu q hq hqe => hfirst u hu (hqe ▸ hq))
  refine ⟨t + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', universalCapture_init,
    ← universalCapture_embed M D (M.tm.initCfg x)
      ((universalCaptureEmb M (M.tm.initCfg x)).mapState Sum.inl) (universalCaptureTag M.State S)
      (by rw [Cfg.mapState_state, embedSilentCfg_state, hq₀]; rfl)
      (Cfg.mapState_inputPos _ _) (fun j => funext fun z => Cfg.mapState_workTapes _ _ j z)
      (fun j => Cfg.mapState_workTapePos _ _ j) (Cfg.mapState_output _ _), ← hcut]
  refine (congrArg (universalCaptureTM M D).tm.step (hrun.trans ((congrArg _ hend).trans
    (universalCapture_embed M D _ _ _ (by rw [hs]; rfl) rfl (fun _ => rfl) (fun _ => rfl)
      rfl)))).trans ?_
  -- the administrative transition into the interpreter
  rw [MultiTapeTM.step_of_some (q := (.inl none : Option M.State ⊕ S)) (by rw [← hs]; rfl)]
  change (controlAction 0 (some (Sum.inr D.q₀ : Option M.State ⊕ S))).apply _ = _
  rw [controlAction_apply, moveInputPos_zero]
  rfl

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
