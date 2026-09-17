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
# The universal Turing machine

[AB09, §1.4.1 and Theorem 1.9, relaxed form]: there is a single machine `U` that,
given a code and an input, simulates the machine the code denotes — `U(x, α) =
M_α(x)` — with the simulation overhead depending only on the code, not on the input.

## Design and deviations from [AB09] (all shaped by the phase-3 audit)

* Statements are relative to an `Turing.EffectiveMachineCode`: the purely algebraic
  scheme admits noncomputable-meaning pathologies against which no universal machine
  exists (audit finding 1, Argument A).
* **Input layout is `pairEncode α x` — code first, input second** — deviating from
  [AB09]'s `⟨x, α⟩`: with the input first, the startup cost of reaching the code
  grows with `|x|` and the stated bounds are false (audit finding 2, Argument B).
  With the code first, startup (parsing and canonizing `α`) costs a constant
  depending only on `α`, absorbed into `C`, and the simulated input head walks the
  verbatim `x` region on demand.
* `universal` is the **all-string evaluator** [AB09's `U(x, α) = M_α(x)`, p. 20]:
  it covers every `α` through `c.decode` (padded and fallback representations
  included), and it carries **both directions** — the forward time bound, and the
  converse that any *completed* output of `U` (output on halting; intermediate
  emissions of a non-halting run are unconstrained) is a completed output of the
  simulated machine, so divergence is preserved (round-1 finding 3; round-2
  Argument C).
* The constant `C` depends on the **representation** `α`, a documented weakening of
  [AB09]'s machine-dependent constant that is *necessary* at this generality: an
  effective scheme can reserve arbitrarily long identical-prefix representations of
  two fixed machines, defeating any constant that factors through `c.decode α`
  (round-2 audit, finding 6 and Argument E). Recovering the book's dependence would
  require further representation assumptions.
* **The core bound is linear**, `C · (t + 1)`: coded machines are already in
  one-work-tape binary normal form, so `U` pays a constant per simulated step.
  [AB09]'s relaxed quadratic bound reappears in `universal_quadratic`, where an
  *arbitrary* binary machine is first normal-formed ([AB09, Claims 1.5-1.6]); that
  corollary is stated — and labeled — at the level of **total function computation**
  (audit finding 4), the machine-level partial statement being `universal` itself.
  The `O(T log T)` sharpening ([AB09, §1.7]) is the phase-5 stretch goal.
* `timed_universal` outputs `true :: output` on success and `[false]` on timeout, a
  concrete rendering of [AB09]'s "special failure symbol" (§1.4.1); its budget is
  quadratic (binary clock maintenance). The deadline convention: halting is checked
  after every simulated transition *including the `t`-th*, so a machine first
  halting exactly at the deadline is a success; at budget `0` no initialized machine
  has halted, and the timeout branch applies (audit finding 6).

## Main results

* `Turing.universal` — the all-string evaluator [AB09, Theorem 1.9 core].
* `Turing.universal_quadratic` — the relaxed quadratic form for total functions of
  arbitrary binary machines [AB09, Theorem 1.9 as proved in §1.4.1].
* `Turing.timed_universal` — the time-bounded universal machine [AB09, §1.4.1].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9, pp. 20-21; Figure 1.6.)
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
-/

open FinTM

/-- Doubling the code and appending its delimiter has suffix-independent length. -/
private lemma universal_pair_length (α x : List Bool) :
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
private def universalCanonTM (c : EffectiveMachineCode) : FinTM Bool :=
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
private lemma universalCanon_complete (c : EffectiveMachineCode) (α x : List Bool) :
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
private def universalInputPos (α x : List Bool) (p : Fin (x.length + 2)) :
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
private lemma universalInput_read {k : ℕ} {S : Type} (α : List Bool) {x : List Bool}
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
private lemma universalInput_move {k : ℕ} {S : Type} (α : List Bool) {x : List Bool}
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
private def universalCaptureTM {S : Type} [Fintype S] [DecidableEq S]
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
private def universalCaptureCfg {S : Type} [Fintype S] [DecidableEq S]
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
private def universalCapturedCfg {S : Type} [Fintype S] [DecidableEq S]
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
private lemma universalCapture_start {S : Type} [Fintype S] [DecidableEq S]
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


/-! ### The table interpreter

The four interpreter tapes are: canonical table, unary state, simulated work,
and the virtual-left-boundary marker. The state tape has a permanent `false` at
zero and the state index in unary `true`s starting at one. Each table search
consumes these unary symbols while skipping nine records per symbol. The next
state is copied from the selected record, so no code-dependent state index is
stored in finite control.
-/

/-- Finite registers and phases of the interpreter. All counters here have fixed
bounds; the unbounded simulated state is represented only on the state tape. -/
private inductive UniversalControl where
  | start
  | rewindTable (initial : Bool) (index : Fin 9)
  | countFirst (initial : Bool) (index : Fin 9)
  | countSecond (initial : Bool) (index : Fin 9) (bit : Bool)
  | initialCopy
  | initialSkip (index : Fin 9)
  | rewindState (index : Option (Fin 9))
  | main
  | group (index : Fin 9)
  | skipFixed (dest : Option (Fin 9)) (remaining : Fin 9) (field : Fin 8)
  | skipUnary (dest : Option (Fin 9)) (remaining : Fin 9)
  | readAction (field : Fin 8) (bits : Fin 8 → Bool)
  | nextState (bits : Fin 8 → Bool)
  | copyState (bits : Fin 8 → Bool)
  | rewindNext (bits : Fin 8 → Bool)
  | applyRecord (bits : Fin 8 → Bool) (halt : Bool)
  | invalid
  deriving DecidableEq, Fintype

/-- Four named tape entries, without a variable-size register. -/
private def universalFour {A : Type} (a b c d : A) : Fin 4 → A :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d

/-- A stationary administrative action, with explicit table and state-tape work. -/
private def universalAdmin (q : UniversalControl) (table : SignType := 0)
    (state : Option (Option Bool) × SignType := (none, 0)) :
    Action 4 Bool UniversalControl :=
  ⟨0, universalFour (none, table) state (none, 0) (none, 0), none, some q⟩

/-- The three read symbols in the fixed serialization order. -/
private def universalReadIndex : Option Bool → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

/-- The record within one nine-record state block. -/
private def universalRecordIndex (inp work : Option Bool) : Fin 9 :=
  ⟨3 * (universalReadIndex inp).val + (universalReadIndex work).val,
    by have hi := (universalReadIndex inp).isLt
       have hw := (universalReadIndex work).isLt
       omega⟩

/-- Decode a valid fixed two-bit head-movement field. -/
private def universalSign (a b : Bool) : SignType :=
  if a then if b then .neg else .pos else .zero

/-- Decode a valid fixed two-bit optional-write field. -/
private def universalWrite (a b : Bool) : Option (Option Bool) :=
  if a then some (some b) else if b then some none else none

/-- The four-tape table interpreter, with a finite control independent of the
number of coded states. Malformed administrative reads enter a live sink;
canonical-table correspondence excludes them on the inputs used by the theorem. -/
private def universalInterpreter : MultiTapeTM 4 Bool UniversalControl where
  q₀ := .start
  tr := fun q inp work => match q with
    | .start =>
        ⟨0, universalFour (none, .neg) (some (some false), .pos) (none, 0)
          (some (some true), .pos), none, some (.rewindTable true 0)⟩
    | .rewindTable initial index =>
        if work 0 = none then universalAdmin (.countFirst initial index) .pos
        else universalAdmin (.rewindTable initial index) .neg
    | .countFirst initial index => match work 0 with
        | some b => universalAdmin (.countSecond initial index b) .pos
        | none => universalAdmin .invalid
    | .countSecond initial index b => match work 0 with
        | some v =>
          if b = v then universalAdmin (.countFirst initial index) .pos
          else if b = false ∧ v = true then
            universalAdmin (if initial then .initialCopy else .initialSkip index) .pos
          else universalAdmin .invalid
        | none => universalAdmin .invalid
    | .initialCopy => match work 0 with
        | some true => universalAdmin .initialCopy .pos (some (some true), .pos)
        | some false => universalAdmin (.rewindState none) .pos
        | none => universalAdmin .invalid
    | .initialSkip index => match work 0 with
        | some true => universalAdmin (.initialSkip index) .pos
        | some false => universalAdmin (.group index) .pos
        | none => universalAdmin .invalid
    | .rewindState index =>
        if work 1 = some false then
          let next := match index with
            | none => UniversalControl.main
            | some i => if h : i.val = 0 then .readAction 0 (fun _ => false)
                else .skipFixed none ⟨i.val - 1, by omega⟩ 0
          universalAdmin next 0 (none, .pos)
        else universalAdmin (.rewindState index) 0 (none, .neg)
    | .main =>
        let v := if work 3 = some true then none else inp
        universalAdmin (.rewindTable false (universalRecordIndex v (work 2))) .neg
    | .group index => match work 1 with
        | some true => universalAdmin (.skipFixed (some index) 8 0) 0 (some none, .pos)
        | none => universalAdmin (.rewindState (some index))
        | some false => universalAdmin .invalid
    | .skipFixed dest remaining field =>
        if h : field.val = 7 then universalAdmin (.skipUnary dest remaining) .pos
        else universalAdmin (.skipFixed dest remaining ⟨field.val + 1, by omega⟩) .pos
    | .skipUnary dest remaining => match work 0 with
        | some true => universalAdmin (.skipUnary dest remaining) .pos
        | some false =>
          if h : remaining.val = 0 then
            universalAdmin (match dest with
              | none => .readAction 0 (fun _ => false)
              | some i => .group i) .pos
          else universalAdmin (.skipFixed dest ⟨remaining.val - 1, by omega⟩ 0) .pos
        | none => universalAdmin .invalid
    | .readAction field bits => match work 0 with
        | some b =>
          let bs := Function.update bits field b
          if h : field.val = 7 then universalAdmin (.nextState bs) .pos
          else universalAdmin (.readAction ⟨field.val + 1, by omega⟩ bs) .pos
        | none => universalAdmin .invalid
    | .nextState bits => match work 0 with
        | some false => universalAdmin (.applyRecord bits true)
        | some true => universalAdmin (.copyState bits) .pos
        | none => universalAdmin .invalid
    | .copyState bits => match work 0 with
        | some true => universalAdmin (.copyState bits) .pos (some (some true), .pos)
        | some false => universalAdmin (.rewindNext bits)
        | none => universalAdmin .invalid
    | .rewindNext bits =>
        if work 1 = some false then universalAdmin (.applyRecord bits false) 0 (none, .pos)
        else universalAdmin (.rewindNext bits) 0 (none, .neg)
    | .applyRecord bits halt =>
        let v := if work 3 = some true then none else inp
        let d := virtualMove (decide (work 3 ≠ some true)) v (universalSign (bits 0) (bits 1))
        ⟨d, universalFour (none, 0) (none, 0)
          (universalWrite (bits 2) (bits 3), universalSign (bits 4) (bits 5)) (none, d),
          if bits 6 then some (bits 7) else none, if halt then none else some .main⟩
    | .invalid => universalAdmin .invalid

/-- State-tape representation: a permanent origin marker and a unary index. -/
private def universalStateTape (q : ℕ) : ℤ → Option Bool :=
  bufferTape (false :: List.replicate q true)

/-- The complete universal machine candidate: prefix extraction and virtual
canonization, captured table, then the fixed finite table interpreter. -/
private def universalTM (c : EffectiveMachineCode) : FinTM Bool :=
  universalCaptureTM (universalCanonTM c) universalInterpreter


/-- Administrative configuration with arbitrary inactive physical input, simulated
work, boundary marker, and accumulated output. Only table/state cursors vary. -/
private def universalEvalCfg {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) : Cfg 4 Bool UniversalControl x :=
  { base with
    state := some q
    workTapes := universalFour (bufferTape table) state (base.workTapes 2) (base.workTapes 3)
    workTapePos := universalFour tp sp (base.workTapePos 2) (base.workTapePos 3) }

/-- The four administrative reads. -/
private lemma universalEval_reads {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) :
    (universalEvalCfg base q table tp state sp).workTapeSymbols =
      universalFour (bufferTape table tp) (state sp)
        (base.workTapeSymbols 2) (base.workTapeSymbols 3) := by
  funext i
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- One administrative action changes only the two designated tape cursors and
optionally the state-tape cell. -/
private lemma universalAdmin_apply {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q q' : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) (dt ds : SignType) (w : Option (Option Bool)) :
    (universalAdmin q' dt (w, ds)).apply (universalEvalCfg base q table tp state sp) =
      universalEvalCfg base q' table (tp + (dt : ℤ))
        (match w with | none => state | some b => Function.update state sp b)
        (sp + (ds : ℤ)) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (List.append_nil _)
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> cases w <;> rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;>
      first | rfl | exact add_zero _

/-- Read-based administrative step rule. -/
private lemma universalEval_step {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q q' : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) (dt ds : SignType) (w : Option (Option Bool))
    (h : universalInterpreter.tr q base.inputSymbol
      (universalFour (bufferTape table tp) (state sp)
        (base.workTapeSymbols 2) (base.workTapeSymbols 3)) = universalAdmin q' dt (w, ds)) :
    universalInterpreter.step (universalEvalCfg base q table tp state sp) =
      universalEvalCfg base q' table (tp + (dt : ℤ))
        (match w with | none => state | some b => Function.update state sp b)
        (sp + (ds : ℤ)) := by
  change (universalInterpreter.tr q _ _).apply _ = _
  rw [universalEval_reads]
  change (universalInterpreter.tr q base.inputSymbol _).apply _ = _
  conv_lhs => rw [h]
  cases w <;> exact universalAdmin_apply base q q' table tp state sp dt ds _

/-- Look up the first unconsumed cell of a contiguous table. -/
private lemma universal_table_read (l r : List Bool) (b : Bool) :
    bufferTape (l ++ b :: r) (l.length : ℤ) = some b := by
  rw [bufferTape_nat, List.getElem?_append_right (le_refl _)]
  simp

/-- Exact-cost table rewind. The initial unconditional left move has put the
cursor at `j-1`, where `j` is at most the table length.

**Proof sketch.** At `j=0`, the cursor is the left blank and one move right
starts the count parser. At positive `j`, a nonblank table cell is read and the
cursor decreases once. Induction accounts for every transition and leaves all
other tapes, physical input, and accumulated output unchanged. -/
private lemma universal_table_rewind {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (initial : Bool) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ) :
    ∀ j, j ≤ table.length →
      universalInterpreter.runFrom
        (universalEvalCfg base (.rewindTable initial index) table (j - 1) state sp) (j + 1) =
      universalEvalCfg base (.countFirst initial index) table 0 state sp := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base (.rewindTable initial index) (.countFirst initial index)
      table (-1) state sp .pos 0 none (by simp [universalInterpreter, universalFour])
    simpa using he
  | succ j ih =>
    intro hj
    have hr : bufferTape table (j : ℤ) = some table[j] := by
      rw [bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have he := universalEval_step base (.rewindTable initial index) (.rewindTable initial index)
      table (j : ℤ) state sp .neg 0 none (by simp [universalInterpreter, universalFour, hr])
    have hh : (j + 1 : ℤ) - 1 = j := by omega
    simp only [Nat.cast_add, Nat.cast_one, hh]
    rw [he]
    simpa using ih (by omega)

/-- Skip an arbitrary doubled, delimited count field at exact cost. No binary
arithmetic on its value is needed by the interpreter.

**Proof sketch.** Each doubled pair returns the parser to its first-half state
in two transitions. The terminal aligned `false,true` pair selects the initial
state copier or skipper. Induct on the count-bit list while growing the consumed
prefix, so table lookup is justified at every cursor position. -/
private lemma universal_count_run {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (initial : Bool) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (bits : List Bool) (l r : List Bool)
    (ht : table = l ++ (bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.countFirst initial index) table l.length state sp)
      (2 * bits.length + 2) =
    universalEvalCfg base (if initial then .initialCopy else .initialSkip index) table
      (l.length + 2 * bits.length + 2) state sp := by
  induction bits generalizing l with
  | nil =>
    have hr0 : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using universal_table_read l (true :: r) false
    have hr1 : bufferTape table (l.length + 1 : ℤ) = some true := by
      have h' : table = (l ++ [false]) ++ true :: r := by simp [ht, List.append_assoc]
      have h := universal_table_read (l ++ [false]) r true
      simpa [h', List.length_append] using h
    have he0 := universalEval_step base (.countFirst initial index)
      (.countSecond initial index false) table l.length state sp .pos 0 none
      (by simp [universalInterpreter, universalFour, hr0])
    have he1 := universalEval_step base (.countSecond initial index false)
      (if initial then .initialCopy else .initialSkip index)
      table (l.length + 1) state sp .pos 0 none
      (by simp [universalInterpreter, universalFour, hr1])
    change universalInterpreter.runFrom _ (0 + 1 + 1) = _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, he0]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [he1]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero,
      List.length_nil, Nat.cast_zero, mul_zero]
    congr 1
  | cons b bits ih =>
    have hr0 : bufferTape table (l.length : ℤ) = some b := by
      rw [ht]
      simpa [List.flatMap_cons, List.append_assoc] using
        universal_table_read l (b :: ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r)) b
    have hr1 : bufferTape table (l.length + 1 : ℤ) = some b := by
      have h' : table = (l ++ [b]) ++ b :: ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) := by
        simp [ht, List.append_assoc]
      have h := universal_table_read (l ++ [b]) ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) b
      simpa [h', List.length_append] using h
    have he0 := universalEval_step base (.countFirst initial index)
      (.countSecond initial index b) table l.length state sp .pos 0 none
      (by simp [universalInterpreter, universalFour, hr0])
    have he1 := universalEval_step base (.countSecond initial index b)
      (.countFirst initial index) table (l.length + 1) state sp .pos 0 none
      (by simp [universalInterpreter, universalFour, hr1])
    have h' : table = (l ++ [b, b]) ++ (bits.flatMap fun b => [b, b]) ++ [false, true] ++ r := by
      simp [ht, List.append_assoc]
    have hi := ih (l ++ [b, b]) h'
    conv_lhs => rw [show 2 * (b :: bits).length + 2 =
      1 + 1 + (2 * bits.length + 2) by simp; omega]
    rw [MultiTapeTM.runFrom_add]
    change universalInterpreter.runFrom
      (universalInterpreter.step (universalInterpreter.step _)) _ = _
    rw [he0]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [he1]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert hi using 1 <;> simp [List.length_append, List.length_cons] <;> congr 1 <;> omega


/-- State representation during destructive lookup: the first `consumed` unary
cells have been erased; `remaining` ones follow them. The origin marker persists. -/
private def universalStateWindow (consumed remaining : ℕ) (z : ℤ) : Option Bool :=
  if z = 0 then some false
  else if (consumed : ℤ) < z ∧ z ≤ consumed + remaining then some true else none

/-- The intact state window is exactly the unary state-tape representation. -/
private lemma universalStateWindow_zero (n : ℕ) :
    universalStateWindow 0 n = universalStateTape n := by
  funext z
  by_cases h0 : z = 0
  · subst z; simp [universalStateWindow, universalStateTape, bufferTape]
  · by_cases hz : 0 ≤ z
    · have hp : 0 < z := by omega
      have he : z.toNat = (z.toNat - 1) + 1 := by omega
      simp only [universalStateWindow, if_neg h0, Nat.cast_zero, zero_add,
        universalStateTape, bufferTape, if_pos hz]
      rw [he, List.getElem?_cons_succ]
      by_cases h : z ≤ n
      · rw [if_pos (by omega), List.getElem?_replicate_of_lt (by omega)]
      · rw [if_neg (by omega), List.getElem?_eq_none (by simp; omega)]
    · simp [universalStateWindow, universalStateTape, bufferTape, h0, hz]
      omega

/-- At the current state cursor, a nonempty window reads one. -/
private lemma universalStateWindow_read (j n : ℕ) :
    universalStateWindow j (n + 1) (j + 1) = some true := by
  simp [universalStateWindow]
  omega

/-- The cursor following the erased state reads blank. -/
private lemma universalStateWindow_end (j : ℕ) :
    universalStateWindow j 0 (j + 1) = none := by
  simp [universalStateWindow]
  omega

/-- Erasing one unary symbol advances the consumed prefix exactly once. -/
private lemma universalStateWindow_erase (j n : ℕ) :
    Function.update (universalStateWindow j (n + 1)) (j + 1 : ℤ) none =
      universalStateWindow (j + 1) n := by
  funext z
  by_cases he : z = j + 1
  · subst z
    simp [universalStateWindow]
    omega
  · rw [Function.update_of_ne he]
    unfold universalStateWindow
    by_cases h0 : z = 0
    · simp [h0]
    · rw [if_neg h0, if_neg h0]
      simp only [Nat.cast_add, Nat.cast_one]
      split <;> split <;> first | rfl | omega

/-- A fully consumed window contains only the permanent marker, regardless of
how many symbols were erased. -/
private lemma universalStateWindow_empty (j : ℕ) :
    universalStateWindow j 0 = universalStateWindow 0 0 := by
  funext z
  simp only [universalStateWindow, Nat.cast_zero, add_zero, zero_add]
  have h₁ : ¬((j : ℤ) < z ∧ z ≤ j) := by omega
  have h₂ : ¬(0 < z ∧ z ≤ 0) := by omega
  simp [h₁, h₂]

/-- Appending a next-state unary symbol extends the intact state tape. -/
private lemma universalStateTape_append (n : ℕ) :
    Function.update (universalStateTape n) (n + 1 : ℤ) (some true) =
      universalStateTape (n + 1) := by
  have h := bufferTape_append (false :: List.replicate n true) true
  simpa only [universalStateTape, List.replicate_add, List.replicate_one,
    List.cons_append, List.length_cons, List.length_replicate,
    Nat.cast_add, Nat.cast_one] using h.symm

/-- An intact unary state reads its blank immediately after the last symbol. -/
private lemma universalStateTape_end (n : ℕ) :
    universalStateTape n (n + 1) = none := by
  simp [universalStateTape, bufferTape]

/-- A marker-directed state rewind has exact cost equal to cursor plus one.
Its premise is deliberately independent of whether traversed cells are erased
blanks or retained unary ones.

**Proof sketch.** Each positive cursor sees a non-marker cell and moves left.
At zero the permanent marker causes one right move and transfer to the supplied
continuation. The entire tape, input head, and real output stay unchanged. -/
private lemma universal_state_rewind {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (q q' : UniversalControl)
    (table : List Bool) (tp : ℤ) (state : ℤ → Option Bool)
    (hzero : state 0 = some false)
    (hother : ∀ j : ℕ, 0 < j → state j ≠ some false)
    (hstop : ∀ inp work, work 1 = some false →
      universalInterpreter.tr q inp work = universalAdmin q' 0 (none, .pos))
    (hscan : ∀ inp work, work 1 ≠ some false →
      universalInterpreter.tr q inp work = universalAdmin q 0 (none, .neg)) :
    ∀ j : ℕ, universalInterpreter.runFrom
      (universalEvalCfg base q table tp state j) (j + 1) =
      universalEvalCfg base q' table tp state 1 := by
  intro j
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base q q' table tp state 0 0 .pos none
      (hstop _ _ (by simpa [universalFour] using hzero))
    simpa using he
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have he := universalEval_step base q q table tp state (j + 1) 0 .neg none
      (hscan _ _ (by simpa [universalFour] using hother (j + 1) (by omega)))
    rw [show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by omega, he]
    simpa using ih

/-- The table's initial-state unary field can be skipped at exact cost. -/
private lemma universal_initial_skip {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (n : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.initialSkip index) table l.length state sp) (n + 1) =
      universalEvalCfg base (.group index) table (l.length + n + 1) state sp := by
  induction n generalizing l with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using universal_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base (.initialSkip index) (.group index)
      table l.length state sp .pos 0 none (by simp [universalInterpreter, universalFour, hr])
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        universal_table_read l (List.replicate n true ++ false :: r) true
    have he := universalEval_step base (.initialSkip index) (.initialSkip index)
      table l.length state sp .pos 0 none (by simp [universalInterpreter, universalFour, hr])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    have hi := ih (l ++ [true]) ht'
    convert hi using 1 <;> simp [List.length_append, List.length_cons] <;> congr 1 <;> omega



/-- Copy a unary table field onto the state tape. This single gadget serves both
initial-state extraction and live successor-state replacement.

**Proof sketch.** A `true` table cell appends one unary state symbol and moves both
cursors right. A terminal `false` switches to the supplied continuation, with its
specified table movement. Induction preserves exact table/state positions and
accounts for all `n+1` transitions. -/
private lemma universal_unary_copy {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (q q' : UniversalControl) (doneMove : SignType)
    (table : List Bool)
    (htrue : ∀ inp work, work 0 = some true →
      universalInterpreter.tr q inp work = universalAdmin q .pos (some (some true), .pos))
    (hfalse : ∀ inp work, work 0 = some false →
      universalInterpreter.tr q inp work = universalAdmin q' doneMove (none, 0))
    (n j : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    universalInterpreter.runFrom
      (universalEvalCfg base q table l.length (universalStateTape j) (j + 1)) (n + 1) =
      universalEvalCfg base q' table (l.length + n + (doneMove : ℤ))
        (universalStateTape (j + n)) (j + n + 1) := by
  induction n generalizing l j with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using universal_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base q q' table l.length (universalStateTape j) (j + 1)
      doneMove 0 none (hfalse _ _ (by simp [universalFour, hr]))
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        universal_table_read l (List.replicate n true ++ false :: r) true
    have he := universalEval_step base q q table l.length (universalStateTape j) (j + 1)
      .pos .pos (some (some true)) (htrue _ _ (by simp [universalFour, hr]))
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, universalStateTape_append]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    have hi := ih (j + 1) (l ++ [true]) ht'
    convert hi using 1 <;> simp [List.length_append, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 n, Int.add_assoc] <;> congr 1 <;> omega

/-- The initial state tape has a unique `false` marker at zero. -/
private lemma universalStateTape_marker (n : ℕ) :
    universalStateTape n 0 = some false ∧
      ∀ j : ℕ, 0 < j → universalStateTape n j ≠ some false := by
  rw [← universalStateWindow_zero]
  constructor
  · simp [universalStateWindow]
  · intro j hj
    simp only [universalStateWindow, Nat.cast_zero, zero_add]
    rw [if_neg (by omega)]
    split <;> simp

/-- Installing a single permanent marker in an otherwise blank tape. -/
private lemma universal_install_marker (b : Bool) :
    Function.update (fun _ : ℤ => none) 0 (some b) = bufferTape [b] := by
  simpa using (bufferTape_append [] b).symm

/-- Interpreter entry with the captured table on its right blank and three
fresh auxiliary tapes. Physical input is already parked at the suffix start. -/
private def universalInterpreterInitial {x : List Bool} (p : Fin (x.length + 2))
    (table : List Bool) : Cfg 4 Bool UniversalControl x :=
  ⟨some .start, p, universalFour (bufferTape table) (fun _ => none) (fun _ => none)
      (fun _ => none), universalFour table.length 0 0 0, []⟩

/-- Inactive data during interpreter initialization: physical input is stationary,
simulated work is blank, and the virtual-left marker is installed at zero with
its head at one (also for empty suffixes). -/
private def universalInterpreterBase {x : List Bool} (p : Fin (x.length + 2)) :
    Cfg 4 Bool UniversalControl x :=
  ⟨some .main, p, universalFour (fun _ => none) (fun _ => none) (fun _ => none)
      (bufferTape [true]), universalFour 0 0 0 1, []⟩

/-- The first interpreter step installs the permanent markers and starts the
unconditional table rewind. -/
private lemma universalInterpreter_first {x : List Bool} (p : Fin (x.length + 2))
    (table : List Bool) :
    universalInterpreter.step (universalInterpreterInitial p table) =
      universalEvalCfg (universalInterpreterBase p) (.rewindTable true 0) table
        (table.length - 1) (universalStateTape 0) 1 := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · rfl
    · exact universal_install_marker false
    · rfl
    · exact universal_install_marker true
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- The transition-record grammar exposed locally for interpreter proofs. This
is definitionally the serialization field dictionary from `Encoding.lean`. -/
private def universalRecordBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) : List Bool :=
  (match a.inputTape with
    | .neg => [true, true] | .zero => [false, false] | .pos => [true, false]) ++
  (match (a.workTapes 0).1 with
    | none => [false, false] | some none => [false, true]
    | some (some false) => [true, false] | some (some true) => [true, true]) ++
  (match (a.workTapes 0).2 with
    | .neg => [true, true] | .zero => [false, false] | .pos => [true, false]) ++
  (match a.output with
    | none => [false, false] | some false => [true, false] | some true => [true, true]) ++
  (match a.state with
    | none => [false] | some q => true :: (List.replicate q.val true ++ [false]))

/-- Canonical record order, including all nine read pairs at every live state. -/
private def universalRecords (M : CodeTM) : List Bool :=
  (List.finRange (M.numStates + 1)).flatMap fun q =>
    ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun work =>
        universalRecordBits (M.tm.tr q inp (fun _ => work))

/-- The canonical serialization begins with exactly its count field and initial
unary state; the remainder is the transition table. -/
private lemma universal_serialization_header (M : CodeTM) :
    ∃ records, M.serialize =
      pairEncode (Nat.bits M.numStates) (List.replicate M.tm.q₀.val true ++ false :: records) := by
  refine ⟨universalRecords M, ?_⟩
  unfold CodeTM.serialize
  change pairEncode _ ((List.replicate M.tm.q₀.val true ++ [false]) ++ _) = _
  rw [List.append_assoc]
  apply congrArg (pairEncode (Nat.bits M.numStates))
  apply congrArg (fun r : List Bool => List.replicate M.tm.q₀.val true ++ false :: r)
  unfold universalRecords
  dsimp only [List.append]
  congr 1
  funext q
  congr 1
  funext inp
  congr 1
  funext work
  generalize M.tm.tr q inp (fun _ => work) = a
  rcases a with ⟨di, tapes, out, next⟩
  have htapes : tapes = fun _ => tapes 0 := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    rw [hi]
  rw [htapes]
  generalize tapes 0 = entry
  rcases entry with ⟨write, dm⟩
  cases di <;> cases dm <;> rcases write with _ | (_ | (_ | _)) <;>
    rcases out with _ | (_ | _) <;> cases next <;> rfl

/-- Exact interpreter initialization for a canonical count/initial-state prefix.
No transition-table lookup is involved yet.

**Proof sketch.** Install both markers (one transition), rewind the whole captured
table (`|table|+1`), skip the doubled count (`2|bits|+2`), copy the initial unary
state (`n+1`), and rewind its cursor (`n+2`). The sum is
`|table| + 2|bits| + 2n + 7`. Every intermediate configuration keeps the physical
input fixed and real output empty. -/
private lemma universalInterpreter_initialize {x : List Bool}
    (p : Fin (x.length + 2)) (table bits records : List Bool) (n : ℕ)
    (ht : table = pairEncode bits (List.replicate n true ++ false :: records)) :
    universalInterpreter.runFrom (universalInterpreterInitial p table)
      (table.length + 2 * bits.length + 2 * n + 7) =
    universalEvalCfg (universalInterpreterBase p) .main table
      (2 * bits.length + 2 + n + 1) (universalStateTape n) 1 := by
  let base := universalInterpreterBase p
  have hrew := universal_table_rewind base true 0 table (universalStateTape 0) 1
    table.length (le_refl _)
  have hcount := universal_count_run base true 0 table (universalStateTape 0) 1
    bits [] (List.replicate n true ++ false :: records) (by simpa [pairEncode] using ht)
  let countPrefix := (bits.flatMap fun b => [b, b]) ++ [false, true]
  have hlen : countPrefix.length = 2 * bits.length + 2 := by
    simpa [countPrefix, pairEncode] using universal_pair_length bits []
  have hcopy := universal_unary_copy base .initialCopy (.rewindState none) .pos table
    (by intro inp work h; simp [universalInterpreter, h])
    (by intro inp work h; simp [universalInterpreter, h]) n 0 countPrefix records
    (by simpa [countPrefix, pairEncode, List.append_assoc] using ht)
  have hstate := universal_state_rewind base (.rewindState none) .main table
    (2 * bits.length + 2 + n + 1) (universalStateTape n)
    (universalStateTape_marker n).1 (universalStateTape_marker n).2
    (by intro inp work h; simp [universalInterpreter, h])
    (by intro inp work h; simp [universalInterpreter, h]) (n + 1)
  have htime : table.length + 2 * bits.length + 2 * n + 7 =
      1 + (table.length + 1) + (2 * bits.length + 2) + (n + 1) + (n + 2) := by omega
  rw [htime,
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1) + (2 * bits.length + 2) + (n + 1)) (n + 2),
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1) + (2 * bits.length + 2)) (n + 1),
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1)) (2 * bits.length + 2),
    MultiTapeTM.runFrom_add _ 1 (table.length + 1)]
  change universalInterpreter.runFrom
    (universalInterpreter.runFrom
      (universalInterpreter.runFrom
        (universalInterpreter.runFrom
          (universalInterpreter.step (universalInterpreterInitial p table))
          (table.length + 1)) (2 * bits.length + 2)) (n + 1)) (n + 2) = _
  rw [universalInterpreter_first, hrew]
  have hc : universalInterpreter.runFrom
      (universalEvalCfg base (.countFirst true 0) table 0 (universalStateTape 0) 1)
      (2 * bits.length + 2) =
    universalEvalCfg base .initialCopy table (2 * bits.length + 2) (universalStateTape 0) 1 := by
    simpa using hcount
  rw [hc]
  have hp : universalInterpreter.runFrom
      (universalEvalCfg base .initialCopy table (2 * bits.length + 2) (universalStateTape 0) 1)
      (n + 1) =
    universalEvalCfg base (.rewindState none) table (2 * bits.length + 2 + n + 1)
      (universalStateTape n) (n + 1) := by
    simpa [hlen] using hcopy
  rw [hp]
  simpa using hstate


/-- Source configurations represented at interpreter checkpoints. The table
cursor is the only administrative coordinate left unspecified by the source. -/
private def universalSimulationCfg (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (tablePos : ℕ) :
    Cfg 4 Bool UniversalControl (pairEncode α x) :=
  ⟨src.state.map (fun _ => .main), universalInputPos α x src.inputPos,
    universalFour (bufferTape M.serialize)
      (universalStateTape ((src.state.map Fin.val).getD 0)) (src.workTapes 0)
      (bufferTape [true]), universalFour tablePos 1 (src.workTapePos 0) src.inputPos.val,
    src.output⟩

/-- Checkpoint representations preserve completed-output and halting fields. -/
private lemma universalSimulation_fields (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (tablePos : ℕ) :
    ((universalSimulationCfg M α src tablePos).state = none ↔ src.state = none) ∧
      (universalSimulationCfg M α src tablePos).output = src.output := by
  simp [universalSimulationCfg]

/-- The capture-stage endpoint is precisely a right-block interpreter entry,
with the canonizer work tapes retained as inactive data. -/
private lemma universalCaptured_right {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) {x : List Bool}
    (src : Cfg M.k Bool M.State x) :
    universalCapturedCfg M D src =
    rightCfg Sum.inr
      (⟨some D.q₀, src.inputPos,
        universalFour (bufferTape src.output) (fun _ => none) (fun _ => none) (fun _ => none),
        universalFour src.output.length 0 0 0, []⟩ : Cfg 4 Bool S x)
      src.workTapes src.workTapePos := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [universalCapturedCfg, universalCaptureCfg, rightCfg, tapeBlocks]
    · intro j
      rcases j with ⟨j, hj⟩
      have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;>
        simp [universalCapturedCfg, universalCaptureCfg, rightCfg, tapeBlocks, universalFour] <;> rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [universalCapturedCfg, universalCaptureCfg, rightCfg, tapeBlocks]
    · intro j
      rcases j with ⟨j, hj⟩
      have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;>
        simp [universalCapturedCfg, universalCaptureCfg, rightCfg, tapeBlocks, universalFour] <;> rfl

/-- Every interpreter run lifts to the complete capture machine without touching
its inactive prefix/canonizer work tapes. -/
private lemma universalCapture_interpreter_run (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg 4 Bool UniversalControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) (t : ℕ) :
    (universalCaptureTM M universalInterpreter).tm.runFrom
      (rightCfg Sum.inr cfg tapes heads) t =
    rightCfg Sum.inr (universalInterpreter.runFrom cfg t) tapes heads :=
  rightCfg_run universalInterpreter (universalCaptureTM M universalInterpreter).tm
    Sum.inr (by intros; rfl) cfg tapes heads t

/-- The code-dependent startup bound, including complete interpreter setup. -/
private def universalStartupBound (c : EffectiveMachineCode) (α : List Bool) : ℕ :=
  3 * α.length + c.canonizerTime α.length + (c.decode α).serialize.length +
    2 * (Nat.bits (c.decode α).numStates).length + 2 * (c.decode α).tm.q₀.val + 12

/-- Full prefix-start correspondence: the complete candidate reaches the first
source checkpoint, with the canonical table, unary initial state, blank simulated
work tape, and virtual input marker, within a bound independent of the suffix.

**Proof sketch.** First capture the virtually run canonizer, preserving its exact
parked physical head. Identify this endpoint with a right-block interpreter entry,
then lift the exact interpreter-initialization run. The initial marker head at one
matches the native initial input position, also on empty input. No step of startup
needs the suffix length or a suffix read. -/
private lemma universal_initialized (c : EffectiveMachineCode) (α x : List Bool) :
    ∃ (t : ℕ) (tapes : Fin (universalCanonTM c).k → ℤ → Option Bool)
      (heads : Fin (universalCanonTM c).k → ℤ),
      t ≤ universalStartupBound c α ∧
      (universalTM c).tm.runFrom ((universalTM c).tm.initCfg (pairEncode α x)) t =
        rightCfg Sum.inr
          (universalSimulationCfg (c.decode α) α ((c.decode α).tm.initCfg x)
            (2 * (Nat.bits (c.decode α).numStates).length + 2 + (c.decode α).tm.q₀.val + 1))
          tapes heads := by
  let T := 3 * α.length + 4 + c.canonizerTime α.length
  let src := (universalCanonTM c).tm.runFrom
    ((universalCanonTM c).tm.initCfg (pairEncode α x)) T
  have hc := universalCanon_complete c α x
  obtain ⟨t, ht, he⟩ := universalCapture_start (universalCanonTM c) universalInterpreter
    (pairEncode α x) T hc.1
  obtain ⟨records, hrecords⟩ := universal_serialization_header (c.decode α)
  have hinit := universalInterpreter_initialize src.inputPos (c.decode α).serialize
    (Nat.bits (c.decode α).numStates) records (c.decode α).tm.q₀.val hrecords
  let d := (c.decode α).serialize.length + 2 * (Nat.bits (c.decode α).numStates).length +
    2 * (c.decode α).tm.q₀.val + 7
  refine ⟨t + d, src.workTapes, src.workTapePos, ?_, ?_⟩
  · dsimp only [universalStartupBound, d, T] at *
    omega
  · change (universalCaptureTM (universalCanonTM c) universalInterpreter).tm.runFrom _ _ = _
    rw [MultiTapeTM.runFrom_add, he, universalCaptured_right]
    change (universalCaptureTM (universalCanonTM c) universalInterpreter).tm.runFrom
      (rightCfg Sum.inr (universalInterpreterInitial src.inputPos src.output)
        src.workTapes src.workTapePos) d = _
    have ho : src.output = (c.decode α).serialize := hc.2.1
    rw [ho, universalCapture_interpreter_run, hinit]
    congr 1
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      exact hc.2.2
    · funext i
      rcases i with ⟨i, hi⟩
      have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    · funext i
      rcases i with ⟨i, hi⟩
      have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;> simp [universalEvalCfg,
        universalInterpreterBase, universalSimulationCfg, universalFour, Nat.cast_add]
    · rfl

/-- A block simulation with positive block lengths gives a cofinal physical run.
The upper bound accounts for startup and each source transition; the lower bound
is what makes the completed-output converse independent of administrative phases.

**Proof sketch.** Induct on source time. Startup supplies the initial related
configuration. Append the positive-duration block for each source transition and
use run addition to concatenate it. Add the upper bounds and use positivity for
the lower bound, without assuming that source or target eventually halts. -/
private lemma universal_block_run {k l : ℕ} {Q R : Type} {x y : List Bool}
    (M : MultiTapeTM k Bool Q) (U : MultiTapeTM l Bool R)
    (relation : Cfg k Bool Q x → Cfg l Bool R y → Prop) (S B : ℕ)
    (hstart : ∃ t, t ≤ S ∧ relation (M.initCfg x) (U.runFrom (U.initCfg y) t))
    (hstep : ∀ src dst, relation src dst →
      ∃ d, 1 ≤ d ∧ d ≤ B ∧ relation (M.step src) (U.runFrom dst d)) :
    ∀ n, ∃ t, n ≤ t ∧ t ≤ S + B * n ∧
      relation (M.runFrom (M.initCfg x) n) (U.runFrom (U.initCfg y) t) := by
  intro n
  induction n with
  | zero =>
    obtain ⟨t, ht, hr⟩ := hstart
    exact ⟨t, Nat.zero_le _, by simpa using ht, hr⟩
  | succ n ih =>
    obtain ⟨t, hnt, ht, hr⟩ := ih
    obtain ⟨d, hd, hBd, hrel⟩ := hstep _ _ hr
    refine ⟨t + d, by omega, ?_, ?_⟩
    · rw [Nat.mul_succ]
      omega
    · rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add]
      exact hrel

/-- Assembly of both evaluator clauses from a configuration-level block
simulation. This lemma has no admitted premise: its simulation obligations are
explicit hypotheses that the concrete interpreter must discharge.

**Proof sketch.** In the forward direction, the cofinal block run gives a related
halted configuration by startup plus at most one block bound per source step;
`S+B` absorbs this into `(S+B)(t+1)`. For the converse, if the target has halted by
physical time `t`, take the related checkpoint after `t` source steps. Its physical
time is at least `t`, so absorbing halting preserves the completed output there.
The state/output correspondence then forces source halting with that same output.
This rules out target halting on every divergent source run, even if either run
has emitted a nonempty intermediate output. -/
private lemma universal_from_blocks (c : EffectiveMachineCode) (U : FinTM Bool)
    (S B : List Bool → ℕ)
    (relation : ∀ α x : List Bool,
      Cfg 1 Bool (Fin ((c.decode α).numStates + 1)) x →
      Cfg U.k Bool U.State (pairEncode α x) → Prop)
    (hstart : ∀ α x, ∃ t, t ≤ S α ∧
      relation α x ((c.decode α).tm.initCfg x)
        (U.tm.runFrom (U.tm.initCfg (pairEncode α x)) t))
    (hstep : ∀ α x src dst, relation α x src dst →
      ∃ d, 1 ≤ d ∧ d ≤ B α ∧
        relation α x ((c.decode α).tm.step src) (U.tm.runFrom dst d))
    (hhalt : ∀ α x src dst, relation α x src dst → (src.state = none ↔ dst.state = none))
    (hout : ∀ α x src dst, relation α x src dst → src.output = dst.output) :
    ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      (∀ output : List Bool,
        (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (c.decode α).toFinTM.ComputesInTime x output t) := by
  intro α
  refine ⟨S α + B α, fun x => ?_⟩
  have hrun := universal_block_run (c.decode α).tm U.tm (relation α x)
    (S α) (B α) (hstart α x) (hstep α x)
  constructor
  · intro output t hm
    obtain ⟨v, -, hv, hr⟩ := hrun t
    have hs := (computesInTime_iff _ _ _ _).mp hm
    have hu : U.ComputesInTime (pairEncode α x) output v :=
      (computesInTime_iff _ _ _ _).mpr
        ⟨(hhalt α x _ _ hr).mp hs.1, (hout α x _ _ hr).symm.trans hs.2⟩
    apply hu.mono
    calc
      v ≤ S α + B α * t := hv
      _ ≤ S α * (t + 1) + B α * (t + 1) := by
        apply Nat.add_le_add
        · simpa only [Nat.mul_one] using Nat.mul_le_mul_left (S α) (Nat.succ_pos t)
        · exact Nat.mul_le_mul_left (B α) (by omega)
      _ = (S α + B α) * (t + 1) := by ring
  · intro output ⟨t, hu⟩
    obtain ⟨v, htv, -, hr⟩ := hrun t
    have hs := (computesInTime_iff _ _ _ _).mp (hu.mono htv)
    refine ⟨t, (computesInTime_iff _ _ _ _).mpr ?_⟩
    exact ⟨(hhalt α x _ _ hr).mpr hs.1, (hout α x _ _ hr).trans hs.2⟩


/-- Code-dependent block budget for the concrete interpreter. The intended
ledger is recorded in the delivery report; its realization is the remaining
concrete-step obligation in `universal`. -/
private def universalBlockBound (c : EffectiveMachineCode) (α : List Bool) : ℕ :=
  3 * (c.decode α).serialize.length + 5 * ((c.decode α).numStates + 1) + 20

/-- Concrete checkpoint relation. The bound on the table cursor is needed for
a uniform rewind cost; inactive canonizer tapes remain existentially framed. -/
private def universalRelation (c : EffectiveMachineCode) (α x : List Bool)
    (src : Cfg 1 Bool (Fin ((c.decode α).numStates + 1)) x)
    (dst : Cfg (universalTM c).k Bool (universalTM c).State (pairEncode α x)) : Prop :=
  ∃ (p : ℕ) (tapes : Fin (universalCanonTM c).k → ℤ → Option Bool)
    (heads : Fin (universalCanonTM c).k → ℤ), p ≤ (c.decode α).serialize.length ∧
    dst = rightCfg Sum.inr (universalSimulationCfg (c.decode α) α src p) tapes heads

/-- The canonical header ends inside its table buffer. -/
private lemma universal_header_bound (M : CodeTM) :
    2 * (Nat.bits M.numStates).length + 2 + M.tm.q₀.val + 1 ≤ M.serialize.length := by
  obtain ⟨records, hr⟩ := universal_serialization_header M
  rw [hr, universal_pair_length]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- Full startup supplies the concrete checkpoint relation. -/
private lemma universalRelation_start (c : EffectiveMachineCode) (α x : List Bool) :
    ∃ t, t ≤ universalStartupBound c α ∧
      universalRelation c α x ((c.decode α).tm.initCfg x)
        ((universalTM c).tm.runFrom ((universalTM c).tm.initCfg (pairEncode α x)) t) := by
  obtain ⟨t, tapes, heads, ht, he⟩ := universal_initialized c α x
  exact ⟨t, ht, _, tapes, heads, universal_header_bound _, he⟩

/-- The concrete checkpoint relation preserves halting in both directions. -/
private lemma universalRelation_halt (c : EffectiveMachineCode) (α x : List Bool)
    (src : Cfg 1 Bool (Fin ((c.decode α).numStates + 1)) x)
    (dst : Cfg (universalTM c).k Bool (universalTM c).State (pairEncode α x))
    (h : universalRelation c α x src dst) : src.state = none ↔ dst.state = none := by
  obtain ⟨p, tapes, heads, -, rfl⟩ := h
  simp only [rightCfg, universalSimulationCfg, Option.map_eq_none_iff]

/-- The concrete checkpoint relation preserves the complete accumulated output. -/
private lemma universalRelation_output (c : EffectiveMachineCode) (α x : List Bool)
    (src : Cfg 1 Bool (Fin ((c.decode α).numStates + 1)) x)
    (dst : Cfg (universalTM c).k Bool (universalTM c).State (pairEncode α x))
    (h : universalRelation c α x src dst) : src.output = dst.output := by
  obtain ⟨p, tapes, heads, -, rfl⟩ := h
  rfl

/-- **The universal machine as an all-string evaluator** [AB09, Theorem 1.9]: for any
effective scheme there is a single machine `U` such that for every string `α` there
is a constant `C` (depending on `α`, absorbing its decoding) with, for every input
`x`: whenever the machine `α` denotes halts on `x` within `t` steps with `output`,
`U` on `pairEncode α x` halts with the same output within `C · (t + 1)` steps —
and conversely every *completed* output of `U` on `pairEncode α x` (its output on
halting) is a completed output of the denoted machine on `x`, so divergence is
preserved.

**Proof sketch** (after [AB09, Figure 1.6], adapted to the code-first layout).
Startup: `U` runs the scheme's `canonizer` on the doubled-bit `α`-region (via the
composition combinators), leaving the fixed serialization of `M := c.decode α` — the
state count, initial state, and table — on a *table* work tape, and writes the
initial state on a *state* tape; cost `O(canonizerTime |α| + |α| + 1)`, a constant
for fixed `α`, absorbed into `C`. `U`'s input head then parks at the start of the
verbatim `x` region, and a *work* tape mirrors `M`'s work tape. **The simulated
input's left boundary must be emulated explicitly** (round-2 audit, finding 3): the
cell physically left of the `x` region is the pairing delimiter's `true`, not a
blank, so `U` keeps a marker on a spare work tape whose head tracks the virtual
input position — at virtual position zero it supplies a blank read and suppresses
further outward moves (mirroring `moveInputPos`'s clamp), and for empty `x` the
virtual head starts at the right boundary blank adjacent to that marked left
boundary. Each simulated step: read the mirrored work symbol and the input symbol
under the simulated head (the input head moves one cell per simulated move — `x` is
verbatim, no doubling — with the boundary marker moved in lockstep), scan the table
for the record matching (state, input read, work read) — at most the table length,
constant in `t` — and apply it: update the state tape, write/move on the mirrored
tape, emit `M`'s emission verbatim. Forward bound: `C · (t + 1)`. Converse:
`U` emits only what the simulation emits and halts only when the simulation halts,
so any completed output of `U` is an output of `M` on `x`. -/
theorem universal (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      (∀ output : List Bool,
        (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (c.decode α).toFinTM.ComputesInTime x output t) := by
  refine ⟨universalTM c, ?_⟩
  apply universal_from_blocks c (universalTM c) (universalStartupBound c)
    (universalBlockBound c) (universalRelation c)
  · exact universalRelation_start c
  · intro α x src dst h
    by_cases hs : src.state = none
    · have hu := (universalRelation_halt c α x src dst h).mp hs
      refine ⟨1, le_refl _, ?_, ?_⟩
      · simp only [universalBlockBound]
        omega
      · rw [MultiTapeTM.step_of_halt hs, MultiTapeTM.runFrom_of_halt _ hu]
        exact h
    · -- Remaining obligation: execute one complete serialized-table lookup and
      -- application block for a live source, with positive duration and the
      -- code-dependent bound. Startup, boundary motion, and the two-clause
      -- assembly are proved above; this concrete block proof remains open.
      sorry
  · exact universalRelation_halt c
  · exact universalRelation_output c

/-- **The relaxed quadratic form, for total functions** [AB09, Theorem 1.9 as proved
in §1.4.1 — labeled per audit finding 4: this is the total-function corollary; the
machine-level, partial-computation statement is `Turing.universal`]: every binary
machine computing a total function `f` within `T` has a code `α` such that the
*same* universal machine computes `f x` from `pairEncode α x` within
`C · (T |x| + 1)²`.

**Proof sketch.** Normal-form the machine with `Turing.FinTM.one_work_tape_binary`
(quadratic, [AB09, Claims 1.5-1.6]), relabel its states with `Turing.exists_codeTM`,
take `α := c.encode` of that coded machine (so `c.decode α` is that machine, by
`MachineCode.decode_encode`), and apply the forward direction of `Turing.universal`;
the constants compose as `C_U · (c₁ · (T n + 1)² + 1) ≤ C · (T n + 1)²`. -/
theorem universal_quadratic (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (M₀ : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ),
      M₀.ComputesFunInTime f T →
      ∃ (α : List Bool) (C : ℕ), ∀ x : List Bool,
        U.ComputesInTime (pairEncode α x) (f x) (C * (T x.length + 1) ^ 2) := by
  obtain ⟨U, hU⟩ := universal c
  refine ⟨U, ?_⟩
  intro M₀ f T hM
  obtain ⟨M₁, c₁, hk, h₁⟩ := FinTM.one_work_tape_binary M₀ f T hM
  obtain ⟨N, hN⟩ := exists_codeTM M₁ hk
  let α := c.encode N
  obtain ⟨C_U, hCU⟩ := hU α
  refine ⟨α, C_U * (c₁ + 1), fun x => ?_⟩
  have hcoded : (c.decode α).toFinTM.ComputesInTime x (f x)
      (c₁ * (T x.length + 1) ^ 2) := by
    rw [show c.decode α = N from c.toMachineCode.decode_encode N]
    exact (hN x (f x) _).2 (h₁ x)
  apply ((hCU x).1 (f x) _ hcoded).mono
  have hpow : 0 < (T x.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  calc C_U * (c₁ * (T x.length + 1) ^ 2 + 1)
      ≤ C_U * (c₁ * (T x.length + 1) ^ 2 + (T x.length + 1) ^ 2) :=
        Nat.mul_le_mul (le_refl C_U) (Nat.add_le_add_left hpow _)
    _ = C_U * (c₁ + 1) * (T x.length + 1) ^ 2 := by ring

/-- **The time-bounded universal machine** [AB09, §1.4.1, "Universal TM with time
bound"]: a single machine that, given `⟨⟨⌞t⌟, α⟩, x⟩` (clock and code first, input
last), simulates the machine `α` denotes on `x` for at most `t` steps, reporting
success (`true :: output`) or timeout (`[false]`).

**Proof sketch.** Extend the simulation of `Turing.universal` with a binary
countdown clock on a further work tape, initialized from `⌞t⌟ = Nat.bits t` (parsed
from the doubled-bit region; cost `O(t + 1)`, within budget). Each simulated step
costs an additional `O((Nat.bits t).length + 1)` for the decrement, whence the
quadratic budget; `M`'s emissions are buffered on a work tape rather than emitted
(their total length is at most `t`, by `Turing.MultiTapeTM.output_length_le`).
Halting is checked after each simulated transition, **including the `t`-th**: if the
simulated machine has halted by the time the clock expires — deadline included —
`U` emits `true` and flushes the buffer; otherwise it emits `false`. At `t = 0` no
initialized machine has halted (`Turing.FinTM.not_computesInTime_zero`), and the
timeout branch applies (audit finding 6). The two cases below are exhaustive:
either some output witnesses halting within `t`, or every output fails to. -/
theorem timed_universal (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      (∀ output : List Bool,
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          (true :: output) (C * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          [false] (C * (t + 1) ^ 2)) := by
  sorry

end Turing
