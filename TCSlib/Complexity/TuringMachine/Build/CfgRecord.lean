/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.SymbolLift
import TCSlib.Complexity.TuringMachine.Build.InputCall

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: configuration records over a rich alphabet (§12.8)

The record carrier of the §12.8 rich-alphabet design
(`machine-library-design.md` §12.8a §2, decision 12.8.1): a configuration of a
`Bool` machine with work tapes inside a radius-`s` window, written as a list of
fields over the rich alphabet `Turing.RecSym`. Records are what the
configuration-graph searches of chapter 4 (the reachability simulation of
`NSPACE` in `DSPACE` by breadth-first search, Savitch's midpoint recursion)
keep on their tapes, and the record rows are the machines that read, step and
compare them.

**Status: partial §12.8 fill C (status update).** The pure decoding facts are
proved. The state/tag test is proved modulo `fieldsTape_field`, `scanTM_run_ofCfg`,
`scanResult_fold`, `skipTM_run_ofCfg` and `skipBackTM_run_ofCfg`; equality is proved
modulo `fieldsTape_field`, `compareTM_run_ofCfg`, `skipTM_run_ofCfg` and
`skipBackTM_run_ofCfg`. The step row remains a statement under the fill brief's
continuation rule. No private helper is admitted.

## Design

* **One cell per simulated cell.** A tape field holds the `2s + 1` window cells
  of one work tape, each a content track and a head-mark track
  (`Turing.RecSym.cell`). The input position is a fixed-width binary field of
  digits, `O(log n)` cells, and the state and the tag take one cell each. A
  record therefore has `k(2s + 1) + posWidth n + 2` cells and `k + 2`
  separators, which is `O(S n)` at radius `O(S n)` for `S ≥ log`.
* **Blank-separated fields** (`Turing.joinFields`): every field is a §12.6
  delimited word in place (`Turing.fieldsTape_field`), so the framed catalog
  rows apply field by field, and no field is empty, so two blanks end a table.
* **Digits are the lift's `e`.** `Turing.RecSym.digitEmb` is the embedding
  along which the `Bool` counter rows run on rich tapes
  (`Turing.MultiTapeTM.liftSymbols`), and the native input of a rich
  simulator is the input's image under it.
* **The window predicate** `Turing.Cfg.InWindow` lives here, relocated
  verbatim from `TCSlib.Complexity.ClassPSPACE.TQBF` (decision 12.8.2), which
  now imports it, so the record carrier and the adjacency codec share one
  definition.
* **Record rows are existential modules** in the `exists_installCallTM` style:
  a machine, entry and verdict anchors, and a linear first-return bound, with
  every head, the input position and the scratch restored.

## Main definitions

* `Turing.Cfg.InWindow` — the radius-`s` window predicate (relocated).
* `Turing.RecSym`, `Turing.RecSym.digitEmb` — the record alphabet and its
  digit embedding.
* `Turing.binDigits`, `Turing.posWidth` — fixed-width binary digits and the
  input-position width.
* `Turing.cfgRecord` — the record of a configuration.
* `Turing.RecordValid`, `Turing.RecordAt` — valid records, and a record laid
  out at a head.

## Main results

* `Turing.cfgRecord_length` — a record has `k + 3` fields.
* `Turing.cfgRecord_inj` — on windowed configurations, records agree exactly
  when configuration cores and tags do (proved; fill-C status update).
* `Turing.recordValid_iff` — validity as a field-by-field shape condition
  (proved; fill-C status update).
* `Turing.exists_recordStepTM`, `Turing.exists_recordEqTM`,
  `Turing.exists_recordTestTM` — the record rows R8.7: one simulated step, record
  equality, and a test of the state and tag (fill-C status update: step is a
  statement; equality and test are proved modulo the catalog rows listed above).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1: the configuration graph and
  Claim 4.4(1), the `O(S(n))`-bit description of a configuration;
  Theorem 4.2(iii) and Theorem 4.14 (Savitch), whose simulations search the
  graph keeping configuration descriptions on work tapes. The record adds an
  `O(log n)` input-position field, as the book's description does.)
-/

namespace Turing

/-! ### The window predicate -/

/-- A configuration lies **in the radius-`s` window** when every work head
sits within `[-s, s]` and every work cell outside `[-s, s]` is blank — the
side condition under which the packaged codec of
`Complexity.exists_adjacency_codec_cnf` is faithful. (The input head needs no
clause: its type bounds it.) It is equally the side condition under which a
configuration record determines its configuration core, together with its
separately supplied tag (`Turing.cfgRecord_inj`);
relocated here from `TCSlib.Complexity.ClassPSPACE.TQBF` (decision 12.8.2). -/
def Cfg.InWindow {k : ℕ} {Symbol State : Type} {x : List Symbol} (s : ℕ)
    (c : Cfg k Symbol State x) : Prop :=
  (∀ i, |c.workTapePos i| ≤ (s : ℤ)) ∧
  ∀ (i : Fin k) (z : ℤ), (s : ℤ) < |z| → c.workTapes i z = none

/-! ### The record alphabet -/

/-- **The record alphabet** (design §12.8a §2) over machine states `Q` and tags
`T`: binary digits, simulated work cells with a head-mark track, the state
cell, and the tag cell. Fields of a record are separated by blank cells. -/
inductive RecSym (Q T : Type) where
  /-- a binary digit: the input-position field, counters, and the native input -/
  | digit (b : Bool)
  /-- one simulated work cell: its content and whether the head is on it -/
  | cell (content : Option Bool) (mark : Bool)
  /-- the state cell, `none` for halted -/
  | st (q : Option Q)
  /-- the tag cell: a summary of what the run has emitted -/
  | tag (τ : T)
deriving DecidableEq

/-- The record alphabet is finite when the states and tags are; this is the
`Fintype` instance `Turing.FinTM.alphabet_reduction` needs. -/
instance recSymFintype (Q T : Type) [Fintype Q] [Fintype T] : Fintype (RecSym Q T) :=
  derive_fintype% _

/-- **The digit embedding** (design §12.8a §2): `Bool` into the record alphabet
by `Turing.RecSym.digit`. It is the `e` along which `Bool` rows and the `Bool`
input are lifted to rich tapes (`Turing.MultiTapeTM.liftSymbols`). -/
def RecSym.digitEmb (Q T : Type) : Bool ↪ RecSym Q T :=
  ⟨RecSym.digit, fun _ _ h => by cases h; rfl⟩

/-! ### The record -/

/-- **Fixed-width binary digits** (design §12.8a §2): the `w` low bits of `v`,
least significant first. -/
def binDigits (w v : ℕ) : List Bool := (List.range w).map v.testBit

/-- **The input-position width** (design §12.8a §2) at input length `n`: the
bit length of `n + 1`, so that `2 ^ posWidth n > n + 1` and every input
position `0, …, n + 1` has a distinct `Turing.binDigits` code. -/
def posWidth (n : ℕ) : ℕ := (Nat.bits (n + 1)).length

/-- **The configuration record** (design §12.8a §2) of `c` at window radius
`s` with tag `τ`: `k + 3` fields. Field `0` is the state, field `1` the input
position in `Turing.binDigits` of width `Turing.posWidth |x|`, fields `2` to
`k + 1` the window cells `-s, …, s` of each work tape with their head marks,
and field `k + 2` the tag. The output tape is not recorded; the tag summarizes
it. -/
def cfgRecord {k : ℕ} {Q T : Type} {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T) :
    List (List (RecSym Q T)) :=
  [RecSym.st c.state] ::
    ((binDigits (posWidth x.length) c.inputPos.val).map RecSym.digit) ::
    (((List.finRange k).map fun i => (List.range (2 * s + 1)).map fun j =>
      RecSym.cell (c.workTapes i ((j : ℤ) - s)) (decide (c.workTapePos i = (j : ℤ) - s))) ++
    [[RecSym.tag τ]])

/-- **Record length** (design §12.8a §2): a record has `k + 3` fields, whatever
the configuration, radius and tag. -/
theorem cfgRecord_length {k : ℕ} {Q T : Type} {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x)
    (τ : T) : (cfgRecord s c τ).length = k + 3 := by
  simp [cfgRecord]

/-- Every native input position is strictly below the power of two specified by its width. -/
private theorem record_pos_lt (n : ℕ) : n + 1 < 2 ^ posWidth n := by
  unfold posWidth
  rw [Nat.size_eq_bits_len]
  exact Nat.lt_size_self _

/-- Decoding the fixed-width digits recovers any value below the width's power of two.

**Proof sketch.** Remove the low bit and divide the value by two. The induction hypothesis
decodes the remaining bits; the quotient-remainder identity restores the original value. -/
private theorem record_digits_value (w v : ℕ) (hv : v < 2 ^ w) :
    Nat.ofDigits 2 ((binDigits w v).map Bool.toNat) = v := by
  induction w generalizing v with
  | zero => simp at hv; subst hv; simp [binDigits]
  | succ w ih =>
    have hbits : binDigits (w + 1) v = v.testBit 0 :: binDigits w (v / 2) := by
      simp only [binDigits, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp [Nat.testBit_add_one]
    rw [hbits, List.map_cons, Nat.ofDigits_cons, ih (v / 2) (by rw [pow_succ] at hv; omega)]
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h] <;> omega

/-- Fixed-width digit strings distinguish the values in their representable range. -/
private theorem record_digits_inj (w u v : ℕ) (hu : u < 2 ^ w) (hv : v < 2 ^ w)
    (h : binDigits w u = binDigits w v) : u = v := by
  rw [← record_digits_value w u hu, ← record_digits_value w v hv, h]

/-- **Canonical decoding** (design §12.8a §2). On windowed configurations of
one input, records agree exactly when the configurations agree on state, input
position, work tapes and work heads, and the tags agree. The output is not
compared, so this is injectivity on the configuration core, the vertex
quotient of the configuration graph.

**Proof sketch.** Compare the fields. The state field gives the state. The
position field is `Turing.binDigits` at a width with `2 ^ posWidth |x| >
|x| + 1`, which is injective on values `≤ |x| + 1`, the range of input
positions. For tape `i`, the content track gives the cells in `[-s, s]`, and
outside it both configurations are blank by the window hypothesis. The mark
track has exactly one mark, at the head, which lies in `[-s, s]`. The tag field
gives the tag. -/
theorem cfgRecord_inj {k : ℕ} {Q T : Type} {x : List Bool} (s : ℕ) {c d : Cfg k Bool Q x}
    {τ τ' : T} (hc : c.InWindow s) (hd : d.InWindow s) :
    cfgRecord s c τ = cfgRecord s d τ' ↔
      (c.state = d.state ∧ c.inputPos = d.inputPos ∧ c.workTapes = d.workTapes ∧
        c.workTapePos = d.workTapePos) ∧ τ = τ' := by
  classical
  constructor
  · intro h
    simp only [cfgRecord, List.cons.injEq, bind_pure_comp, Functor.map, List.map_map, Function.comp_def] at h
    obtain ⟨hstate, hpos, hrest⟩ := h
    have hs : c.state = d.state := by simpa using hstate
    have hb : binDigits (posWidth x.length) c.inputPos.val =
        binDigits (posWidth x.length) d.inputPos.val :=
      (List.map_inj_right (fun _ _ h => RecSym.digit.inj h)).mp hpos
    have hp : c.inputPos = d.inputPos := Fin.ext
      (record_digits_inj _ _ _
        (lt_of_le_of_lt (by have := c.inputPos.isLt; omega) (record_pos_lt x.length))
        (lt_of_le_of_lt (by have := d.inputPos.isLt; omega) (record_pos_lt x.length)) hb)
    obtain ⟨hfields, htag⟩ := List.append_inj' hrest (by rfl)
    have ht : τ = τ' := by simpa using htag
    have hcell (i : Fin k) (j : ℕ) (hj : j < 2 * s + 1) :
        RecSym.cell (Q := Q) (T := T) (c.workTapes i ((j : ℤ) - s))
            (decide (c.workTapePos i = (j : ℤ) - s)) =
          RecSym.cell (d.workTapes i ((j : ℤ) - s))
            (decide (d.workTapePos i = (j : ℤ) - s)) := by
      have hi := List.map_inj_left.mp hfields i (by simp)
      exact List.map_inj_left.mp hi j (List.mem_range.mpr hj)
    have hw : c.workTapes = d.workTapes := by
      funext i z
      by_cases hz : |z| ≤ (s : ℤ)
      · have hz' := abs_le.mp hz
        have hnat : (((z + s).toNat : ℕ) : ℤ) = z + s := Int.toNat_of_nonneg (by omega)
        have h := (RecSym.cell.inj (hcell i (z + s).toNat (by omega))).1
        simpa only [hnat, add_sub_cancel_right] using h
      · rw [hc.2 i z (by omega), hd.2 i z (by omega)]
    have hh : c.workTapePos = d.workTapePos := by
      funext i
      have hi := abs_le.mp (hc.1 i)
      have hnat : (((c.workTapePos i + s).toNat : ℕ) : ℤ) = c.workTapePos i + s :=
        Int.toNat_of_nonneg (by omega)
      have h := (RecSym.cell.inj (hcell i (c.workTapePos i + s).toNat (by omega))).2
      simp only [hnat, add_sub_cancel_right, decide_true] at h
      exact (of_decide_eq_true h.symm).symm
    exact ⟨⟨hs, hp, hw, hh⟩, ht⟩
  · rintro ⟨⟨hs, hp, hw, hh⟩, ht⟩
    simp only [cfgRecord, hs, hp, hw, hh, ht]

/-- **Valid records** (design §12.8a §2): the field list is the record, at
radius `s`, of some windowed configuration on some input of length `n`, with
some tag. -/
def RecordValid (k n s : ℕ) (Q T : Type) (fs : List (List (RecSym Q T))) : Prop :=
  ∃ (x : List Bool) (c : Cfg k Bool Q x) (τ : T), x.length = n ∧ c.InWindow s ∧
    cfgRecord s c τ = fs

/-- **Validity is a shape condition** (design §12.8a §2). A field list is a
valid record exactly when it has `k + 3` fields: a state cell; `posWidth n`
digits of a value at most `n + 1`; for each tape, `2s + 1` work cells of which
exactly one carries the head mark; and a tag cell. This shape supports a
validity machine built from finite-state folds over the fields, given the
widths `2s + 1` and `posWidth n` and the bound `n + 1` as templates or
counters. A fold of one field alone cannot check a variable width: a single
marked cell is valid at `s = 0` and not at `s = 1`. The validator itself is
deferred to S1b's statement phase.

**Proof sketch.** Forward: read the shape off `Turing.cfgRecord`, with the mark
at index `pos + s` of each tape field, which is in range by the window
hypothesis. Backward: take the input `List.replicate n false`, the state and
the tag from their cells, the input position from the digits, and for tape `i`
the cell at `z` from index `z + s` of its field when `|z| ≤ s`, and blank
otherwise, with the head at the mark minus `s`. This configuration is windowed
and its record is the given list. -/
theorem recordValid_iff {k : ℕ} {Q T : Type} (n s : ℕ) (fs : List (List (RecSym Q T))) :
    RecordValid k n s Q T fs ↔
      fs.length = k + 3 ∧
      (∃ q : Option Q, fs[0]? = some [RecSym.st q]) ∧
      (∃ v ≤ n + 1, fs[1]? = some ((binDigits (posWidth n) v).map RecSym.digit)) ∧
      (∀ i : Fin k, ∃ (cs : ℕ → Option Bool) (m : ℕ), m < 2 * s + 1 ∧
        fs[i.val + 2]? = some ((List.range (2 * s + 1)).map fun j =>
          RecSym.cell (cs j) (decide (j = m)))) ∧
      (∃ τ : T, fs[k + 2]? = some [RecSym.tag τ]) := by
  classical
  constructor
  · rintro ⟨x, c, τ, rfl, hc, rfl⟩
    refine ⟨cfgRecord_length s c τ, ⟨c.state, rfl⟩,
      ⟨c.inputPos.val, by have := c.inputPos.isLt; omega, rfl⟩, ?_, ⟨τ, ?_⟩⟩
    · intro i
      have hi := abs_le.mp (hc.1 i)
      have hnat : (((c.workTapePos i + s).toNat : ℕ) : ℤ) = c.workTapePos i + s :=
        Int.toNat_of_nonneg (by omega)
      refine ⟨fun j => c.workTapes i ((j : ℤ) - s), (c.workTapePos i + s).toNat,
        by omega, ?_⟩
      simp only [cfgRecord, List.getElem?_cons_succ, bind_pure_comp, Functor.map, List.map_map, Function.comp_def]
      rw [List.getElem?_append_left (by simp), List.getElem?_map,
        List.getElem?_eq_getElem (by simp)]
      simp only [List.getElem_finRange, Option.map_some, Option.some.injEq]
      apply List.map_congr_left
      intro j _
      congr 1
      rw [decide_eq_decide]
      change (c.workTapePos i = (j : ℤ) - s) ↔ j = (c.workTapePos i + s).toNat
      omega
    · simp [cfgRecord, List.length_finRange]
  · rintro ⟨hlen, ⟨q, hq⟩, ⟨v, hv, hpos⟩, htapes, ⟨τ, htag⟩⟩
    choose cs m hm hfield using htapes
    let c : Cfg k Bool Q (List.replicate n false) :=
      ⟨q, ⟨v, by simpa using (show v < n + 2 by omega)⟩,
        (fun i z => if |z| ≤ (s : ℤ) then cs i (z + s).toNat else none),
        (fun i => (m i : ℤ) - s), []⟩
    have hc : c.InWindow s := by
      constructor
      · intro i
        change |(m i : ℤ) - s| ≤ (s : ℤ)
        have := hm i
        rw [abs_le]
        omega
      · intro i z hz
        change (if |z| ≤ (s : ℤ) then _ else _) = none
        rw [if_neg (by omega)]
    refine ⟨List.replicate n false, c, τ, List.length_replicate .., hc, ?_⟩
    apply List.ext_getElem?
    intro j
    by_cases hj : j < k + 3
    · rcases j with _ | (_ | j)
      · exact hq.symm
      · simpa [cfgRecord, c] using hpos.symm
      · by_cases hlast : j = k
        · subst j
          simpa [cfgRecord, c, List.getElem?_append] using htag.symm
        · have hjk : j < k := by omega
          let i : Fin k := ⟨j, hjk⟩
          rw [hfield i]
          simp only [cfgRecord, List.getElem?_cons_succ, bind_pure_comp, Functor.map, List.map_map, Function.comp_def]
          rw [List.getElem?_append_left (by simpa using hjk), List.getElem?_map,
            List.getElem?_eq_getElem (by simpa using hjk)]
          simp only [List.getElem_finRange, Option.map_some, Option.some.injEq]
          apply List.map_congr_left
          intro a ha
          have ha' := List.mem_range.mp ha
          have hz : |(a : ℤ) - s| ≤ (s : ℤ) := by rw [abs_le]; omega
          simp only [c, hz, if_pos, sub_add_cancel, Int.toNat_natCast]
          congr 1
          rw [decide_eq_decide]
          change ((m i : ℤ) - s = (a : ℤ) - s) ↔ a = m i
          omega
    · rw [List.getElem?_eq_none (by rw [cfgRecord_length]; omega),
        List.getElem?_eq_none (by omega)]

/-- **A record at a head** (design §12.8a §2): tape `r` holds the field layout
of `fs` from its head, delimited by blanks at relative positions `-1` and
`|joinFields fs|`. The cells beyond the delimiters are arbitrary. -/
def RecordAt {K : ℕ} {Γ S : Type*} {x : List Γ} (d : Cfg K Γ S x) (r : Fin K)
    (fs : List (List Γ)) : Prop :=
  ∀ p : ℤ, -1 ≤ p → p ≤ ((joinFields fs).length : ℤ) →
    d.workTapes r (d.workTapePos r + p) = fieldsTape fs p

/-! ### R8.7 — the record rows -/

/-- A finite run segment, recording its endpoint, verdict cut, and a common head radius.
This is only bookkeeping for `runFrom_add`; the machine phases use `phaseHostTM_run`. -/
private def RecordRun {K : ℕ} {Γ S : Type} {x : List Γ} (R : MultiTapeTM K Γ S)
    (yes no : S) (base : Fin K → ℤ) (radius : ℕ) (a b : Cfg K Γ S x) (t : ℕ) : Prop :=
  R.runFrom a t = b ∧
    (∀ u < t, (R.runFrom a u).state ≠ some yes ∧ (R.runFrom a u).state ≠ some no) ∧
    ∀ u ≤ t, ∀ j, |(R.runFrom a u).workTapePos j - base j| ≤ (radius : ℤ)

/-- The empty run has the required cut and retains the given head bound. -/
private theorem recordRun_zero {K : ℕ} {Γ S : Type} {x : List Γ}
    (R : MultiTapeTM K Γ S) (yes no : S) (base : Fin K → ℤ) (radius : ℕ)
    (a : Cfg K Γ S x) (h : ∀ j, |a.workTapePos j - base j| ≤ (radius : ℤ)) :
    RecordRun R yes no base radius a a 0 := by
  refine ⟨rfl, by omega, ?_⟩
  intro u hu j
  have : u = 0 := by omega
  subst u
  exact h j

/-- Concatenation preserves a shared verdict cut and a shared radius.

**Proof sketch.** Split a prefix at the join and use `runFrom_add` on the second part. -/
private theorem recordRun_trans {K : ℕ} {Γ S : Type} {x : List Γ}
    {R : MultiTapeTM K Γ S} {yes no : S} {base : Fin K → ℤ} {radius : ℕ}
    {a b c : Cfg K Γ S x} {t v : ℕ}
    (h : RecordRun R yes no base radius a b t)
    (g : RecordRun R yes no base radius b c v) :
    RecordRun R yes no base radius a c (t + v) := by
  refine ⟨by rw [MultiTapeTM.runFrom_add, h.1, g.1], ?_, ?_⟩
  · intro u hu
    by_cases hut : u < t
    · exact h.2.1 u hut
    · have he : u = t + (u - t) := by omega
      rw [he, MultiTapeTM.runFrom_add, h.1]
      exact g.2.1 _ (by omega)
  · intro u hu j
    by_cases hut : u ≤ t
    · exact h.2.2 u hut j
    · have he : u = t + (u - t) := by omega
      rw [he, MultiTapeTM.runFrom_add, h.1]
      exact g.2.2 _ (by omega) j

/-- A tagged phase cannot be a verdict at a different index. -/
private theorem record_tag_ne {K : ℕ} {Γ I : Type} {Ph : I → Type} {x : List Γ}
    (i : I) (v : Σ i, Ph i) (hi : i ≠ v.1) (c : Cfg K Γ (Ph i) x) :
    (c.mapState (Sigma.mk i)).state ≠ some v := by
  cases hs : c.state with
  | none => simp [Cfg.mapState, hs]
  | some s =>
    intro h
    have he : (⟨i, s⟩ : Σ i, Ph i) = v := by simpa [Cfg.mapState, hs] using h
    exact hi (congrArg Sigma.fst he)

/-- Package the tagged prefix and dispatched endpoint supplied by `phaseHostTM_run`.
No transition or phase-host induction is repeated here. -/
private theorem recordRun_tagged {K : ℕ} {Γ I : Type} {Ph : I → Type} {x : List Γ}
    {R : MultiTapeTM K Γ (Σ i, Ph i)} {yes no : Σ i, Ph i}
    {base : Fin K → ℤ} {radius : ℕ} {a b : Cfg K Γ (Σ i, Ph i) x}
    {i : I} {M : MultiTapeTM K Γ (Ph i)} {c : Cfg K Γ (Ph i) x} {t : ℕ}
    (hp : ∀ u ≤ t, R.runFrom a u = (M.runFrom c u).mapState (Sigma.mk i))
    (he : R.runFrom a (t + 1) = b) (hy : i ≠ yes.1) (hn : i ≠ no.1)
    (hb : ∀ u ≤ t, ∀ j, |(M.runFrom c u).workTapePos j - base j| ≤ (radius : ℤ))
    (hend : ∀ j, |b.workTapePos j - base j| ≤ (radius : ℤ)) :
    RecordRun R yes no base radius a b (t + 1) := by
  refine ⟨he, ?_, ?_⟩
  · intro u hu
    rw [hp u (by omega)]
    exact ⟨record_tag_ne i yes hy _, record_tag_ne i no hn _⟩
  · intro u hu j
    by_cases ht : u ≤ t
    · rw [hp u ht]
      exact hb u ht j
    · have : u = t + 1 := by omega
      rw [this, he]
      exact hend j

/-- Width one is exactly the empty-input case, where no native movement is needed. -/
private theorem recordStep_width_one (n : ℕ) : posWidth n = 1 ↔ n = 0 := by
  unfold posWidth
  rw [Nat.size_eq_bits_len]
  constructor
  · intro h
    have : ¬ 2 ≤ n + 1 := fun hn => by
      have : 1 < Nat.size (n + 1) := Nat.lt_size.mpr (by simpa using hn)
      omega
    omega
  · rintro rfl
    exact Nat.size_one

/-- Complementing a fixed-width counter exchanges its value with the distance from all ones.
**Proof sketch.** The two low bits sum to one; the tail values have weight two. -/
private theorem recordStep_complement_value (u : List Bool) :
    Nat.ofDigits 2 ((u.map not).map Bool.toNat) + Nat.ofDigits 2 (u.map Bool.toNat) =
      2 ^ u.length - 1 := by
  induction u with
  | nil => simp
  | cons b u ih =>
    have hp := Nat.one_le_two_pow (n := u.length)
    cases b <;>
      simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons, pow_succ,
        Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- A digit word with a representable value is that value's canonical fixed-width record word.
This uses the existing record decoder and Mathlib's equal-length digit injectivity. -/
private theorem recordStep_word_of_value (w : List Bool) (n : ℕ)
    (hn : n < 2 ^ w.length) (hw : Nat.ofDigits 2 (w.map Bool.toNat) = n) :
    w = binDigits w.length n := by
  apply (List.map_injective_iff (f := Bool.toNat)).mpr
    (by intro a b h; cases a <;> cases b <;> simp_all)
  apply Nat.ofDigits_inj_of_len_eq (by decide : 1 < 2)
  · simp [binDigits]
  · intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    cases b <;> decide
  · intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    cases b <;> decide
  · rw [hw, record_digits_value _ _ hn]

/-- Carry and borrow on the record's fixed-width digits are mutual successor operations.
**Proof sketch.** The public one-round counter value and length identify the predecessor
word using the shared canonical decoder. A structural carry/borrow inverse gives the
successor direction; no binary-value induction is repeated. -/
private theorem recordStep_digits_succ (w n : ℕ) (hn : n + 1 < 2 ^ w) :
    incFixed (binDigits w n) = some (binDigits w (n + 1)) ∧
      decFixed (binDigits w (n + 1)) = some (binDigits w n) := by
  have hv := record_digits_value w (n + 1) hn
  have hc := counterWord_value (binDigits w (n + 1)) 1 (by rw [hv]; omega)
  rw [hv] at hc
  have hlen : (counterWord (binDigits w (n + 1)) 1).length = w := by
    simp [counterWord_length, binDigits]
  have hw : counterWord (binDigits w (n + 1)) 1 = binDigits w n := by
    have h := recordStep_word_of_value (counterWord (binDigits w (n + 1)) 1) n
      (by rw [hlen]; omega) (by simpa using hc)
    simpa only [hlen] using h
  change (decFixed (binDigits w (n + 1))).getD (binDigits w (n + 1)) = binDigits w n at hw
  have hd : decFixed (binDigits w (n + 1)) = some (binDigits w n) := by
    cases h : decFixed (binDigits w (n + 1)) with
    | none =>
      have he : binDigits w (n + 1) = binDigits w n := by simpa [h] using hw
      have := record_digits_inj w (n + 1) n hn (by omega) he
      omega
    | some v =>
      have he : v = binDigits w n := by simpa [h] using hw
      simp only [he]
  have inverse (u v : List Bool) (h : decFixed u = some v) : incFixed v = some u := by
    induction u generalizing v with
    | nil => simp [decFixed] at h
    | cons b u ih =>
      cases b with
      | true =>
        simp only [decFixed, Option.some.injEq] at h
        subst v
        rfl
      | false =>
        cases htail : decFixed u with
        | none => simp [decFixed, htail] at h
        | some v' =>
          simp only [decFixed, htail, Option.map_some, Option.some.injEq] at h
          subst v
          simp [incFixed, ih v' htail]
  exact ⟨inverse _ _ hd, hd⟩

/-- Complementing the remaining all-one fuel gives the fixed-width word for q+1.
**Proof sketch.** Public counter value and length facts give the remaining value. The
complement sum gives q+1, and the canonical decoder identifies its word. -/
private theorem recordStep_saved_digits (w : List Bool) (q : ℕ)
    (hw : Nat.ofDigits 2 (w.map Bool.toNat) = 2 ^ w.length - 1)
    (hq : q + 1 < 2 ^ w.length) :
    (counterWord w (q + 1)).map not = binDigits w.length (q + 1) := by
  have hle : q + 1 ≤ Nat.ofDigits 2 (w.map Bool.toNat) := by omega
  have hv := counterWord_value w (q + 1) hle
  have hn := recordStep_complement_value (counterWord w (q + 1))
  rw [counterWord_length, hv, hw] at hn
  have he := recordStep_word_of_value ((counterWord w (q + 1)).map not) (q + 1)
    (by simpa [counterWord_length] using hq) (by omega)
  simpa [counterWord_length] using he

/-- A source transition leaves the window exactly when a head crosses a boundary.
Writing at a head that was inside the window cannot create an exterior nonblank cell.
**Proof sketch.** Split the three possible moves. Interior positions stay inside; at each
boundary only its outward move fails. Outside cells are unchanged by the point update. -/
private theorem recordStep_window {k : ℕ} {Q : Type} {x : List Bool}
    (s : ℕ) (c : Cfg k Bool Q x) (hc : c.InWindow s) (a : Action k Bool Q) :
    (a.apply c).InWindow s ↔ ∀ i,
      ¬ (c.workTapePos i = -(s : ℤ) ∧ (a.workTapes i).2 = -1) ∧
      ¬ (c.workTapePos i = (s : ℤ) ∧ (a.workTapes i).2 = 1) := by
  have heads (i : Fin k) : |c.workTapePos i + ((a.workTapes i).2 : ℤ)| ≤ (s : ℤ) ↔
      ¬ (c.workTapePos i = -(s : ℤ) ∧ (a.workTapes i).2 = -1) ∧
      ¬ (c.workTapePos i = (s : ℤ) ∧ (a.workTapes i).2 = 1) := by
    have h := hc.1 i
    rw [abs_le] at h ⊢
    cases hm : (a.workTapes i).2 <;> simp at * <;> omega
  constructor
  · intro h i
    exact (heads i).mp (h.1 i)
  · intro h
    refine ⟨fun i => (heads i).mpr (h i), ?_⟩
    intro i z hz
    have hne : z ≠ c.workTapePos i := by
      intro he
      subst z
      have := hc.1 i
      omega
    simp only [Action.apply]
    cases hw : (a.workTapes i).1 <;> simp [Function.update, hne, hc.2 i z hz]

/-- Reconstruct the selected digit bank through the public R1 selected-tape and frame facts.
**Proof sketch.** Selected cells decode and re-encode because they are digits or blanks.
Unselected cells and heads are the time-zero frame of the supplied lifted row. -/
private theorem recordStep_restrict {K m : ℕ} {Γ S : Type} [DecidableEq Γ]
    (R : MultiTapeTM m Bool S) (e : Bool ↪ Γ) (ι : Fin m ↪ Fin K) {x : List Bool}
    (d : Cfg K Γ S (x.map e))
    (hdig : ∀ i p γ, d.workTapes (ι i) p = some γ → ∃ b, γ = e b) :
    d = embedEmitCfg ι d.workTapes d.workTapePos d.output
      (Cfg.liftSymbols e (⟨d.state, Fin.cast (by simp) d.inputPos,
        fun i p => (d.workTapes (ι i) p).bind (decodeBool e),
        fun i => d.workTapePos (ι i), []⟩ : Cfg m Bool S x)) := by
  let c : Cfg m Bool S x := ⟨d.state, Fin.cast (by simp) d.inputPos,
    fun i p => (d.workTapes (ι i) p).bind (decodeBool e),
    fun i => d.workTapePos (ι i), []⟩
  have frame := (embedEmitTM_frame ι (R.liftSymbols e)
    d.workTapes d.workTapePos d.output (c.liftSymbols e) 0).1
  apply Cfg.ext
  · rfl
  · apply Fin.ext; rfl
  · funext j
    by_cases h : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := h
      rw [embedEmitCfg_selected_tape]
      funext p
      change d.workTapes (ι i) p =
        ((d.workTapes (ι i) p).bind (decodeBool e)).map e
      cases hp : d.workTapes (ι i) p with
      | none => rfl
      | some γ =>
        obtain ⟨b, rfl⟩ := hdig i p γ hp
        simp [decodeBool_apply]
    · exact (frame j h).1.symm
  · funext j
    by_cases h : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := h
      rw [embedEmitCfg_selected_pos]
      rfl
    · exact (frame j h).2.symm
  · simp [embedEmitCfg, Cfg.liftSymbols]

/-- Transport every prefix of a Bool row on a selected digit bank; the surrounding rich
record and arbitrary output prefix remain the R1 frame. The restriction lemma is used once. -/
private theorem recordStep_transport {K m : ℕ} {Γ S : Type} [DecidableEq Γ]
    (R : MultiTapeTM m Bool S) (e : Bool ↪ Γ) (ι : Fin m ↪ Fin K) {x : List Bool}
    (d : Cfg K Γ S (x.map e))
    (hdig : ∀ i p γ, d.workTapes (ι i) p = some γ → ∃ b, γ = e b) (t : ℕ) :
    (embedEmitTM ι (R.liftSymbols e)).runFrom d t =
      embedEmitCfg ι d.workTapes d.workTapePos d.output
        ((R.runFrom (⟨d.state, Fin.cast (by simp) d.inputPos,
          fun i p => (d.workTapes (ι i) p).bind (decodeBool e),
          fun i => d.workTapePos (ι i), []⟩ : Cfg m Bool S x) t).liftSymbols e) := by
  conv_lhs => rw [recordStep_restrict R e ι d hdig]
  rw [embedEmitTM_runFrom, MultiTapeTM.liftSymbols_runFrom]

/-- One shared frame argument for the three permitted native-input tables.
**Proof sketch.** Each live step is the public input-only action, and halted steps are
stationary. Induct on the run length, projecting tapes, heads and output. -/
private theorem recordStep_native_frame {K : ℕ} {Γ S : Type} {x : List Γ}
    (R : MultiTapeTM K Γ S) (move : S → Option Γ → SignType)
    (next : S → Option Γ → S)
    (htr : ∀ q inp work, R.tr q inp work = inputMoveAction (move q inp) (next q inp))
    (d : Cfg K Γ S x) (t : ℕ) :
    (R.runFrom d t).workTapes = d.workTapes ∧
      (R.runFrom d t).workTapePos = d.workTapePos ∧ (R.runFrom d t).output = d.output := by
  induction t with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    cases hs : (R.runFrom d t).state with
    | none => rw [MultiTapeTM.step_of_halt hs]; exact ih
    | some q =>
      rw [step_of_inputMoveAction R _ (move q _) hs (htr q _ _)]
      exact ih

/-- No public native-input-head primitive distinguishes the two blank boundaries.
This probe reads the current cell; at a blank it tries right and then moves left.
The Boolean verdict records the right boundary, whose resulting position is one cell left. -/
private inductive RecordStepProbe where
  | start
  | peek
  | done (right : Bool)
deriving DecidableEq, Fintype

/-- No public native-input-head primitive probes which blank boundary is under the head.
The permitted Probe table has no work-tape action or emission. -/
private def recordStepProbe {Γ : Type} : MultiTapeTM 4 Γ RecordStepProbe where
  q₀ := .start
  tr q inp _ := match q with
    | .start => if inp.isSome then inputMoveAction 0 (.done false)
        else inputMoveAction 1 .peek
    | .peek => inputMoveAction (-1) (.done inp.isNone)
    | .done b => inputMoveAction 0 (.done b)

/-- No public native-input-head primitive provides the save-loop round.
Save has zero work tapes: a nonblank input cell moves left and returns to false; a blank
exits to true. The separate counter is supplied only by `counterLoopTM`. -/
private def recordStepSave : MultiTapeTM 0 Bool Bool where
  q₀ := false
  tr q inp _ := if q || inp.isNone then inputMoveAction 0 true
    else inputMoveAction (-1) false

/-- No public native-input-head primitive reads a native symbol into finite control.
Read makes one stationary step and returns the decoded Bool symbol, leaving the bank intact. -/
private def recordStepRead {Q T : Type} [DecidableEq Q] [DecidableEq T] :
    MultiTapeTM 4 (RecSym Q T) (Option (Option Bool)) where
  q₀ := none
  tr _ inp _ := inputMoveAction 0 (some (inp.bind (decodeBool (RecSym.digitEmb Q T))))

/-- The Read table's exact one-step exit, full exit cut, and fixed work bank. -/
private theorem recordStep_read_run {Q T : Type} [DecidableEq Q] [DecidableEq T]
    {x : List (RecSym Q T)} (d : Cfg 4 (RecSym Q T) (Option (Option Bool)) x)
    (hd : d.state = some none) :
    recordStepRead.runFrom d 1 =
        {d with state := some (some (d.inputSymbol.bind (decodeBool (RecSym.digitEmb Q T))))} ∧
      (∀ u < 1, ∀ b, (recordStepRead.runFrom d u).state ≠ some (some b)) := by
  constructor
  · change recordStepRead.step d = _
    rw [step_of_inputMoveAction recordStepRead d 0 hd rfl, moveInputPos_zero]
  · intro u hu b
    have : u = 0 := by omega
    subst u
    simp [hd]

/-- Before Save reaches the left boundary it takes exactly one left step per round.
The output clause will supply the arbitrary-prefix restoration after the R1 lift.
**Proof sketch.** At round r below the starting position the native symbol is interior.
Apply the public input-only step. At the starting position the next round exits. -/
private theorem recordStep_save_orbit {x : List Bool} (c : Cfg 0 Bool Bool x)
    (hc : c.state = some false) (hp : c.inputPos.val ≤ x.length) :
    (∀ r ≤ c.inputPos.val,
      (counterLoopOrbit recordStepSave (fun _ => 1) c r).state = some false ∧
      (counterLoopOrbit recordStepSave (fun _ => 1) c r).inputPos.val = c.inputPos.val - r ∧
      (counterLoopOrbit recordStepSave (fun _ => 1) c r).output = c.output) ∧
    (counterLoopOrbit recordStepSave (fun _ => 1) c (c.inputPos.val + 1)).state = some true ∧
    (counterLoopOrbit recordStepSave (fun _ => 1) c (c.inputPos.val + 1)).inputPos.val = 0 ∧
    (counterLoopOrbit recordStepSave (fun _ => 1) c (c.inputPos.val + 1)).output = c.output := by
  have before : ∀ r ≤ c.inputPos.val,
      (counterLoopOrbit recordStepSave (fun _ => 1) c r).state = some false ∧
      (counterLoopOrbit recordStepSave (fun _ => 1) c r).inputPos.val = c.inputPos.val - r ∧
      (counterLoopOrbit recordStepSave (fun _ => 1) c r).output = c.output := by
    intro r
    induction r with
    | zero => intro _; exact ⟨hc, rfl, rfl⟩
    | succ r ih =>
      intro hr
      obtain ⟨hs, hi, ho⟩ := ih (by omega)
      rw [counterLoopOrbit, Function.iterate_succ_apply']
      change (recordStepSave.step (counterLoopOrbit recordStepSave (fun _ => 1) c r)).state = some false ∧
        (recordStepSave.step (counterLoopOrbit recordStepSave (fun _ => 1) c r)).inputPos.val = c.inputPos.val - (r + 1) ∧
        (recordStepSave.step (counterLoopOrbit recordStepSave (fun _ => 1) c r)).output = c.output
      generalize counterLoopOrbit recordStepSave (fun _ => 1) c r = a at hs hi ho ⊢
      have ha := inputSymbolInner (cfg := a) (a.inputPos.val - 1) (by omega) (by omega)
      rw [step_of_inputMoveAction recordStepSave a (q' := false) (-1) hs (by simp [recordStepSave, ha])]
      refine ⟨rfl, ?_, ho⟩
      change (moveInputPos a.inputPos SignType.neg).val = _
      rw [FinTM.moveInputPos_neg_val]
      omega
  refine ⟨before, ?_⟩
  obtain ⟨hs, hi, ho⟩ := before c.inputPos.val le_rfl
  rw [counterLoopOrbit, Function.iterate_succ_apply']
  change (recordStepSave.step (counterLoopOrbit recordStepSave (fun _ => 1) c c.inputPos.val)).state = some true ∧
    (recordStepSave.step (counterLoopOrbit recordStepSave (fun _ => 1) c c.inputPos.val)).inputPos.val = 0 ∧
    (recordStepSave.step (counterLoopOrbit recordStepSave (fun _ => 1) c c.inputPos.val)).output = c.output
  generalize counterLoopOrbit recordStepSave (fun _ => 1) c c.inputPos.val = a at hs hi ho ⊢
  have ha : a.inputPos = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
  have hin : a.inputSymbol = none := by simp [Cfg.inputSymbol, ha]
  rw [step_of_inputMoveAction recordStepSave a (q' := true) 0 hs (by simp [recordStepSave, hin]),
    moveInputPos_zero]
  exact ⟨rfl, by rw [ha]; rfl, ho⟩

/-- A native input symbol is blank exactly at the two clamped boundaries. -/
private theorem recordStep_input_blank {K : ℕ} {Γ S : Type} {x : List Γ}
    (d : Cfg K Γ S x) : d.inputSymbol = none ↔
      d.inputPos.val = 0 ∨ d.inputPos.val = x.length + 1 := by
  by_cases h0 : d.inputPos = 0
  · simp [Cfg.inputSymbol, h0]
  by_cases hR : d.inputPos.val = x.length + 1
  · simp [Cfg.inputSymbol, h0, hR]
  have hval : d.inputPos.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hin := inputSymbolInner (cfg := d) (d.inputPos.val - 1) (by omega)
    (by have := d.inputPos.isLt; omega)
  simp [hin, hval, hR]

/-- Probe distinguishes the two blank boundaries in at most two steps on a nonempty input.
It leaves position q at q (normal), or moves the right boundary to the last symbol (right).
**Proof sketch.** A nonblank cell returns immediately. At a blank, a right step reads the
first symbol exactly at the left boundary; otherwise it clamps at the right boundary.
The second step moves left. Every prefix has fixed work heads by the shared native frame. -/
private theorem recordStep_probe_run {Γ : Type} {x : List Γ} (hx : 0 < x.length)
    (d : Cfg 4 Γ RecordStepProbe x) (hd : d.state = some .start) :
    ∃ t ≤ 2, ∃ b : Bool, ∃ p : Fin (x.length + 2),
      recordStepProbe.runFrom d t = {d with state := some (.done b), inputPos := p} ∧
      (∀ u < t, ∀ v, (recordStepProbe.runFrom d u).state ≠ some (.done v)) ∧
      b = decide (d.inputPos.val = x.length + 1) ∧
      p.val = (if b then x.length else d.inputPos.val) ∧
      (∀ u ≤ t, (recordStepProbe.runFrom d u).workTapePos = d.workTapePos) := by
  have fixed (t : ℕ) : (recordStepProbe.runFrom d t).workTapePos = d.workTapePos := by
    exact (recordStep_native_frame recordStepProbe
      (fun q inp => match q with
        | .start => if inp.isSome then 0 else 1 | .peek => -1 | .done _ => 0)
      (fun q inp => match q with
        | .start => if inp.isSome then .done false else .peek
        | .peek => .done inp.isNone | .done b => .done b)
      (by intro q inp work; cases q <;> cases inp <;> rfl) d t).2.1
  have right (hR : d.inputPos.val = x.length + 1) : moveInputPos d.inputPos 1 = d.inputPos := by
    have he : d.inputPos = (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) := Fin.ext hR
    rw [he]
    exact moveInputPos_rightBoundary
  by_cases hblank : d.inputSymbol = none
  · let a : Cfg 4 Γ RecordStepProbe x :=
      {d with state := some .peek, inputPos := moveInputPos d.inputPos 1}
    have step1 : recordStepProbe.step d = a :=
      step_of_inputMoveAction recordStepProbe d (q' := .peek) 1 hd (by
        simp [recordStepProbe, hblank])
    have step2 : recordStepProbe.step a =
        {d with state := some (.done a.inputSymbol.isNone), inputPos := moveInputPos a.inputPos (-1)} := by
      rw [step_of_inputMoveAction recordStepProbe a (q' := .done a.inputSymbol.isNone)
        (-1) rfl rfl]
    refine ⟨2, le_rfl, a.inputSymbol.isNone, moveInputPos a.inputPos (-1), ?_, ?_, ?_, ?_,
      fun u _ => fixed u⟩
    · change recordStepProbe.step (recordStepProbe.step d) = _
      rw [step1, step2]
    · intro u hu v
      have hu' : u = 0 ∨ u = 1 := by omega
      rcases hu' with rfl | rfl
      · simp [hd]
      · change (recordStepProbe.step d).state ≠ _
        rw [step1]
        simp [a]
    · rcases (recordStep_input_blank d).mp hblank with h0 | hR
      · have hpos : a.inputPos.val = 1 := by simp [a, moveInputPos, h0]
        have hin := inputSymbolInner (cfg := a) 0 (by omega) hx
        simp [hin, h0]
      · have hpos : a.inputPos = d.inputPos := right hR
        have hin : a.inputSymbol = none := (recordStep_input_blank a).mpr (Or.inr (by
          rw [hpos]; exact hR))
        simp [hin, hR]
    · rcases (recordStep_input_blank d).mp hblank with h0 | hR
      · have hpos : a.inputPos.val = 1 := by simp [a, moveInputPos, h0]
        have hin := inputSymbolInner (cfg := a) 0 (by omega) hx
        change (moveInputPos a.inputPos SignType.neg).val = _
        rw [FinTM.moveInputPos_neg_val]
        simp [hin, hpos, h0]
      · have hpos : a.inputPos.val = x.length + 1 := by change (moveInputPos d.inputPos 1).val = _; rw [right hR, hR]
        have hin : a.inputSymbol = none := (recordStep_input_blank a).mpr (Or.inr hpos)
        change (moveInputPos a.inputPos SignType.neg).val = _
        rw [FinTM.moveInputPos_neg_val]
        simp [hin, hpos]
  · have hbound := (recordStep_input_blank d).not.mp hblank
    have hR : d.inputPos.val ≠ x.length + 1 := fun h => hbound (Or.inr h)
    have his : d.inputSymbol.isSome = true := by cases h : d.inputSymbol <;> simp_all
    refine ⟨1, by omega, false, d.inputPos, ?_, ?_, by simp [hR], rfl, fun u _ => fixed u⟩
    · change recordStepProbe.step d = _
      rw [step_of_inputMoveAction recordStepProbe d (q' := .done false) 0 hd
        (by simp [recordStepProbe, his]), moveInputPos_zero]
    · intro u hu v
      have : u = 0 := by omega
      subst u
      simp [hd]

/-- Save's countdown reaches escape with the native head at zero, its work head restored,
and the complemented residual fuel coding q+1. The full counter-loop cut and trajectory
are retained for the later phase-host application.
**Proof sketch.** The save orbit exits in round q. All-one fuel is strictly larger than q;
apply `counterLoopTM_run_escape`, then its public arithmetic bounds and complement identity. -/
private theorem recordStep_save_run {x : List Bool} (c : Cfg 0 Bool Bool x)
    (hc : c.state = some false) (hp : c.inputPos.val ≤ x.length) (w : List Bool)
    (hwval : Nat.ofDigits 2 (w.map Bool.toNat) = 2 ^ w.length - 1)
    (hfuel : c.inputPos.val < Nat.ofDigits 2 (w.map Bool.toNat))
    (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ z : ℤ, -1 ≤ z → z ≤ (w.length : ℤ) → ct (cp + z) = FinTM.bufferTape w z) :
    ∃ t ≤ 5 * (c.inputPos.val + 1) + 2 * w.length,
      (counterLoopTM recordStepSave false (some true)).runFrom
          (counterLoopCfg (some (.dec .run)) c ct cp) t =
        counterLoopCfg (some .escape)
          {c with state := some true, inputPos := 0}
          (fun z => if cp ≤ z ∧ z < cp + (w.length : ℤ)
            then FinTM.bufferTape (counterWord w (c.inputPos.val + 1)) (z - cp) else ct z) cp ∧
      (∀ u < t,
        ((counterLoopTM recordStepSave false (some true)).runFrom
          (counterLoopCfg (some (.dec .run)) c ct cp) u).state ≠ some .done ∧
        ((counterLoopTM recordStepSave false (some true)).runFrom
          (counterLoopCfg (some (.dec .run)) c ct cp) u).state ≠ some .escape) ∧
      (∀ u ≤ t,
        ((counterLoopTM recordStepSave false (some true)).runFrom
          (counterLoopCfg (some (.dec .run)) c ct cp) u).workTapePos 0 ∈
            Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      Nat.ofDigits 2 (((counterWord w (c.inputPos.val + 1)).map not).map Bool.toNat) =
        c.inputPos.val + 1 := by
  obtain ⟨before, hs, hi, ho⟩ := recordStep_save_orbit c hc hp
  have orbit : counterLoopOrbit recordStepSave (fun _ => 1) c (c.inputPos.val + 1) =
      {c with state := some true, inputPos := 0} :=
    Cfg.ext_zero_tapes hs (Fin.ext hi) ho
  let t := c.inputPos.val + 1 + counterOverhead w (c.inputPos.val + 1)
  obtain ⟨he, hcut, hhead, _⟩ := counterLoopTM_run_escape recordStepSave false true
    (by decide) (fun _ => 1) c w ct cp hw c.inputPos.val hfuel
    (by
      intro r hr
      refine ⟨(before r hr).1, Nat.one_pos, ?_⟩
      intro u hu hv
      change u < 1 at hv
      omega) hs t (by simp [t])
  rw [orbit] at he
  refine ⟨t, ?_, he, hcut, hhead, ?_⟩
  · have hb := counterOverhead_le_of_le w (c.inputPos.val + 1) (by omega)
    dsimp [t]
    omega
  · have hv := counterWord_value w (c.inputPos.val + 1) (by omega)
    have hn := recordStep_complement_value (counterWord w (c.inputPos.val + 1))
    rw [counterWord_length, hv, hwval] at hn
    omega

/-- Finite data gathered before a record step writes anything to the record. The optional tag
allows an initial state even when the tag type is empty (then no valid entry record exists). -/
private structure RecordStepData (k : ℕ) (Q T : Type) where
  state : Option Q := none
  widthOne : Bool := false
  posZero : Bool := true
  symbols : Fin k → Option Bool := fun _ => none
  edgeLeft : Fin k → Bool := fun _ => false
  edgeRight : Fin k → Bool := fun _ => false
  tag : Option T := none
  nativeRight : Bool := false
  input : Option Bool := none
deriving DecidableEq

set_option synthInstance.maxSize 2048 in
/-- Finiteness of the nine-component data record; the larger local synthesis limit only
accommodates the derived nested-product instance. -/
private instance {k : ℕ} {Q T : Type} [Fintype Q] [Fintype T] :
    Fintype (RecordStepData k Q T) := by
  classical
  exact derive_fintype% _

/-- The stages of R8. Field counters are finite; each transition between stages is a dispatch
of the public phase host. Scratch tapes are B=1, Cs=2 and D=3. -/
private inductive RecordStepStage (k : ℕ) where
  | state | stateSkip | position | copyB | copyD | positionSkip
  | tapeRead (i : Fin k) | tapeSkip (i : Fin k) | tagRead | readBack (j : Fin (k + 2))
  | clearHaltB | clearHaltD | clearEmptyD | fuel | probe | save | seek | read
  | complement | decrementD | restore | clearD | clearRejectB
  | writeState | skipNewState | incB | decB | copyBack | clearB | skipNewPos
  | writeTape (i : Fin k) | shiftTape (i : Fin k) | skipNewTape (i : Fin k)
  | writeTag | writeBack (j : Fin (k + 2)) | verdict (yes : Bool)
deriving DecidableEq, Fintype

/-- Stage together with its accumulated finite data. -/
private abbrev RecordStepIndex (k : ℕ) (Q T : Type) :=
  RecordStepStage k × RecordStepData k Q T

/-- A field-read accumulator: a cell was seen, the marked content, the left-edge flag,
and the mark of the most recent cell (the right-edge flag at the end). -/
private def recordStepTapeFold {Q T : Type}
    (a : Bool × Option Bool × Bool × Bool) : RecSym Q T → Bool × Option Bool × Bool × Bool
  | .cell b m => (true, if m then b else a.2.1, a.2.2.1 || (!a.1 && m), m)
  | _ => a

/-- A prefix of a single-mark tape field records its marked content and both edge flags.
**Proof sketch.** Append the last cell to a range prefix. Only the unique marked index
can change the saved symbol, the first cell can set the left flag, and the last cell sets
the right flag. -/
private theorem recordStep_tape_prefix {Q T : Type} (f : ℕ → Option Bool) (p r : ℕ) :
    (((List.range r).map fun (j : ℕ) =>
      RecSym.cell (Q := Q) (T := T) (f j) (decide (p = j))).foldl recordStepTapeFold
        (false, none, false, false)) =
      (decide (0 < r), if p < r then f p else none,
        decide (0 < r ∧ p = 0), decide (0 < r ∧ p + 1 = r)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      recordStepTapeFold]
    by_cases hp : p = r
    · subst p
      by_cases hr : r = 0
      · simp [hr]
      · simp [hr]
        omega
    ·
      have he : p < r + 1 ↔ p < r := by omega
      simp [hp, he]
      omega

/-- The tape-field fold recovers the actual symbol under the source head and exactly its
two boundary tests, without changing the field.
**Proof sketch.** Shift the window head by s to a natural index and use the prefix invariant
at the full field length. The in-window hypothesis places the unique mark in that prefix. -/
private theorem recordStep_tape_fold {k : ℕ} {Q T : Type} {x : List Bool}
    (s : ℕ) (c : Cfg k Bool Q x) (hc : c.InWindow s) (i : Fin k) :
    let w : List (RecSym Q T) := (List.range (2 * s + 1)).map fun (j : ℕ) =>
      .cell (c.workTapes i ((j : ℤ) - s)) (decide (c.workTapePos i = (j : ℤ) - s))
    scanResult (scanFold recordStepTapeFold) scanKeep (false, none, false, false) w =
      ((true, c.workTapes i (c.workTapePos i),
        decide (c.workTapePos i = -(s : ℤ)), decide (c.workTapePos i = (s : ℤ))), w) := by
  dsimp only
  rw [scanResult_fold]
  let p := (c.workTapePos i + s).toNat
  have hi := hc.1 i
  rw [abs_le] at hi
  have hp : (p : ℤ) = c.workTapePos i + s := Int.toNat_of_nonneg (by omega)
  have hp' : p < 2 * s + 1 := by omega
  have hm (j : ℕ) : decide (p = j) = decide (c.workTapePos i = (j : ℤ) - s) := by
    rw [decide_eq_decide]
    omega
  have hw : ((List.range (2 * s + 1)).map fun (j : ℕ) =>
      RecSym.cell (Q := Q) (T := T) (c.workTapes i ((j : ℤ) - s)) (decide (p = j))) =
      (List.range (2 * s + 1)).map (fun (j : ℕ) =>
        RecSym.cell (c.workTapes i ((j : ℤ) - s)) (decide (c.workTapePos i = (j : ℤ) - s))) := by
    apply List.map_congr_left
    intro j _
    rw [hm]
  have hf := recordStep_tape_prefix (Q := Q) (T := T)
    (fun (j : ℕ) => c.workTapes i ((j : ℤ) - s)) p (2 * s + 1)
  rw [hw] at hf
  rw [hf]
  have hpos : (p : ℤ) - s = c.workTapePos i := by omega
  have hl : p = 0 ↔ c.workTapePos i = -(s : ℤ) := by omega
  have hr : p + 1 = 2 * s + 1 ↔ c.workTapePos i = (s : ℤ) := by omega
  simp only [if_pos hp', hpos, Nat.zero_lt_succ, true_and, hl, hr, decide_true]


/-- Saturating width count and all-zero flag for the position field. -/
private def recordStepPosFold {Q T : Type} (a : Fin 3 × Bool) : RecSym Q T → Fin 3 × Bool
  | .digit b => (⟨min 2 (a.1.val + 1), by omega⟩, a.2 && !b)
  | _ => a

/-- The position fold counts up to two and tests whether the represented value is zero.
**Proof sketch.** Induct over the digit word with an arbitrary count and Boolean flag;
the saturated count adds the word length and the flag conjoins the complemented digits. -/
private theorem recordStep_position_fold {Q T : Type} (w : List Bool) :
    scanResult (scanFold (@recordStepPosFold Q T)) scanKeep (0, true)
        (w.map RecSym.digit) =
      ((⟨min 2 w.length, by omega⟩, decide (Nat.ofDigits 2 (w.map Bool.toNat) = 0)),
        w.map RecSym.digit) := by
  have fold (a : Fin 3) (b : Bool) :
      (w.map (RecSym.digit (Q := Q) (T := T))).foldl recordStepPosFold (a, b) =
        (⟨min 2 (a.val + w.length), by omega⟩, b && w.all not) := by
    induction w generalizing a b with
    | nil =>
      apply Prod.ext
      · apply Fin.ext
        simp only [List.map_nil, List.foldl_nil, List.length_nil, Nat.add_zero]
        have := a.isLt
        omega
      · simp
    | cons v w ih =>
      simp only [List.map_cons, List.foldl_cons, recordStepPosFold, ih,
        List.length_cons, List.all_cons]
      apply Prod.ext
      · apply Fin.ext
        dsimp only
        omega
      · exact Bool.and_assoc _ _ _
  have value : w.all not = decide (Nat.ofDigits 2 (w.map Bool.toNat) = 0) := by
    clear fold
    induction w with
    | nil => rfl
    | cons b w ih => cases b <;> simp [Nat.ofDigits_cons, ih]
  rw [scanResult_fold, fold, value]
  simp

/-- The source action selected from data read before the rewrite. The halted case is used
only as finite data: the host takes its separate unchanged-record branch. -/
private def recordStepAction {k : ℕ} {Q T : Type} (M : MultiTapeTM k Bool Q)
    (d : RecordStepData k Q T) : Action k Bool Q :=
  match d.state with
  | some q => M.tr q d.input d.symbols
  | none => ⟨0, fun _ => (none, 0), none, none⟩

/-- The recorded edge flags detect precisely the forbidden outward moves. -/
private def recordStepOutside {k : ℕ} {Q T : Type} (M : MultiTapeTM k Bool Q)
    (d : RecordStepData k Q T) : Bool :=
  decide (∃ i, (d.edgeLeft i = true ∧ ((recordStepAction M d).workTapes i).2 = -1) ∨
    (d.edgeRight i = true ∧ ((recordStepAction M d).workTapes i).2 = 1))

/-- Native-position rows select only dedicated digit tapes: target B or D, scratch Cs. -/
private def recordStepSeekBank (restore : Bool) : Fin 2 ↪ Fin 4 :=
  ⟨fun i => if i = 0 then (if restore then 3 else 1) else 2, by
    intro i j h
    fin_cases i <;> fin_cases j <;> cases restore <;> simp_all⟩

/-- Save and the one-tape arithmetic rows select one dedicated digit tape. -/
private def recordStepDigitBank (i : Fin 3) : Fin 1 ↪ Fin 4 :=
  ⟨fun _ => ⟨i.val + 1, by omega⟩, fun a b _ => Subsingleton.elim a b⟩

/-- Mark projection for the public delay transducer. -/
private def recordStepGetMark {Q T : Type} : RecSym Q T → Bool
  | .cell _ b => b
  | _ => false

/-- Mark replacement preserves the content track. -/
private def recordStepSetMark {Q T : Type} : RecSym Q T → Bool → RecSym Q T
  | .cell c _, b => .cell c b
  | γ, _ => γ

/-- Rewrite a work symbol exactly at its old mark, before moving the mark. -/
private def recordStepWriteCell {Q T : Type} (write : Option (Option Bool)) :
    RecSym Q T → RecSym Q T
  | .cell c b => .cell (if b then write.getD c else c) b
  | γ => γ

/-- The finite-control right-clamp test identifies exactly the right blank of the input.
It also covers the empty input, whose two positions are both blank. -/
private theorem recordStep_right_clamp {k : ℕ} {Q : Type} {x : List Bool}
    (c : Cfg k Bool Q x) :
    (c.inputSymbol.isNone && !(decide (c.inputPos.val = 0))) =
      decide (c.inputPos.val = x.length + 1) := by
  have hb := recordStep_input_blank c
  by_cases hzero : c.inputPos.val = 0
  · simp [hzero]
  · by_cases hr : c.inputPos.val = x.length + 1
    · have hn := hb.mpr (Or.inr hr)
      simp [hn, hr]
    · have hn : c.inputSymbol ≠ none := fun h => (hb.mp h).elim hzero hr
      cases hs : c.inputSymbol <;> simp_all

/-- The F1 branch's unchanged word, borrow or carry is precisely the clamped native move.
**Proof sketch.** The two boundary tests give the two clamped cases. Every other move is
a representable successor or predecessor, so the shared digit arithmetic applies. -/
private theorem recordStep_position_digits {k : ℕ} {Q : Type} {x : List Bool}
    (c : Cfg k Bool Q x) (m : SignType) :
    (match m with
      | .zero => some (binDigits (posWidth x.length) c.inputPos.val)
      | .neg => if c.inputPos.val = 0 then some (binDigits (posWidth x.length) c.inputPos.val)
          else decFixed (binDigits (posWidth x.length) c.inputPos.val)
      | .pos => if c.inputSymbol.isNone && !(decide (c.inputPos.val = 0)) then
          some (binDigits (posWidth x.length) c.inputPos.val)
          else incFixed (binDigits (posWidth x.length) c.inputPos.val)) =
      some (binDigits (posWidth x.length) (moveInputPos c.inputPos m).val) := by
  have hp := c.inputPos.isLt
  have hw := record_pos_lt x.length
  cases m with
  | zero => simp
  | neg =>
    rw [FinTM.moveInputPos_neg_val]
    by_cases hz : c.inputPos.val = 0
    · simp [hz]
    · rw [if_neg hz]
      have hs : c.inputPos.val - 1 + 1 = c.inputPos.val := by omega
      have h := (recordStep_digits_succ (posWidth x.length) (c.inputPos.val - 1)
        (by omega)).2
      simpa only [hs] using h
  | pos =>
    rw [recordStep_right_clamp]
    by_cases hr : c.inputPos.val = x.length + 1
    · have he : c.inputPos = ⟨x.length + 1, by omega⟩ := Fin.ext hr
      simp [he, moveInputPos_rightBoundary]
    · have he := moveInputPos_pos_of_ne_right c.inputPos hr
      simp only [hr, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [he]
      exact (recordStep_digits_succ (posWidth x.length) c.inputPos.val (by omega)).1

/-- The marked-cell map writes exactly the source action's point update, preserving the
old mark until the separate shift pass. -/
private theorem recordStep_cell_write {k : ℕ} {Q T : Type} {x : List Bool}
    (a : Action k Bool Q) (c : Cfg k Bool Q x) (i : Fin k) (z : ℤ) :
    recordStepWriteCell (Q := Q) (T := T) (a.workTapes i).1
        (.cell (c.workTapes i z) (decide (c.workTapePos i = z))) =
      .cell ((a.apply c).workTapes i z) (decide (c.workTapePos i = z)) := by
  by_cases hz : c.workTapePos i = z
  · subst z
    cases hw : (a.workTapes i).1 <;> simp [recordStepWriteCell, hw]
  · have hz' : z ≠ c.workTapePos i := Ne.symm hz
    cases hw : (a.workTapes i).1 <;> simp [recordStepWriteCell, hz, hz', hw]

/-- The public delay transducers move the mark by the source move and preserve every
content cell, including when a mark would leave the displayed window.
**Proof sketch.** Use the public shift formulas. At an interior index the previous or next
mark is the shifted equality test; at the boundary the initial false agrees because the
old head is inside the window. The zero move is the identity fold. -/
private theorem recordStep_cell_shift {Q T : Type} (s : ℕ) (f : ℤ → Option Bool)
    (h : ℤ) (hh : |h| ≤ (s : ℤ)) (m : SignType) :
    let w : List (RecSym Q T) := (List.range (2 * s + 1)).map fun (j : ℕ) =>
      .cell (f ((j : ℤ) - s)) (decide (h = (j : ℤ) - s))
    (match m with
      | .neg => (scanResult scanKeep (scanShift recordStepGetMark recordStepSetMark) false w).2
      | .zero => (scanResult scanKeep scanKeep false w).2
      | .pos => (scanResult (scanShift recordStepGetMark recordStepSetMark) scanKeep false w).2) =
      (List.range (2 * s + 1)).map (fun (j : ℕ) =>
        .cell (f ((j : ℤ) - s)) (decide (h + (m : ℤ) = (j : ℤ) - s))) := by
  dsimp only
  rw [abs_le] at hh
  cases m with
  | zero =>
    have hi := scanResult_fold (fun b (_ : RecSym Q T) => b) false
      ((List.range (2 * s + 1)).map fun (j : ℕ) =>
        RecSym.cell (f ((j : ℤ) - s)) (decide (h = (j : ℤ) - s)))
    simpa only [SignType.zero_eq_zero, SignType.coe_zero, add_zero] using congrArg Prod.snd hi
  | pos =>
    rw [scanResult_shiftRight]
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      cases j with
      | zero =>
        have he : h + 1 ≠ -(s : ℤ) := by omega
        simp [List.getElem_zipWith, recordStepSetMark, he]
      | succ j =>
        simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range,
          List.getElem_cons_succ, recordStepGetMark, recordStepSetMark,
          SignType.pos_eq_one, SignType.coe_one]
        congr 1
        rw [decide_eq_decide]
        omega
  | neg =>
    rw [scanResult_shiftLeft]
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      have hjn : j < 2 * s + 1 := by simpa using hj'
      by_cases hend : j < 2 * s
      · rw [List.getElem_zipWith, List.getElem_append_left (by simpa using hend)]
        simp only [List.getElem_map, List.getElem_tail, List.getElem_range,
          recordStepGetMark, recordStepSetMark, SignType.neg_eq_neg_one, SignType.coe_neg_one]
        congr 1
        rw [decide_eq_decide]
        omega
      · have hlast : j = 2 * s := by omega
        subst j
        have he : h - 1 ≠ (s : ℤ) := by omega
        rw [List.getElem_zipWith, List.getElem_append_right (by simp)]
        simp only [List.getElem_map, List.getElem_range, List.length_map,
          List.length_tail, List.length_range, Nat.add_sub_cancel, Nat.sub_self,
          List.getElem_cons_zero, recordStepSetMark, SignType.neg_eq_neg_one,
          SignType.coe_neg_one, Nat.cast_mul, Nat.cast_ofNat]
        congr 1
        simp only [Bool.false_eq, decide_eq_false_iff_not]
        omega

/-- The write-then-shift recipe gives exactly the tape field of the applied source action.
The two scans retain the field length, so they fit the unchanged public field layout.
**Proof sketch.** The map pass is the point-update lemma at each displayed cell. The delay
pass is the mark-shift lemma with that updated content function. -/
private theorem recordStep_tape_word {k : ℕ} {Q T : Type} {x : List Bool}
    (s : ℕ) (c : Cfg k Bool Q x) (hc : c.InWindow s) (a : Action k Bool Q) (i : Fin k) :
    let old : List (RecSym Q T) := (List.range (2 * s + 1)).map fun (j : ℕ) =>
      .cell (c.workTapes i ((j : ℤ) - s)) (decide (c.workTapePos i = (j : ℤ) - s))
    let written := (scanResult (scanMap (recordStepWriteCell (a.workTapes i).1)) scanKeep () old).2
    (match (a.workTapes i).2 with
      | .neg => (scanResult scanKeep (scanShift recordStepGetMark recordStepSetMark) false written).2
      | .zero => (scanResult scanKeep scanKeep false written).2
      | .pos => (scanResult (scanShift recordStepGetMark recordStepSetMark) scanKeep false written).2) =
      (List.range (2 * s + 1)).map (fun (j : ℕ) =>
        .cell ((a.apply c).workTapes i ((j : ℤ) - s))
          (decide ((a.apply c).workTapePos i = (j : ℤ) - s))) := by
  dsimp only
  rw [scanResult_map]
  simp only [List.map_map]
  have hw : (fun (j : ℕ) => recordStepWriteCell (Q := Q) (T := T) (a.workTapes i).1
      (.cell (c.workTapes i ((j : ℤ) - s)) (decide (c.workTapePos i = (j : ℤ) - s)))) =
      fun (j : ℕ) => RecSym.cell ((a.apply c).workTapes i ((j : ℤ) - s))
        (decide (c.workTapePos i = (j : ℤ) - s)) := by
    funext j
    exact recordStep_cell_write a c i _
  dsimp only [Function.comp_def]
  rw [hw]
  exact recordStep_cell_shift s ((a.apply c).workTapes i) (c.workTapePos i) (hc.1 i)
    (a.workTapes i).2

/-- Every phase has exactly the state type of its unchanged row. -/
private def recordStepPhase {k : ℕ} {Q T S : Type} (i : RecordStepIndex k Q T) : Type :=
  match i.1 with
  | .state => ScanPhase (Option Q)
  | .position => ScanPhase (Fin 3 × Bool)
  | .tapeRead _ => ScanPhase (Bool × Option Bool × Bool × Bool)
  | .tagRead => ScanPhase (Option T)
  | .fuel | .complement | .writeState | .writeTape _ | .writeTag => ScanPhase Unit
  | .shiftTape _ => ScanPhase Bool
  | .probe => RecordStepProbe
  | .save => CounterLoopState Bool
  | .seek | .restore => S
  | .read => Option (Option Bool)
  | .incB | .decB | .decrementD => FlagPhase
  | .copyB | .copyD | .copyBack | .clearHaltB | .clearHaltD | .clearEmptyD |
      .clearD | .clearRejectB | .clearB => SweepPhase
  | _ => SeekPhase

/-- Each branch is the finite state type of its cited library row or native table. -/
private instance {k : ℕ} {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (i : RecordStepIndex k Q T) : Fintype (recordStepPhase (S := S) i) := by
  rcases i with ⟨i, d⟩
  cases i <;> dsimp [recordStepPhase] <;> infer_instance

/-- Equality is decided within the row selected by the stage. -/
private instance {k : ℕ} {Q T S : Type} [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (i : RecordStepIndex k Q T) : DecidableEq (recordStepPhase (S := S) i) := by
  rcases i with ⟨i, d⟩
  cases i <;> dsimp [recordStepPhase] <;> infer_instance

/-- R8's row family on four tapes. Native-reading Bool rows and the arithmetic rows all
use the same R1 transport on dedicated digit banks. No row selects the record tape. -/
private def recordStepRows {k : ℕ} {Q T S : Type} [DecidableEq Q] [DecidableEq T]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T) (seek : MultiTapeTM 2 Bool S)
    (i : RecordStepIndex k Q T) : MultiTapeTM 4 (RecSym Q T) (recordStepPhase (S := S) i) :=
  match i with
  | ⟨.state, _⟩ => scanTM 4 0 (scanFold (fun _ γ => match γ with
      | .st q => q | _ => none)) scanKeep none
  | ⟨.position, _⟩ => scanTM 4 0 (scanFold recordStepPosFold) scanKeep (0, true)
  | ⟨.copyB, _⟩ => copyTM 4 0 1
  | ⟨.copyD, _⟩ => copyTM 4 0 3
  | ⟨.tapeRead _, _⟩ => scanTM 4 0 (scanFold recordStepTapeFold) scanKeep
      (false, none, false, false)
  | ⟨.tagRead, _⟩ => scanTM 4 0 (scanFold (fun _ γ => match γ with
      | .tag τ => some τ | _ => none)) scanKeep none
  | ⟨.readBack _, _⟩ | ⟨.writeBack _, _⟩ => skipBackTM 4 0
  | ⟨.clearHaltB, _⟩ | ⟨.clearRejectB, _⟩ | ⟨.clearB, _⟩ => clearTM 4 1
  | ⟨.clearHaltD, _⟩ | ⟨.clearEmptyD, _⟩ | ⟨.clearD, _⟩ => clearTM 4 3
  | ⟨.fuel, _⟩ => scanTM 4 3 (scanMap (fun _ => RecSym.digit true)) scanKeep ()
  | ⟨.probe, _⟩ => recordStepProbe
  | ⟨.save, _⟩ => embedEmitTM (recordStepDigitBank 2)
      ((counterLoopTM recordStepSave false (some true)).liftSymbols (RecSym.digitEmb Q T))
  | ⟨.seek, _⟩ => embedEmitTM (recordStepSeekBank false) (seek.liftSymbols (RecSym.digitEmb Q T))
  | ⟨.restore, _⟩ => embedEmitTM (recordStepSeekBank true) (seek.liftSymbols (RecSym.digitEmb Q T))
  | ⟨.read, _⟩ => recordStepRead
  | ⟨.complement, _⟩ => scanTM 4 3 (scanMap (fun γ => match γ with
      | .digit b => .digit (!b) | γ => γ)) scanKeep ()
  | ⟨.decrementD, _⟩ => embedEmitTM (recordStepDigitBank 2)
      ((decrementTM 1 0).liftSymbols (RecSym.digitEmb Q T))
  | ⟨.incB, _⟩ => embedEmitTM (recordStepDigitBank 0)
      ((incrementTM 1 0).liftSymbols (RecSym.digitEmb Q T))
  | ⟨.decB, _⟩ => embedEmitTM (recordStepDigitBank 0)
      ((decrementTM 1 0).liftSymbols (RecSym.digitEmb Q T))
  | ⟨.copyBack, _⟩ => copyTM 4 1 0
  | ⟨.writeState, d⟩ => scanTM 4 0
      (scanMap (fun _ => RecSym.st (recordStepAction M d).state)) scanKeep ()
  | ⟨.writeTape j, d⟩ => scanTM 4 0
      (scanMap (recordStepWriteCell ((recordStepAction M d).workTapes j).1)) scanKeep ()
  | ⟨.shiftTape j, d⟩ => match ((recordStepAction M d).workTapes j).2 with
    | .neg => scanTM 4 0 scanKeep (scanShift recordStepGetMark recordStepSetMark) false
    | .zero => scanTM 4 0 scanKeep scanKeep false
    | .pos => scanTM 4 0 (scanShift recordStepGetMark recordStepSetMark) scanKeep false
  | ⟨.writeTag, d⟩ => scanTM 4 0 (scanMap (fun γ => match d.tag with
      | some τ => RecSym.tag (upd τ (recordStepAction M d).output) | none => γ)) scanKeep ()
  | ⟨.stateSkip, _⟩ | ⟨.positionSkip, _⟩ | ⟨.tapeSkip _, _⟩ | ⟨.skipNewState, _⟩ |
      ⟨.skipNewPos, _⟩ | ⟨.skipNewTape _, _⟩ | ⟨.verdict _, _⟩ => skipTM 4 0

/-- The finite dispatch that selects rejection before the first record rewrite. -/
private def recordStepApply {k : ℕ} {Q T S : Type} (M : MultiTapeTM k Bool Q)
    (d : RecordStepData k Q T) : Σ i : RecordStepIndex k Q T, recordStepPhase (S := S) i :=
  if recordStepOutside M d then ⟨⟨.clearRejectB, d⟩, .sweep⟩
  else ⟨⟨.writeState, d⟩, .fwd ()⟩

/-- The first tape field, or the tag for a zero-work-tape source. -/
private def recordStepFirstTape {k : ℕ} {Q T S : Type} (d : RecordStepData k Q T)
    (writing : Bool) : Σ i : RecordStepIndex k Q T, recordStepPhase (S := S) i :=
  if h : 0 < k then
    if writing then ⟨⟨.writeTape ⟨0, h⟩, d⟩, .fwd ()⟩
    else ⟨⟨.tapeRead ⟨0, h⟩, d⟩, .fwd (false, none, false, false)⟩
  else if writing then ⟨⟨.writeTag, d⟩, .fwd ()⟩ else ⟨⟨.tagRead, d⟩, .fwd none⟩

/-- All R8 phase exits are intercepted here. Dedicated verdicts erase the accumulated data,
so their states are the same anchors for every admissible input and source configuration. -/
private def recordStepNext {k : ℕ} {Q T S : Type} [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (start finish : S)
    (i : RecordStepIndex k Q T) : recordStepPhase (S := S) i →
      Option (Σ i : RecordStepIndex k Q T, recordStepPhase (S := S) i) :=
  match i with
  | ⟨.state, d⟩ => fun p => match p with
    | .done q => some ⟨⟨.stateSkip, {d with state := q}⟩, .run⟩ | _ => none
  | ⟨.stateSkip, d⟩ => fun p => match p with
    | .done => some ⟨⟨.position, d⟩, .fwd (0, true)⟩ | _ => none
  | ⟨.position, d⟩ => fun p => match p with
    | .done a => some ⟨⟨.copyB, {d with widthOne := a.1 == 1, posZero := a.2}⟩, .sweep⟩
    | _ => none
  | ⟨.copyB, d⟩ => fun p => match p with
    | .done => some ⟨⟨.copyD, d⟩, .sweep⟩ | _ => none
  | ⟨.copyD, d⟩ => fun p => match p with
    | .done => some ⟨⟨.positionSkip, d⟩, .run⟩ | _ => none
  | ⟨.positionSkip, d⟩ => fun p => match p with
    | .done => some (recordStepFirstTape d false) | _ => none
  | ⟨.tapeRead j, d⟩ => fun p => match p with
    | .done a => some ⟨⟨.tapeSkip j,
        { d with
          symbols := Function.update d.symbols j a.2.1
          edgeLeft := Function.update d.edgeLeft j a.2.2.1
          edgeRight := Function.update d.edgeRight j a.2.2.2 }⟩, .run⟩
    | _ => none
  | ⟨.tapeSkip j, d⟩ => fun p => match p with
    | .done => if h : j.val + 1 < k then
        some ⟨⟨.tapeRead ⟨j.val + 1, h⟩, d⟩, .fwd (false, none, false, false)⟩
        else some ⟨⟨.tagRead, d⟩, .fwd none⟩
    | _ => none
  | ⟨.tagRead, d⟩ => fun p => match p with
    | .done τ => some ⟨⟨.readBack ⟨k + 1, by omega⟩, {d with tag := τ}⟩, .run⟩ | _ => none
  | ⟨.readBack j, d⟩ => fun p => match p with
    | .done => if h : 0 < j.val then some ⟨⟨.readBack ⟨j.val - 1, by omega⟩, d⟩, .run⟩
        else if d.state.isNone then some ⟨⟨.clearHaltB, d⟩, .sweep⟩
        else if d.widthOne then some ⟨⟨.clearEmptyD, d⟩, .sweep⟩
        else some ⟨⟨.fuel, d⟩, .fwd ()⟩
    | _ => none
  | ⟨.clearHaltB, d⟩ => fun p => match p with
    | .done => some ⟨⟨.clearHaltD, d⟩, .sweep⟩ | _ => none
  | ⟨.clearHaltD, _⟩ => fun p => match p with
    | .done => some ⟨⟨.verdict true, {}⟩, .run⟩ | _ => none
  | ⟨.clearEmptyD, d⟩ => fun p => match p with
    | .done => some (recordStepApply M {d with input := none}) | _ => none
  | ⟨.fuel, d⟩ => fun p => match p with
    | .done _ => some ⟨⟨.probe, d⟩, .start⟩ | _ => none
  | ⟨.probe, d⟩ => fun p => match p with
    | .done b => some ⟨⟨.save, {d with nativeRight := b}⟩, .dec .run⟩ | _ => none
  | ⟨.save, d⟩ => fun p => match p with
    | .escape => some ⟨⟨.seek, d⟩, start⟩ | _ => none
  | ⟨.seek, d⟩ => fun p => if p = finish then some ⟨⟨.read, d⟩, none⟩ else none
  | ⟨.read, d⟩ => fun p => match p with
    | some b => some ⟨⟨.complement, {d with input := b}⟩, .fwd ()⟩ | none => none
  | ⟨.complement, d⟩ => fun p => match p with
    | .done _ => if d.nativeRight then some ⟨⟨.restore, d⟩, start⟩
        else some ⟨⟨.decrementD, d⟩, .run⟩
    | _ => none
  | ⟨.decrementD, d⟩ => fun p => match p with
    | .done _ => some ⟨⟨.restore, d⟩, start⟩ | _ => none
  | ⟨.restore, d⟩ => fun p => if p = finish then some ⟨⟨.clearD, d⟩, .sweep⟩ else none
  | ⟨.clearD, d⟩ => fun p => match p with
    | .done => some (recordStepApply M d) | _ => none
  | ⟨.clearRejectB, _⟩ => fun p => match p with
    | .done => some ⟨⟨.verdict false, {}⟩, .run⟩ | _ => none
  | ⟨.writeState, d⟩ => fun p => match p with
    | .done _ => some ⟨⟨.skipNewState, d⟩, .run⟩ | _ => none
  | ⟨.skipNewState, d⟩ => fun p => match p with
    | .done => match (recordStepAction M d).inputTape with
      | .zero => some ⟨⟨.clearB, d⟩, .sweep⟩
      | .neg => if d.posZero then some ⟨⟨.clearB, d⟩, .sweep⟩ else some ⟨⟨.decB, d⟩, .run⟩
      | .pos => if d.input.isNone && !d.posZero then some ⟨⟨.clearB, d⟩, .sweep⟩
          else some ⟨⟨.incB, d⟩, .run⟩
    | _ => none
  | ⟨.incB, d⟩ | ⟨.decB, d⟩ => fun p => match p with
    | .done _ => some ⟨⟨.copyBack, d⟩, .sweep⟩ | _ => none
  | ⟨.copyBack, d⟩ => fun p => match p with
    | .done => some ⟨⟨.clearB, d⟩, .sweep⟩ | _ => none
  | ⟨.clearB, d⟩ => fun p => match p with
    | .done => some ⟨⟨.skipNewPos, d⟩, .run⟩ | _ => none
  | ⟨.skipNewPos, d⟩ => fun p => match p with
    | .done => some (recordStepFirstTape d true) | _ => none
  | ⟨.writeTape j, d⟩ => fun p => match p with
    | .done _ => some ⟨⟨.shiftTape j, d⟩, .fwd false⟩ | _ => none
  | ⟨.shiftTape j, d⟩ => fun p => match p with
    | .done _ => some ⟨⟨.skipNewTape j, d⟩, .run⟩ | _ => none
  | ⟨.skipNewTape j, d⟩ => fun p => match p with
    | .done => if h : j.val + 1 < k then some ⟨⟨.writeTape ⟨j.val + 1, h⟩, d⟩, .fwd ()⟩
        else some ⟨⟨.writeTag, d⟩, .fwd ()⟩
    | _ => none
  | ⟨.writeTag, d⟩ => fun p => match p with
    | .done _ => some ⟨⟨.writeBack ⟨k + 1, by omega⟩, d⟩, .run⟩ | _ => none
  | ⟨.writeBack j, d⟩ => fun p => match p with
    | .done => if h : 0 < j.val then some ⟨⟨.writeBack ⟨j.val - 1, by omega⟩, d⟩, .run⟩
        else some ⟨⟨.verdict true, {}⟩, .run⟩
    | _ => none
  | ⟨.verdict _, _⟩ => fun _ => none

/-- Control type of the single public phase-host instance for record stepping. -/
private abbrev RecordStepControl (k : ℕ) (Q T S : Type) :=
  Σ i : RecordStepIndex k Q T, recordStepPhase (S := S) i

/-- The entry begins the state fold with no data yet read. -/
private def recordStepEntry {k : ℕ} {Q T S : Type} : RecordStepControl k Q T S :=
  ⟨⟨.state, {}⟩, .fwd none⟩

/-- Verdict anchors are independent of the data accumulated on this call. -/
private def recordStepVerdict {k : ℕ} {Q T S : Type} (b : Bool) : RecordStepControl k Q T S :=
  ⟨⟨.verdict b, {}⟩, .run⟩

/-- The concrete four-tape construction is exactly one instance of `phaseHostTM`. -/
private def recordStepMachine {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) :
    MultiTapeTM 4 (RecSym Q T) (RecordStepControl k Q T S) :=
  phaseHostTM (recordStepRows M upd seek) recordStepEntry (recordStepNext M start finish)

/-- The first state fold and its dispatch take five steps, preserve all cells and native
position, and have work-head radius one. This is the first `RecordRun` of the construction.
**Proof sketch.** Apply the public scan contract to the singleton state field, then the
fold identity. Its apparent rewrite is the original delimited field. The public phase-host
lemma adds one dispatch; the existing tagged-segment helper supplies the verdict cut. -/
private theorem recordStep_state_run {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List (RecSym Q T)}
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) x)
    (hd : d.state = some recordStepEntry) (q : Option Q)
    (hw : ∀ z : ℤ, -1 ≤ z → z ≤ 1 →
      d.workTapes 0 (d.workTapePos 0 + z) = FinTM.bufferTape [RecSym.st q] z) :
    RecordRun (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos 1 d
      {d with state := some ⟨⟨.stateSkip, {state := q}⟩, .run⟩} 5 := by
  let i : RecordStepIndex k Q T := ⟨.state, {}⟩
  let c : Cfg 4 (RecSym Q T) (ScanPhase (Option Q)) x :=
    ⟨some (.fwd none), d.inputPos, d.workTapes, d.workTapePos, d.output⟩
  let δ : Option Q → RecSym Q T → Option Q := fun _ γ => match γ with
    | .st a => a | _ => none
  obtain ⟨hrow, hcut, hheads⟩ := scanTM_run_ofCfg (0 : Fin 4) (scanFold δ) scanKeep none
    [RecSym.st q] c rfl hw
  have hfold : scanResult (scanFold δ) scanKeep none [RecSym.st q] = (q, [RecSym.st q]) := by
    rw [scanResult_fold]
    rfl
  rw [hfold] at hrow
  have he : (recordStepRows M upd seek i).runFrom c 4 = {c with state := some (.done q)} := by
    refine hrow.trans ?_
    apply Cfg.ext <;> try rfl
    funext j z
    dsimp only
    split
    next h =>
      obtain ⟨rfl, hlo, hhi⟩ := h
      have hz := hw (z - d.workTapePos 0) (by dsimp [c] at hlo; omega)
        (by dsimp [c] at hhi; omega)
      simpa [c] using hz.symm
    next => rfl
  let out : RecordStepControl k Q T S := ⟨⟨.stateSkip, {state := q}⟩, .run⟩
  have phase := phaseHostTM_run (recordStepRows M upd seek) recordStepEntry
    (recordStepNext M start finish) i c {c with state := some (.done q)} 4 he (.done q) rfl
    out rfl (by
      intro u hu a ha
      cases a with
      | fwd a => rfl
      | bwd a => rfl
      | done a => exact (hcut u hu a ha).elim)
  have hin : c.mapState (Sigma.mk i) = d := by
    apply Cfg.ext <;> try rfl
    simpa [Cfg.mapState, c, recordStepEntry, i] using hd.symm
  have hout : ({c with state := some (.done q)} : Cfg 4 (RecSym Q T) (ScanPhase (Option Q)) x).mapState
      (fun _ => out) = {d with state := some out} := rfl
  rw [hin] at phase
  have hend : (recordStepMachine M upd seek start finish).runFrom d 5 =
      {d with state := some out} := by
    simpa only [hout] using phase.2
  apply recordRun_tagged phase.1 hend
  · intro h
    have hst := congrArg Prod.fst h
    cases hst
  · intro h
    have hst := congrArg Prod.fst h
    cases hst
  · intro u hu j
    have hh := hheads j u hu
    by_cases hj : j = 0
    · subst j
      simp only [↓reduceIte, Finset.mem_Icc, List.length_cons, List.length_nil] at hh
      change |((scanTM 4 0 (scanFold δ) scanKeep none).runFrom c u).workTapePos 0 -
        c.workTapePos 0| ≤ (1 : ℤ)
      rw [abs_le]
      constructor <;> omega
    · rw [if_neg hj] at hh
      change |((recordStepRows M upd seek i).runFrom c u).workTapePos j - d.workTapePos j| ≤ 1
      rw [hh]
      simp [c]
  · intro j
    simp

/-- **R8.7, one simulated step** (design §12.8a §3, GAP-4). For a fixed `Bool`
machine `M` and a tag update `upd` that ignores silent steps, there is a module
over the record alphabet with an entry and two distinct verdict anchors with
the following contract. Start it at its entry with the record of a windowed
configuration `c` at the head of tape `0`, its other tapes blank, and the
native input `x` as digits. It reaches a verdict within `C` times the record
length plus `|x| + 1`, and no verdict earlier. If `M.step c` is windowed, the
verdict is `yes` and the record interval holds the record of `M.step c`, with
tag `upd τ (M.outputSymbol c)`; otherwise the verdict is `no` and nothing has
changed. In both cases every head, the input position, the other tapes and the
output are restored. Up to the verdict every work head stays within `C` times
the record length plus one of its entry position. So the module's work space
is linear in the record length, however far the native input head travels.
It depends on `|x|` only through the `posWidth |x|` position digits. A halted
`c` steps to itself with its tag
unchanged, by `hupd`.

**Proof sketch.** Compose by R2 seams, with no private trace. Read: `scanTM`
folds collect the state, the tag, and for each tape field the marked cell's
content and whether the mark is at an edge, moving between fields by `skipTM`.
Read the input symbol. The host's input position is arbitrary, so first save
it in binary on a scratch digit tape: a counter of width `posWidth |x|`, which
holds every input position since positions are at most `|x| + 1`. Then copy
the position field to another scratch digit tape (`copyTM`), run the lifted
`exists_inputSeekTM` on it, read the symbol, and restore the saved position.
At `|x| = 0`, which the one-digit position width reveals, the input is blank
and the head need not move. Dispatch on `M.tr` over the finite data. Apply: `scanTM` maps rewrite
the marked content, the state and the tag; delay steps shift the marks; the
position field moves by the lifted increment or decrement on the scratch tape,
clamped at `0` and `|x| + 1` as `moveInputPos` clamps, and is copied back. A
mark leaving the window selects `no` before anything is written. Rewind by
`skipBackTM`. Each phase takes time linear in the record length or in `|x|`.
Its work heads move only over the record and over scratch words of the
position width, hence within `O(L + 1)` cells.

**Fill-C continuation sketch appendix (partial).** The concrete witness below is one
`phaseHostTM` on the four-tape bank. Bool rows use the R1 transport on dedicated digit
tapes; the record tape remains in the unselected frame. The native-position save uses
all-one fuel, `counterLoopTM_run_escape`, complement, and the normal-branch decrement.
The Probe/Save/Read contracts, digit and field arithmetic, and first tagged read segment
are proved privately. The remaining admission is the complete composition of these
segments, including the seek/restore, scratch cleanup and final time/radius ledger. -/
theorem exists_recordStepTM {k : ℕ} {Q T : Type} [Fintype Q] [DecidableEq Q] [Fintype T]
    [DecidableEq T] (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (hupd : ∀ τ, upd τ none = τ) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + 1) (RecSym Q T) P) (entry yes no : P) (C : ℕ), yes ≠ no ∧
      ∀ {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T), c.InWindow s →
      ∀ d : Cfg (K + 1) (RecSym Q T) P (x.map (RecSym.digitEmb Q T)),
        d.state = some entry → RecordAt d 0 (cfgRecord s c τ) →
        (∀ j : Fin (K + 1), j ≠ 0 → ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * ((joinFields (cfgRecord s c τ)).length + x.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no) ∧
          (∀ u ≤ t, ∀ j : Fin (K + 1),
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((joinFields (cfgRecord s c τ)).length + 1) : ℕ) : ℤ)) ∧
          ((M.step c).InWindow s →
            R.runFrom d t =
              { d with
                state := some yes
                workTapes := fun j q =>
                  if j = 0 ∧ d.workTapePos j ≤ q ∧
                      q < d.workTapePos j + ((joinFields (cfgRecord s c τ)).length : ℤ)
                    then fieldsTape (cfgRecord s (M.step c) (upd τ (M.outputSymbol c)))
                      (q - d.workTapePos j)
                  else d.workTapes j q }) ∧
          (¬ (M.step c).InWindow s → R.runFrom d t = { d with state := some no }) := by
  classical
  obtain ⟨S, hfin, heq, seek, start, finish, Cseek, hseek⟩ := exists_inputSeekTM
  letI : Fintype S := hfin
  letI : DecidableEq S := heq
  let P := RecordStepControl k Q T S
  let entry : P := recordStepEntry
  let yes : P := recordStepVerdict true
  let no : P := recordStepVerdict false
  let R := recordStepMachine M upd seek start finish
  refine ⟨3, P, inferInstance, inferInstance, R, entry, yes, no,
    200 * (k + 3) * (Cseek + 1), ?_, ?_⟩
  · intro h
    have hh := congrArg (fun p : P => p.1.1) h
    cases hh
  · intro x s c τ hc d hd hrec hblank
    have hzero : 0 < (cfgRecord s c τ).length := by rw [cfgRecord_length]; omega
    have hspan : 1 ≤ (joinFields (cfgRecord s c τ)).length := by
      simpa [fieldOffset, cfgRecord] using
        fieldOffset_add_length_le (cfgRecord s c τ) 0 hzero
    have hread := recordStep_state_run M upd seek start finish d hd c.state (by
      intro z hz hlast
      rw [hrec z hz (by omega)]
      simpa only [cfgRecord, List.getElem_cons_zero, fieldOffset, List.take_zero,
        List.map_nil, List.sum_nil, Nat.cast_zero, zero_add] using
          fieldsTape_field (cfgRecord s c τ) 0 hzero z hz (by simpa [cfgRecord] using hlast))
    -- Proof sketch (continuation): concatenate the read, save/seek/restore, and rewrite
    -- segments with recordRun_trans. Each stage cites phaseHostTM_run and its public row
    -- contract; recordRun_tagged transfers the cut and common radius. The native cycle
    -- uses recordStep_transport and the checked Probe/Save/Read contracts. The old record
    -- is retained through the outward-move test, then each fixed-width field is rewritten.
    -- The remaining obligation is this complete segment ledger and its two exact endpoints.
    sorry

/-- Finite field and tape counters for the record comparison. -/
private inductive RecordEqIndex (k : ℕ) where
  | compare (j : Fin (k + 3))
  | forward (j : Fin (k + 2)) (i : Fin 2)
  | backward (b : Bool) (j : Fin (k + 2)) (i : Fin 2)
  | verdict (b : Bool)
deriving DecidableEq, Fintype

/-- The comparison phase uses the framed compare; all traversal phases use seek states. -/
private def recordEqPhase {k : ℕ} : RecordEqIndex k → Type
  | .compare _ => FlagPhase
  | _ => SeekPhase

/-- Finiteness of each unchanged equality row's phase type. -/
private instance {k : ℕ} (i : RecordEqIndex k) : Fintype (recordEqPhase i) := by
  cases i <;> dsimp [recordEqPhase] <;> infer_instance

/-- Equality of the equality row's phase states is decidable. -/
private instance {k : ℕ} (i : RecordEqIndex k) : DecidableEq (recordEqPhase i) := by
  cases i <;> dsimp [recordEqPhase] <;> infer_instance

/-- Return from field `j`, or report the verdict immediately when no field was crossed. -/
private def recordEqBack {k : ℕ} (b : Bool) (j : Fin (k + 3)) :
    Σ i : RecordEqIndex k, recordEqPhase i :=
  if h : 0 < j.val then ⟨.backward b ⟨j.val - 1, by omega⟩ 0, .run⟩
  else ⟨.verdict b, .run⟩

/-- Equality's unchanged library rows, without scratch tapes. -/
private def recordEqRows {k : ℕ} {Γ : Type} [DecidableEq Γ] (i : RecordEqIndex k) :
    MultiTapeTM 2 Γ (recordEqPhase i) :=
  match i with
  | .compare _ => compareTM 2 0 1
  | .forward _ i => skipTM 2 i
  | .backward _ _ i => skipBackTM 2 i
  | .verdict _ => skipTM 2 0

/-- Stationary equality dispatch: compare, cross both equal fields, or restore both heads. -/
private def recordEqNext {k : ℕ} (i : RecordEqIndex k) :
    recordEqPhase i → Option (Σ i : RecordEqIndex k, recordEqPhase i) :=
  match i with
  | .compare j => fun s => match s with
    | .done b => if b then
        if h : j.val < k + 2 then some ⟨.forward ⟨j.val, h⟩ 0, .run⟩
        else some (recordEqBack true j)
      else some (recordEqBack false j)
    | _ => none
  | .forward j i => fun s => match s with
    | .done => if i = 0 then some ⟨.forward j 1, .run⟩
        else some ⟨.compare ⟨j.val + 1, by omega⟩, .run⟩
    | _ => none
  | .backward b j i => fun s => match s with
    | .done => if i = 0 then some ⟨.backward b j 1, .run⟩
        else some (recordEqBack b ⟨j.val, by omega⟩)
    | _ => none
  | .verdict _ => fun _ => none

/-- **R8.7, record equality** (design §12.8a §3). There is a two-tape module
over the record alphabet with an entry and two distinct verdict anchors with
the following contract. Start it at its entry with field lists `fs` and `gs`,
of `k + 3` fields each, laid out at the heads of tapes `0` and `1`. It reaches
`yes` if `fs = gs` and `no` otherwise, within `C` times the length of `fs`'s
layout plus one, with no verdict earlier and nothing else changed. Up to the
verdict both heads stay within that many cells of their entry positions,
however long `gs` is. The input is arbitrary and not read.

**Proof sketch.** For each of the `k + 3` fields, run `compareTM` framed
(`compareTM_run_ofCfg`) on the two current fields; on `false`, return `no`, and
on `true`, `skipTM` both tapes to the next field. After the last field, return
`yes`. Before the verdict, `skipBackTM` both heads over the fields crossed,
which have the same lengths on both tapes. Every phase is linear in the cells
of `fs` crossed.

**Fill-C sketch appendix.** One `phaseHostTM` carries the field counter and tape
selector. `phaseHostTM_run` supplies each tagged prefix and stationary dispatch;
`recordRun_trans` only concatenates these established runs. A failed comparison
restores exactly the equal prefix. The bound uses only the first layout, including
when fields are empty or the second field is longer. -/
theorem exists_recordEqTM (k : ℕ) (Q T : Type) [Fintype Q] [DecidableEq Q] [Fintype T]
    [DecidableEq T] :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (R : MultiTapeTM 2 (RecSym Q T) P)
      (entry yes no : P) (C : ℕ), yes ≠ no ∧
      ∀ {x : List (RecSym Q T)} (fs gs : List (List (RecSym Q T))),
        fs.length = k + 3 → gs.length = k + 3 →
      ∀ d : Cfg 2 (RecSym Q T) P x, d.state = some entry → RecordAt d 0 fs → RecordAt d 1 gs →
        ∃ t ≤ C * ((joinFields fs).length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no) ∧
          (∀ u ≤ t, ∀ j : Fin 2,
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((joinFields fs).length + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t = { d with state := some (if fs = gs then yes else no) } := by
  classical
  let S := Σ i : RecordEqIndex k, recordEqPhase i
  let entry : S := ⟨.compare ⟨0, by omega⟩, .run⟩
  let yes : S := ⟨.verdict true, .run⟩
  let no : S := ⟨.verdict false, .run⟩
  let R : MultiTapeTM 2 (RecSym Q T) S := phaseHostTM recordEqRows entry recordEqNext
  refine ⟨S, inferInstance, inferInstance, R, entry, yes, no, 12 * (2 * k + 5), ?_⟩
  refine ⟨?_, ?_⟩
  · intro h
    have he := congrArg Sigma.fst h
    cases he
  intro x fs gs hfs hgs d hd hrf hrg
  let L := (joinFields fs).length
  let B := 12 * (L + 1)
  let cfg {A : Type} (q : A) (p : Fin 2 → ℕ) : Cfg 2 (RecSym Q T) A x :=
    ⟨some q, d.inputPos, d.workTapes,
      (fun i => d.workTapePos i + (fieldOffset fs (p i) : ℤ)), d.output⟩
  have hhead {A : Type} (q : A) (p : Fin 2 → ℕ) (hp : ∀ i, p i < fs.length) :
      ∀ i, |(cfg q p).workTapePos i - d.workTapePos i| ≤ ((L + 1 : ℕ) : ℤ) := by
    intro i
    have hb := fieldOffset_add_length_le fs (p i) (hp i)
    dsimp [cfg]
    rw [add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp [L] at *
    omega
  have hprefix (j l : ℕ) (hl : l ≤ j) (h : fs.take j = gs.take j) :
      fs.take l = gs.take l := by
    have he := congrArg (List.take l) h
    simpa [List.take_take, Nat.min_eq_left hl] using he
  have hfield (j l : ℕ) (hl : l < j) (hf : l < fs.length) (hg : l < gs.length)
      (h : fs.take j = gs.take j) : fs[l] = gs[l] := by
    have he := congrArg (fun w : List (List (RecSym Q T)) => w[l]?) h
    simpa [List.getElem?_take, hl, List.getElem?_eq_getElem hf,
      List.getElem?_eq_getElem hg] using he
  have hword0 (j : ℕ) (hj : j < fs.length) (z : ℤ) (hl : -1 ≤ z)
      (hu : z ≤ (fs[j].length : ℤ)) :
      d.workTapes 0 (d.workTapePos 0 + (fieldOffset fs j : ℤ) + z) =
        FinTM.bufferTape fs[j] z := by
    have hb := fieldOffset_add_length_le fs j hj
    rw [add_assoc, hrf _ (by omega) (by dsimp [L] at *; omega)]
    exact fieldsTape_field fs j hj z hl hu
  have hword1 (j : ℕ) (hj : j < gs.length) (he : fs.take j = gs.take j)
      (z : ℤ) (hl : -1 ≤ z) (hu : z ≤ (gs[j].length : ℤ)) :
      d.workTapes 1 (d.workTapePos 1 + (fieldOffset fs j : ℤ) + z) =
        FinTM.bufferTape gs[j] z := by
    have hoff : fieldOffset fs j = fieldOffset gs j := by unfold fieldOffset; rw [he]
    have hb := fieldOffset_add_length_le gs j hj
    rw [hoff, add_assoc, hrg _ (by omega) (by omega)]
    exact fieldsTape_field gs j hj z hl hu
  have hword (i : Fin 2) (j : ℕ) (hj : j < k + 3) (he : fs.take (j + 1) = gs.take (j + 1))
      (z : ℤ) (hl : -1 ≤ z) (hu : z ≤ (fs[j].length : ℤ)) :
      d.workTapes i (d.workTapePos i + (fieldOffset fs j : ℤ) + z) =
        FinTM.bufferTape fs[j] z := by
    fin_cases i
    · exact hword0 j (by omega) z hl hu
    · have hf := hfield (j + 1) j (by omega) (by omega) (by omega) he
      rw [hf] at hu ⊢
      exact hword1 j (by omega) (hprefix _ _ (by omega) he) z hl hu
  have hskip (j : Fin (k + 2)) (he : fs.take (j.val + 1) = gs.take (j.val + 1))
      (i : Fin 2) (p : Fin 2 → ℕ) (hpi : p i = j.val) (hp : ∀ r, p r < fs.length) :
      RecordRun R yes no d.workTapePos (L + 1)
        (cfg (⟨.forward j i, .run⟩ : S) p)
        (cfg (if i = 0 then (⟨.forward j 1, .run⟩ : S)
          else ⟨.compare ⟨j.val + 1, by omega⟩, .run⟩)
          (Function.update p i (j.val + 1))) (fs[j.val].length + 2) := by
    obtain ⟨hr, hc, hh⟩ := skipTM_run_ofCfg i fs[j.val] (cfg SeekPhase.run p) rfl
      (by intro z hl hu; simpa only [cfg, hpi] using hword i j.val (by omega) he z (by omega) hu)
    have hn : ∀ r, Function.update p i (j.val + 1) r < fs.length := by
      intro r
      by_cases hi : r = i
      · subst r; simp only [Function.update_self]; omega
      · simpa [Function.update_of_ne hi] using hp r
    have hend : (skipTM 2 i).runFrom (cfg SeekPhase.run p) (fs[j.val].length + 1) =
        cfg SeekPhase.done (Function.update p i (j.val + 1)) := by
      rw [hr]
      apply Cfg.ext <;> try rfl
      funext r
      by_cases hi : r = i
      · subst r
        simp only [cfg, Function.update_self, hpi,
          fieldOffset_succ fs j.val (by omega), Nat.cast_add, Nat.cast_one]
        omega
      · simp only [cfg, Function.update_of_ne hi]
    have hphase := phaseHostTM_run (recordEqRows (Γ := RecSym Q T)) entry recordEqNext
      (.forward j i) (cfg SeekPhase.run p)
      (cfg SeekPhase.done (Function.update p i (j.val + 1))) (fs[j.val].length + 1)
      hend .done rfl
      (if i = 0 then (⟨.forward j 1, .run⟩ : S) else ⟨.compare ⟨j.val + 1, by omega⟩, .run⟩)
      (by by_cases hi : i = 0 <;> simp [recordEqNext, hi])
      (by
        intro u hu z hz
        cases z with
        | done => exact False.elim (hc u hu hz)
        | run => rfl
        | gap => rfl
        | back => rfl)
    apply recordRun_tagged hphase.1 hphase.2 (by intro h; cases h) (by intro h; cases h) ?_
      (hhead _ _ hn)
    intro u hu r
    have hs := hh r u hu
    by_cases hi : r = i
    · subst r
      simp only [Finset.mem_Icc] at hs
      have hb := fieldOffset_add_length_le fs j.val (by omega)
      dsimp only [cfg] at hs ⊢
      rw [hpi] at hs
      rw [abs_le]
      dsimp [L] at *
      constructor <;> omega
    · rw [if_neg hi] at hs
      rw [hs]
      exact hhead _ p hp r
  have hback (b : Bool) (j : Fin (k + 2))
      (he : fs.take (j.val + 1) = gs.take (j.val + 1))
      (i : Fin 2) (p : Fin 2 → ℕ) (hpi : p i = j.val + 1) (hp : ∀ r, p r < fs.length) :
      RecordRun R yes no d.workTapePos (L + 1)
        (cfg (⟨.backward b j i, .run⟩ : S) p)
        (cfg (if i = 0 then (⟨.backward b j 1, .run⟩ : S)
          else recordEqBack b ⟨j.val, by omega⟩) (Function.update p i j.val))
        (fs[j.val].length + 4) := by
    have hoff := fieldOffset_succ fs j.val (by omega)
    obtain ⟨hr, hc, hh⟩ := skipBackTM_run_ofCfg i fs[j.val] (cfg SeekPhase.run p) rfl
      (by
        intro z hl hu
        convert hword i j.val (by omega) he z hl hu using 1
        dsimp [cfg]
        congr 1
        rw [hpi, hoff]
        push_cast
        ring)
    have hn : ∀ r, Function.update p i j.val r < fs.length := by
      intro r
      by_cases hi : r = i
      · subst r; simp only [Function.update_self]; omega
      · simpa [Function.update_of_ne hi] using hp r
    have hend : (skipBackTM 2 i).runFrom (cfg SeekPhase.run p) (fs[j.val].length + 3) =
        cfg SeekPhase.done (Function.update p i j.val) := by
      rw [hr]
      apply Cfg.ext <;> try rfl
      funext r
      by_cases hi : r = i
      · subst r
        simp only [cfg, Function.update_self, hpi, hoff, Nat.cast_add, Nat.cast_one]
        omega
      · simp only [cfg, Function.update_of_ne hi]
    have hphase := phaseHostTM_run (recordEqRows (Γ := RecSym Q T)) entry recordEqNext
      (.backward b j i) (cfg SeekPhase.run p)
      (cfg SeekPhase.done (Function.update p i j.val)) (fs[j.val].length + 3)
      hend .done rfl
      (if i = 0 then (⟨.backward b j 1, .run⟩ : S) else recordEqBack b ⟨j.val, by omega⟩)
      (by by_cases hi : i = 0 <;> simp [recordEqNext, hi])
      (by
        intro u hu z hz
        cases z with
        | done => exact False.elim (hc u hu hz)
        | run => rfl
        | gap => rfl
        | back => rfl)
    apply recordRun_tagged hphase.1 hphase.2 (by intro h; cases h) (by intro h; cases h) ?_
      (hhead _ _ hn)
    intro u hu r
    have hs := hh r u hu
    by_cases hi : r = i
    · subst r
      simp only [Finset.mem_Icc] at hs
      have hb := fieldOffset_add_length_le fs (j.val + 1) (by omega)
      have hoff' : (fieldOffset fs (j.val + 1) : ℤ) = fieldOffset fs j.val + fs[j.val].length + 1 := by
        rw [hoff]; push_cast; ring
      dsimp only [cfg] at hs ⊢
      rw [hpi] at hs
      rw [abs_le]
      dsimp [L] at *
      constructor <;> omega
    · rw [if_neg hi] at hs
      rw [hs]
      exact hhead _ p hp r
  have hforward (j : Fin (k + 2)) (he : fs.take (j.val + 1) = gs.take (j.val + 1)) :
      RecordRun R yes no d.workTapePos (L + 1)
        (cfg (⟨.forward j 0, .run⟩ : S) (fun _ => j.val))
        (cfg (⟨.compare ⟨j.val + 1, by omega⟩, .run⟩ : S) (fun _ => j.val + 1))
        ((fs[j.val].length + 2) + (fs[j.val].length + 2)) := by
    have h0 := hskip j he 0 (fun _ => j.val) rfl (by intro r; change j.val < fs.length; omega)
    have h1 := hskip j he 1 (Function.update (fun _ => j.val) 0 (j.val + 1))
      (by simp) (by intro r; fin_cases r <;> simp <;> omega)
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false] at h1
    have hp : Function.update (Function.update (fun _ : Fin 2 => j.val) 0 (j.val + 1))
        1 (j.val + 1) = fun _ => j.val + 1 := by
      funext r; fin_cases r <;> simp
    have h := recordRun_trans h0 h1
    rw [hp] at h
    exact h
  have hrestore (b : Bool) : ∀ j (hj : j ≤ k + 2), fs.take j = gs.take j →
      ∃ t ≤ j * B, RecordRun R yes no d.workTapePos (L + 1)
        (cfg (recordEqBack b ⟨j, by omega⟩) (fun _ => j))
        (cfg (⟨.verdict b, .run⟩ : S) (fun _ => 0)) t := by
    intro j
    induction j with
    | zero =>
      intro hj he
      exact ⟨0, by omega, recordRun_zero _ _ _ _ _ _ (hhead _ _ (by intro r; omega))⟩
    | succ j ih =>
      intro hj he
      obtain ⟨t, ht, hr⟩ := ih (by omega) (hprefix _ _ (by omega) he)
      let jj : Fin (k + 2) := ⟨j, by omega⟩
      have h0 := hback b jj he 0 (fun _ => j + 1) rfl (by intro r; change j + 1 < fs.length; omega)
      have h1 := hback b jj he 1 (Function.update (fun _ => j + 1) 0 j)
        (by simp [jj]) (by intro r; fin_cases r <;> simp <;> omega)
      simp only [show (1 : Fin 2) ≠ 0 by decide, if_false] at h1
      have hp : Function.update (Function.update (fun _ : Fin 2 => j + 1) 0 j) 1 j =
          fun _ => j := by funext r; fin_cases r <;> simp
      have hb := recordRun_trans h0 h1
      rw [hp] at hb
      have hb' : RecordRun R yes no d.workTapePos (L + 1)
          (cfg (recordEqBack b ⟨j + 1, by omega⟩) (fun _ => j + 1))
          (cfg (recordEqBack b ⟨j, by omega⟩) (fun _ => j))
          ((fs[j].length + 4) + (fs[j].length + 4)) := by
        simpa only [recordEqBack, Nat.zero_lt_succ, dif_pos] using hb
      have hlen := fieldOffset_add_length_le fs j (by omega)
      refine ⟨((fs[j].length + 4) + (fs[j].length + 4)) + t, ?_, recordRun_trans hb' hr⟩
      rw [Nat.succ_mul]
      dsimp [B, L] at *
      omega
  have hcompare (j : Fin (k + 3)) (he : fs.take j.val = gs.take j.val) :
      ∃ δ ≤ fs[j.val].length, RecordRun R yes no d.workTapePos (L + 1)
        (cfg (⟨.compare j, .run⟩ : S) (fun _ => j.val))
        (cfg (if fs[j.val] = gs[j.val] then
          if h : j.val < k + 2 then (⟨.forward ⟨j.val, h⟩ 0, .run⟩ : S)
          else recordEqBack true j else recordEqBack false j) (fun _ => j.val))
        (2 * δ + 3) := by
    obtain ⟨δ, hδ, hr, hc, hh⟩ := compareTM_run_ofCfg 0 1 (by decide) fs[j.val] gs[j.val]
      (cfg FlagPhase.run (fun _ => j.val)) rfl (hword0 j.val (by omega))
      (hword1 j.val (by omega) he)
    have hphase := phaseHostTM_run (recordEqRows (Γ := RecSym Q T)) entry recordEqNext
      (.compare j) (cfg FlagPhase.run (fun _ => j.val))
      (cfg (FlagPhase.done (decide (fs[j.val] = gs[j.val]))) (fun _ => j.val))
      (2 * δ + 2) hr (.done (decide (fs[j.val] = gs[j.val]))) rfl
      (if fs[j.val] = gs[j.val] then
        if h : j.val < k + 2 then (⟨.forward ⟨j.val, h⟩ 0, .run⟩ : S)
        else recordEqBack true j else recordEqBack false j)
      (by
        by_cases hf : fs[j.val] = gs[j.val]
        · by_cases hj : j.val < k + 2 <;> simp [recordEqNext, hf, hj]
        · simp [recordEqNext, hf])
      (by
        intro u hu z hz
        cases z with
        | run => rfl
        | rewind b => rfl
        | done b => exact False.elim (hc u hu b hz))
    refine ⟨δ, le_trans hδ (min_le_left _ _), ?_⟩
    apply recordRun_tagged hphase.1 hphase.2 (by intro h; cases h) (by intro h; cases h) ?_
      (hhead _ _ (by intro r; omega))
    intro u hu r
    have hs := hh r u hu
    have hi : r = 0 ∨ r = 1 := by fin_cases r <;> simp
    simp only [if_pos hi, Finset.mem_Icc] at hs
    have hb := fieldOffset_add_length_le fs j.val (by omega)
    dsimp only [cfg] at hs ⊢
    rw [abs_le]
    dsimp [L] at *
    constructor <;> omega
  have hsolve : ∀ r (j : Fin (k + 3)), k + 3 - j.val = r → fs.take j.val = gs.take j.val →
      ∃ t ≤ r * B + (k + 2) * B, RecordRun R yes no d.workTapePos (L + 1)
        (cfg (⟨.compare j, .run⟩ : S) (fun _ => j.val))
        (cfg (if fs = gs then yes else no) (fun _ => 0)) t := by
    intro r
    induction r with
    | zero => intro j hj; have := j.isLt; omega
    | succ r ih =>
      intro j hj he
      obtain ⟨δ, hδ, hc⟩ := hcompare j he
      have hspan := fieldOffset_add_length_le fs j.val (by omega)
      have hcost : 2 * δ + 3 ≤ B := by dsimp [B, L]; omega
      by_cases hf : fs[j.val] = gs[j.val]
      · have he' : fs.take (j.val + 1) = gs.take (j.val + 1) := by
          rw [List.take_succ, List.take_succ, he, List.getElem?_eq_getElem (by omega),
            List.getElem?_eq_getElem (by omega), hf]
        by_cases hj' : j.val < k + 2
        · simp only [if_pos hf, dif_pos hj'] at hc
          have hcross := hforward ⟨j.val, hj'⟩ he'
          obtain ⟨t, ht, hr⟩ := ih ⟨j.val + 1, by omega⟩ (by change k + 3 - (j.val + 1) = r; omega) he'
          refine ⟨((2 * δ + 3) + ((fs[j.val].length + 2) + (fs[j.val].length + 2))) + t,
            ?_, recordRun_trans (recordRun_trans hc hcross) hr⟩
          have hgroup : (2 * δ + 3) + ((fs[j.val].length + 2) + (fs[j.val].length + 2)) ≤ B := by
            dsimp [B, L]
            omega
          rw [Nat.succ_mul r B]
          omega
        · simp only [if_pos hf, dif_neg hj'] at hc
          have hlast : j.val = k + 2 := by have := j.isLt; omega
          have heq : fs = gs := by
            have hn : j.val + 1 = k + 3 := by omega
            have hf' : fs.take (k + 3) = fs := by rw [← hfs, List.take_length]
            have hg' : gs.take (k + 3) = gs := by rw [← hgs, List.take_length]
            rw [hn, hf', hg'] at he'
            exact he'
          obtain ⟨t, ht, hr⟩ := hrestore true j.val (by omega) he
          have ht' : t ≤ (k + 2) * B := by simpa only [hlast] using ht
          have hb : B ≤ (r + 1) * B := Nat.le_mul_of_pos_left _ (by omega)
          refine ⟨(2 * δ + 3) + t, by omega, ?_⟩
          simpa only [if_pos heq, yes] using recordRun_trans hc hr
      · simp only [if_neg hf] at hc
        have hne : fs ≠ gs := by intro h; subst gs; exact hf rfl
        obtain ⟨t, ht, hr⟩ := hrestore false j.val (by have := j.isLt; omega) he
        have ht' : t ≤ (k + 2) * B := le_trans ht (Nat.mul_le_mul_right B (by have := j.isLt; omega))
        have hb : B ≤ (r + 1) * B := Nat.le_mul_of_pos_left _ (by omega)
        refine ⟨(2 * δ + 3) + t, by omega, ?_⟩
        simpa only [if_neg hne, no] using recordRun_trans hc hr
  obtain ⟨t, ht, hall⟩ := hsolve (k + 3) ⟨0, by omega⟩ (by simp) rfl
  have hstart : cfg entry (fun _ => 0) = d := by
    apply Cfg.ext
    · exact hd.symm
    · rfl
    · rfl
    · funext i; simp [cfg, fieldOffset]
    · rfl
  change RecordRun R yes no d.workTapePos (L + 1) (cfg entry (fun _ => 0)) _ t at hall
  rw [hstart] at hall
  refine ⟨t, ?_, hall.2.1, ?_, ?_⟩
  · change t ≤ 12 * (2 * k + 5) * (L + 1)
    calc
      t ≤ (k + 3) * B + (k + 2) * B := ht
      _ = 12 * (2 * k + 5) * (L + 1) := by dsimp [B]; ring
  · intro u hu i
    have hh := hall.2.2 u hu i
    have hscale : L + 1 ≤ 12 * (2 * k + 5) * (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
    exact le_trans hh (by exact_mod_cast hscale)
  · rw [hall.1]
    apply Cfg.ext <;> try rfl
    funext i
    simp [cfg, fieldOffset]

/-- Finite dispatch indices for the state/tag test; the field counter is in the control. -/
private inductive RecordTestIndex (k : ℕ) (Q : Type) where
  | state
  | forward (q : Option Q) (j : Fin (k + 2))
  | tag (q : Option Q)
  | backward (b : Bool) (j : Fin (k + 2))
  | verdict (b : Bool)
deriving DecidableEq, Fintype

/-- Each test phase is precisely the state type of its unchanged library row. -/
private def recordTestPhase {k : ℕ} {Q : Type} : RecordTestIndex k Q → Type
  | .state => ScanPhase (Option (Option Q))
  | .tag _ => ScanPhase (Option Bool)
  | _ => SeekPhase

private instance {k : ℕ} {Q : Type} [Fintype Q] (i : RecordTestIndex k Q) :
    Fintype (recordTestPhase i) := by cases i <;> dsimp [recordTestPhase] <;> infer_instance

private instance {k : ℕ} {Q : Type} [DecidableEq Q] (i : RecordTestIndex k Q) :
    DecidableEq (recordTestPhase i) := by cases i <;> dsimp [recordTestPhase] <;> infer_instance

/-- Read a state cell with a fold; other symbols have no state interpretation. -/
private def recordReadState {Q T : Type} (_ : Option (Option Q)) : RecSym Q T → Option (Option Q)
  | .st q => some q
  | _ => none

/-- Read a tag cell and evaluate the fixed finite predicate. -/
private def recordReadTag {Q T : Type} (P : Option Q → T → Bool) (q : Option Q)
    (_ : Option Bool) : RecSym Q T → Option Bool
  | .tag τ => some (P q τ)
  | _ => none

/-- The test's row family: two folds, forward skips, and backward skips. -/
private def recordTestRows {k : ℕ} {Q T : Type} (P : Option Q → T → Bool)
    (i : RecordTestIndex k Q) : MultiTapeTM 1 (RecSym Q T) (recordTestPhase i) :=
  match i with
  | .state => scanTM 1 0 (scanFold recordReadState) scanKeep none
  | .tag q => scanTM 1 0 (scanFold (recordReadTag P q)) scanKeep none
  | .backward _ _ => skipBackTM 1 0
  | .forward _ _ => skipTM 1 0
  | .verdict _ => skipTM 1 0

/-- Stationary dispatch between the test's library phases. -/
private def recordTestNext {k : ℕ} {Q : Type} (i : RecordTestIndex k Q) :
    recordTestPhase i → Option (Σ i : RecordTestIndex k Q, recordTestPhase i) :=
  match i with
  | .state => fun s => match s with
    | .done a => some ⟨.forward (a.getD none) ⟨0, by omega⟩, .run⟩
    | _ => none
  | .forward q j => fun s => match s with
    | .done => if h : j.val + 1 < k + 2 then
        some ⟨.forward q ⟨j.val + 1, h⟩, .run⟩ else some ⟨.tag q, .fwd none⟩
    | _ => none
  | .tag _ => fun s => match s with
    | .done a => some ⟨.backward (a.getD false) ⟨k + 1, by omega⟩, .run⟩
    | _ => none
  | .backward b j => fun s => match s with
    | .done => if h : j.val = 0 then some ⟨.verdict b, .run⟩ else
        some ⟨.backward b ⟨j.val - 1, by omega⟩, .run⟩
    | _ => none
  | .verdict _ => fun _ => none

/-- **R8.7, a test of state and tag** (design §12.8a §3). For a predicate `P`
on states and tags, there is a one-tape module over the record alphabet with an
entry and two distinct verdict anchors with the following contract. Start it
at its entry with the record of `c` with tag `τ` at its head. It reaches `yes`
if `P c.state τ` and `no` otherwise, within `C` times the record length plus
one, with no verdict earlier and nothing else changed. Up to the verdict its
head stays within that many cells of its entry position. Consumers host it on a
record tape by R1 (`embedEmitTM`); the table search of the reachability
simulation tests for a halted accepting record this way.

**Proof sketch.** A `scanTM` fold reads the state field; `skipTM` crosses the
`k + 2` fields to the tag, a second fold reads the tag, and `skipBackTM`
returns over the fields crossed. Dispatch on `P` over the finite data.

**Fill-C sketch appendix.** The finite field counter and read state live in the
index of one `phaseHostTM`. Each fold and skip uses `phaseHostTM_run`; verdict
indices are distinct from every working index. `scanResult_fold` preserves the
field, and the common radius is the layout length plus one throughout the run. -/
theorem exists_recordTestTM {k : ℕ} {Q T : Type} [Fintype Q] [DecidableEq Q] [Fintype T]
    [DecidableEq T] (P : Option Q → T → Bool) :
    ∃ (P' : Type) (_ : Fintype P') (_ : DecidableEq P') (R : MultiTapeTM 1 (RecSym Q T) P')
      (entry yes no : P') (C : ℕ), yes ≠ no ∧
      ∀ {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T) {y : List (RecSym Q T)}
        (d : Cfg 1 (RecSym Q T) P' y), d.state = some entry →
        RecordAt d 0 (cfgRecord s c τ) →
        ∃ t ≤ C * ((joinFields (cfgRecord s c τ)).length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no) ∧
          (∀ u ≤ t, ∀ j : Fin 1,
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((joinFields (cfgRecord s c τ)).length + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t = { d with state := some (if P c.state τ then yes else no) } := by
  classical
  let S := Σ i : RecordTestIndex k Q, recordTestPhase i
  let entry : S := ⟨.state, .fwd none⟩
  let yes : S := ⟨.verdict true, .run⟩
  let no : S := ⟨.verdict false, .run⟩
  let R := phaseHostTM (recordTestRows P) entry recordTestNext
  refine ⟨S, inferInstance, inferInstance, R, entry, yes, no, 6 * (2 * (k + 2) + 2),
    ?_⟩
  refine ⟨?_, ?_⟩
  · intro h
    have he := congrArg Sigma.fst h
    cases he
  intro x s c τ y d hd hrec
  let fs := cfgRecord s c τ
  let L := (joinFields fs).length
  let B := 6 * (L + 1)
  have hlen : fs.length = k + 3 := cfgRecord_length s c τ
  let cfg {A : Type} (q : A) (j : ℕ) : Cfg 1 (RecSym Q T) A y :=
    ⟨some q, d.inputPos, d.workTapes,
      (fun i => d.workTapePos i + (fieldOffset fs j : ℤ)), d.output⟩
  have hhead {A : Type} (q : A) (j : ℕ) (hj : j < fs.length) :
      ∀ i, |(cfg q j).workTapePos i - d.workTapePos i| ≤ ((L + 1 : ℕ) : ℤ) := by
    intro i
    have hb := fieldOffset_add_length_le fs j hj
    dsimp [cfg]
    rw [add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp [L] at *
    omega
  have hword (j : ℕ) (hj : j < fs.length) (p : ℤ) (hl : -1 ≤ p)
      (hu : p ≤ (fs[j].length : ℤ)) :
      d.workTapes 0 (d.workTapePos 0 + (fieldOffset fs j : ℤ) + p) =
        FinTM.bufferTape fs[j] p := by
    have hb := fieldOffset_add_length_le fs j hj
    rw [add_assoc, hrec _ (by omega) (by dsimp [fs] at *; omega)]
    exact fieldsTape_field fs j hj p hl hu
  have hfold {A : Type} (δ : A → RecSym Q T → A) (a : A)
      (j : ℕ) (hj : j < fs.length) :
      (scanTM 1 0 (scanFold δ) scanKeep a).runFrom (cfg (ScanPhase.fwd a) j)
          (2 * fs[j].length + 2) = cfg (.done (fs[j].foldl δ a)) j ∧
      (∀ u < 2 * fs[j].length + 2, ∀ b,
        ((scanTM 1 0 (scanFold δ) scanKeep a).runFrom (cfg (ScanPhase.fwd a) j) u).state ≠
          some (.done b)) ∧
      (∀ u ≤ 2 * fs[j].length + 2, ∀ i,
        |((scanTM 1 0 (scanFold δ) scanKeep a).runFrom (cfg (ScanPhase.fwd a) j) u).workTapePos i -
          d.workTapePos i| ≤ ((L + 1 : ℕ) : ℤ)) := by
    obtain ⟨hr, hc, hh⟩ := scanTM_run_ofCfg 0 (scanFold δ) scanKeep a fs[j]
      (cfg (ScanPhase.fwd a) j) rfl (hword j hj)
    rw [scanResult_fold] at hr
    refine ⟨hr.trans ?_, hc, ?_⟩
    · apply Cfg.ext <;> try rfl
      funext i z
      change (if i = 0 ∧ _ ∧ _ then _ else _) = d.workTapes i z
      by_cases hi : i = 0 ∧ (cfg (ScanPhase.fwd a) j).workTapePos i ≤ z ∧
          z < (cfg (ScanPhase.fwd a) j).workTapePos i + (fs[j].length : ℤ)
      · rw [if_pos hi]
        obtain ⟨rfl, hl, hu⟩ := hi
        have hw := hword j hj (z - (cfg (ScanPhase.fwd a) j).workTapePos 0)
          (by dsimp [cfg] at *; omega) (by dsimp [cfg] at *; omega)
        simpa [cfg] using hw.symm
      · rw [if_neg hi]
    · intro u hu i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have hh' := hh 0 u hu
      simp only [Finset.mem_Icc] at hh'
      have hb := fieldOffset_add_length_le fs j hj
      dsimp only [cfg] at hh' ⊢
      rw [abs_le]
      dsimp [L] at *
      constructor <;> omega
  let fstate (q : Option Q) (j : ℕ) (_hj : j ≤ k + 2) : S :=
    if h : j < k + 2 then ⟨.forward q ⟨j, h⟩, .run⟩ else ⟨.tag q, .fwd none⟩
  let bstate (b : Bool) (j : ℕ) (hj : j ≤ k + 2) : S :=
    if h : 0 < j then ⟨.backward b ⟨j - 1, by omega⟩, .run⟩ else ⟨.verdict b, .run⟩
  have hskip (q : Option Q) (j : ℕ) (hj : j < k + 2) :
      RecordRun R yes no d.workTapePos (L + 1)
        (cfg (fstate q j (by omega)) j) (cfg (fstate q (j + 1) (by omega)) (j + 1))
        (fs[j].length + 2) := by
    have hjf : j < fs.length := by omega
    have hnext : j + 1 < fs.length := by omega
    obtain ⟨hr, hc, hh⟩ := skipTM_run_ofCfg 0 fs[j] (cfg SeekPhase.run j) rfl
      (fun p hl hu => hword j hjf p (by omega) hu)
    have he : (skipTM 1 (0 : Fin 1)).runFrom (cfg SeekPhase.run j) (fs[j].length + 1) =
        cfg SeekPhase.done (j + 1) := by
      rw [hr]
      apply Cfg.ext <;> try rfl
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [cfg, Function.update_self, fieldOffset_succ fs j hjf, Nat.cast_add,
        Nat.cast_one]
      omega
    have hp := phaseHostTM_run (recordTestRows P) entry recordTestNext
      (.forward q ⟨j, hj⟩) (cfg SeekPhase.run j) (cfg SeekPhase.done (j + 1))
      (fs[j].length + 1) he .done rfl (fstate q (j + 1) (by omega))
      (by by_cases h : j + 1 < k + 2 <;> simp [recordTestNext, fstate, h])
      (by
        intro u hu z hz
        cases z with
        | done => exact False.elim (hc u hu hz)
        | run => rfl
        | gap => rfl
        | back => rfl)
    simp only [fstate, dif_pos hj] at *
    apply recordRun_tagged hp.1 hp.2 (by intro h; cases h) (by intro h; cases h) ?_
      (hhead _ _ hnext)
    intro u hu i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hs := hh 0 u hu
    simp only [Finset.mem_Icc] at hs
    have hb := fieldOffset_add_length_le fs j hjf
    dsimp only [cfg] at hs ⊢
    rw [abs_le]
    dsimp [L] at *
    constructor <;> omega
  have hbackstep (b : Bool) (j : ℕ) (hj : j < k + 2) :
      RecordRun R yes no d.workTapePos (L + 1)
        (cfg (bstate b (j + 1) (by omega)) (j + 1)) (cfg (bstate b j (by omega)) j)
        (fs[j].length + 4) := by
    have hjf : j < fs.length := by omega
    have hoff := fieldOffset_succ fs j hjf
    have hw : ∀ p : ℤ, -1 ≤ p → p ≤ (fs[j].length : ℤ) →
        (cfg SeekPhase.run (j + 1)).workTapes 0
          ((cfg SeekPhase.run (j + 1)).workTapePos 0 - fs[j].length - 1 + p) =
          FinTM.bufferTape fs[j] p := by
      intro p hl hu
      convert hword j hjf p hl hu using 1
      dsimp [cfg]
      congr 1
      push_cast [hoff]
      ring
    obtain ⟨hr, hc, hh⟩ := skipBackTM_run_ofCfg 0 fs[j] (cfg SeekPhase.run (j + 1)) rfl hw
    have he : (skipBackTM 1 (0 : Fin 1)).runFrom (cfg SeekPhase.run (j + 1))
        (fs[j].length + 3) = cfg SeekPhase.done j := by
      rw [hr]
      apply Cfg.ext <;> try rfl
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [cfg, Function.update_self, hoff, Nat.cast_add, Nat.cast_one]
      omega
    have hp := phaseHostTM_run (recordTestRows P) entry recordTestNext
      (.backward b ⟨j, hj⟩) (cfg SeekPhase.run (j + 1)) (cfg SeekPhase.done j)
      (fs[j].length + 3) he .done rfl (bstate b j (by omega))
      (by cases j <;> simp [recordTestNext, bstate])
      (by
        intro u hu z hz
        cases z with
        | done => exact False.elim (hc u hu hz)
        | run => rfl
        | gap => rfl
        | back => rfl)
    simp only [bstate, Nat.zero_lt_succ, dif_pos] at *
    apply recordRun_tagged hp.1 hp.2 (by intro h; cases h) (by intro h; cases h) ?_
      (hhead _ _ hjf)
    intro u hu i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hs := hh 0 u hu
    simp only [Finset.mem_Icc] at hs
    have hb := fieldOffset_add_length_le fs (j + 1) (by omega)
    dsimp only [cfg] at hs ⊢
    have hoff' : (fieldOffset fs (j + 1) : ℤ) = fieldOffset fs j + fs[j].length + 1 := by
      rw [hoff]; push_cast; ring
    rw [abs_le]
    dsimp [L] at *
    constructor <;> omega
  have hforward (q : Option Q) : ∀ j (hj : j ≤ k + 2),
      ∃ t ≤ j * B, RecordRun R yes no d.workTapePos (L + 1)
        (cfg (fstate q 0 (by omega)) 0) (cfg (fstate q j hj) j) t := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨0, by omega, recordRun_zero _ _ _ _ _ _ (hhead _ 0 (by omega))⟩
    | succ j ih =>
      intro hj
      obtain ⟨t, ht, hr⟩ := ih (by omega)
      have hb := fieldOffset_add_length_le fs j (by omega)
      refine ⟨t + (fs[j].length + 2), ?_, recordRun_trans hr (hskip q j (by omega))⟩
      dsimp [B, L] at *
      rw [Nat.succ_mul]
      omega
  have hbackward (b : Bool) : ∀ j (hj : j ≤ k + 2),
      ∃ t ≤ j * B, RecordRun R yes no d.workTapePos (L + 1)
        (cfg (bstate b j hj) j) (cfg (⟨.verdict b, .run⟩ : S) 0) t := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨0, by omega, recordRun_zero _ _ _ _ _ _ (hhead _ 0 (by omega))⟩
    | succ j ih =>
      intro hj
      obtain ⟨t, ht, hr⟩ := ih (by omega)
      have hb := fieldOffset_add_length_le fs j (by omega)
      refine ⟨(fs[j].length + 4) + t, ?_, recordRun_trans (hbackstep b j (by omega)) hr⟩
      dsimp [B, L] at *
      rw [Nat.succ_mul]
      omega
  have hsword : fs[0] = [RecSym.st c.state] := rfl
  have htword : fs[k + 2] = [RecSym.tag τ] := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem (by omega)]
    simp [fs, cfgRecord]
  have hstate : RecordRun R yes no d.workTapePos (L + 1)
      (cfg entry 0) (cfg (fstate c.state 0 (by omega)) 0) 5 := by
    obtain ⟨hr, hc, hh⟩ := hfold (recordReadState (Q := Q) (T := T)) none 0 (by omega)
    simp only [hsword, List.length_singleton, List.foldl_cons, List.foldl_nil,
      recordReadState] at hr hc hh
    have hp := phaseHostTM_run (recordTestRows P) entry recordTestNext .state
      (cfg (ScanPhase.fwd (none : Option (Option Q))) 0)
      (cfg (ScanPhase.done (some c.state)) 0) 4 hr (.done (some c.state)) rfl
      (fstate c.state 0 (by omega)) (by simp [recordTestNext, fstate])
      (by
        intro u hu z hz
        cases z with
        | fwd a => rfl
        | bwd a => rfl
        | done a => exact False.elim (hc u hu a hz))
    exact recordRun_tagged hp.1 hp.2 (by intro h; cases h) (by intro h; cases h)
      hh (hhead _ 0 (by omega))
  have htag : RecordRun R yes no d.workTapePos (L + 1)
      (cfg (fstate c.state (k + 2) le_rfl) (k + 2))
      (cfg (bstate (P c.state τ) (k + 2) le_rfl) (k + 2)) 5 := by
    obtain ⟨hr, hc, hh⟩ := hfold (recordReadTag P c.state) none (k + 2) (by omega)
    simp only [htword, List.length_singleton, List.foldl_cons, List.foldl_nil,
      recordReadTag] at hr hc hh
    have hp := phaseHostTM_run (recordTestRows P) entry recordTestNext (.tag c.state)
      (cfg (ScanPhase.fwd (none : Option Bool)) (k + 2))
      (cfg (ScanPhase.done (some (P c.state τ))) (k + 2)) 4 hr
      (.done (some (P c.state τ))) rfl (bstate (P c.state τ) (k + 2) le_rfl)
      (by simp [recordTestNext, bstate])
      (by
        intro u hu z hz
        cases z with
        | fwd a => rfl
        | bwd a => rfl
        | done a => exact False.elim (hc u hu a hz))
    simpa only [fstate, lt_self_iff_false, dif_neg] using
      (recordRun_tagged hp.1 hp.2 (by intro h; cases h) (by intro h; cases h)
        hh (hhead _ (k + 2) (by omega)))
  obtain ⟨tf, htf, hf⟩ := hforward c.state (k + 2) le_rfl
  obtain ⟨tb, htb, hb⟩ := hbackward (P c.state τ) (k + 2) le_rfl
  have hall := recordRun_trans (recordRun_trans (recordRun_trans hstate hf) htag) hb
  have hstart : cfg entry 0 = d := by
    apply Cfg.ext
    · exact hd.symm
    · rfl
    · rfl
    · funext i; simp [cfg, fieldOffset]
    · rfl
  rw [hstart] at hall
  refine ⟨((5 + tf) + 5) + tb, ?_, hall.2.1, ?_, ?_⟩
  · change ((5 + tf) + 5) + tb ≤ 6 * (2 * (k + 2) + 2) * (L + 1)
    have hsmall : 5 ≤ B := by dsimp [B]; omega
    calc
      ((5 + tf) + 5) + tb ≤ (B + (k + 2) * B) + B + (k + 2) * B := by omega
      _ = 6 * (2 * (k + 2) + 2) * (L + 1) := by dsimp [B]; ring
  · intro u hu i
    have hh := hall.2.2 u hu i
    have hscale : L + 1 ≤ 6 * (2 * (k + 2) + 2) * (L + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact le_trans hh (by exact_mod_cast hscale)
  · rw [hall.1]
    apply Cfg.ext
    · cases h : P c.state τ <;> simp [cfg, yes, no]
    · rfl
    · rfl
    · funext i; simp [cfg, fieldOffset]
    · rfl

end Turing
