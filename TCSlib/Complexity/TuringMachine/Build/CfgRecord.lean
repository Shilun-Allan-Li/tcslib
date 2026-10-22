/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.SymbolLift
import TCSlib.Complexity.TuringMachine.Build.InputCall
import TCSlib.Complexity.TuringMachine.Build.Contract

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

**Status: proved §12.8 fill C (continuation 3 status update).** The pure decoding
facts and all three record rows are proved. The catalog, scan and input-seek rows
cited by their proofs are also proved. No public result or private helper in
this module is admitted.

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
* `Turing.Cfg.inWindow_init` — the initial configuration is in every window.
* `Turing.cfgRecord_inj` — on windowed configurations, records agree exactly
  when configuration cores and tags do (proved; fill-C status update).
* `Turing.recordValid_iff` — validity as a field-by-field shape condition
  (proved; fill-C status update).
* `Turing.exists_recordStepTM`, `Turing.exists_recordEqTM`,
  `Turing.exists_recordTestTM` — the record rows R8.7: one simulated step, record
  equality, and a test of the state and tag (fill-C continuation 3 status update:
  all three are proved).
* `Turing.recordAt_iff`, `Turing.record_pos_lt` — reading a record and the position-width
  bound, the specification API (user, 2026-10-16).

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

/-- The digit embedding sends a bit to its digit symbol: `RecSym.digitEmb Q T b = RecSym.digit b`
(the specification API, the briefs' pre-ship inventories, 2026-10-16). -/
theorem RecSym.digitEmb_apply (Q T : Type) (b : Bool) : RecSym.digitEmb Q T b = RecSym.digit b :=
  rfl

/-! ### The record -/

/-- **Fixed-width binary digits** (design §12.8a §2): the `w` low bits of `v`,
least significant first. -/
def binDigits (w v : ℕ) : List Bool := (List.range w).map v.testBit

/-- The `w` low bits of `v`, least significant first: `binDigits w v = (range w).map v.testBit` (the
specification API, the briefs' pre-ship inventories, 2026-10-16). -/
theorem binDigits_eq (w v : ℕ) : binDigits w v = (List.range w).map v.testBit :=
  rfl

/-- **The input-position width** (design §12.8a §2) at input length `n`: the
bit length of `n + 1`, so that `2 ^ posWidth n > n + 1` and every input
position `0, …, n + 1` has a distinct `Turing.binDigits` code. -/
def posWidth (n : ℕ) : ℕ := (Nat.bits (n + 1)).length

/-- The input-position width is the bit length of `n + 1`: `posWidth n = (Nat.bits (n + 1)).length`
(the specification API, the briefs' pre-ship inventories, 2026-10-16). -/
theorem posWidth_eq (n : ℕ) : posWidth n = (Nat.bits (n + 1)).length :=
  rfl

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

/-- Every native input position is strictly below the power of two specified by its width:
`n + 2 ≤ 2 ^ posWidth n`. (Public since the specification API, user 2026-10-16.)

**Proof sketch.** `posWidth n` is the bit length of `n + 1`, which is its `Nat.size`. -/
theorem record_pos_lt (n : ℕ) : n + 1 < 2 ^ posWidth n := by
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

/-- **Reading a record** (the specification API, user 2026-10-16): `RecordAt d r fs` holds
exactly when, at every offset `p` with `-1 ≤ p ≤ |joinFields fs|`, the cell of tape `r` at its
head plus `p` holds `fieldsTape fs p`: the layout's cells, with blank delimiters at offsets `-1`
and `|joinFields fs|`. Cells outside that interval are unconstrained. -/
theorem recordAt_iff {K : ℕ} {Γ S : Type*} {x : List Γ} (d : Cfg K Γ S x) (r : Fin K)
    (fs : List (List Γ)) :
    RecordAt d r fs ↔ ∀ p : ℤ, -1 ≤ p → p ≤ ((joinFields fs).length : ℤ) →
      d.workTapes r (d.workTapePos r + p) = fieldsTape fs p :=
  Iff.rfl

/-! ### R8.7 — the record rows -/

/-- The shared segment specialized to the record verdicts and the common head box. -/
private abbrev RecordSeg {K : ℕ} {Γ S : Type} {x : List Γ} (R : MultiTapeTM K Γ S)
    (yes no : S) (base : Fin K → ℤ) (radius : ℕ) (a b : Cfg K Γ S x) (t : ℕ) : Prop :=
  Segment R {some yes, some no}
    (HeadBox (fun j => base j - radius) (fun j => base j + radius)) a b t

/-- The record's radius condition is the shared interval box, read through its API. -/
private theorem record_headBox_iff {K : ℕ} (base : Fin K → ℤ) (radius : ℕ)
    (p : Fin K → ℤ) :
    HeadBox (fun j => base j - radius) (fun j => base j + radius) p ↔
      ∀ j, |p j - base j| ≤ (radius : ℤ) := by
  rw [headBox_iff]
  apply forall_congr'
  intro j
  rw [Finset.mem_Icc, abs_le]
  omega

/-- Reading a record segment in the radius form required by the frozen public rows.
This is only the shared segment's characterization and the box/radius equivalence. -/
private theorem recordSeg_iff {K : ℕ} {Γ S : Type} {x : List Γ}
    {R : MultiTapeTM K Γ S} {yes no : S} {base : Fin K → ℤ} {radius : ℕ}
    {a b : Cfg K Γ S x} {t : ℕ} :
    RecordSeg R yes no base radius a b t ↔
      R.runFrom a t = b ∧
        (∀ u < t, (R.runFrom a u).state ≠ some yes ∧ (R.runFrom a u).state ≠ some no) ∧
        ∀ u ≤ t, ∀ j, |(R.runFrom a u).workTapePos j - base j| ≤ (radius : ℤ) := by
  simp only [RecordSeg, segment_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or, record_headBox_iff]

/-- A larger radius contains the old head box, for weakening with `Segment.mono`. -/
private theorem record_headBox_mono {K : ℕ} {base : Fin K → ℤ} {r r' : ℕ}
    (hr : r ≤ r') (p : Fin K → ℤ)
    (hp : HeadBox (fun j => base j - r) (fun j => base j + r) p) :
    HeadBox (fun j => base j - r') (fun j => base j + r') p := by
  rw [record_headBox_iff] at hp ⊢
  exact fun j => le_trans (hp j) (by exact_mod_cast hr)

/-- Read a one-exit row contract as its run equation, first-exit cut and per-tape head
envelope. The clauses are the shared segment reader's, with the exit set read as its single
member and the head box read tape by tape; nothing about the row is retraced. -/
private theorem recordStep_contract_clauses {K : ℕ} {Γ S : Type} {x : List Γ} {ι : Type}
    {R : MultiTapeTM K Γ S} {entry done : S} (C : Contract R entry {some done} ι x)
    (i : ι) (d : Cfg K Γ S x) (hd : d.state = some entry) (hp : C.pre i d) :
    R.runFrom d (C.time i d) = C.post i d ∧
      (∀ u < C.time i d, (R.runFrom d u).state ≠ some done) ∧
      ∀ (j : Fin K) (u : ℕ), u ≤ C.time i d →
        (R.runFrom d u).workTapePos j ∈ Finset.Icc (C.lo i d j) (C.hi i d j) := by
  obtain ⟨hrun, hcut, henv⟩ := (segment_iff _ _ _ _ _ _).mp (C.segment i d hd hp)
  exact ⟨hrun, fun u hu hs => hcut u hu (by rw [hs]; exact Set.mem_singleton_iff.mpr rfl),
    fun j u hu => (headBox_iff _ _ _).mp (henv u hu) j⟩

/-- Read a row contract whose exits are a verdict family's range, as its run equation,
first-exit cut against every verdict, and per-tape head envelope, the same way as the
one-exit reader. -/
private theorem recordStep_contract_clauses_range {K : ℕ} {Γ S A : Type} {x : List Γ}
    {ι : Type} {R : MultiTapeTM K Γ S} {entry : S} {f : A → S}
    (C : Contract R entry (Set.range fun a => some (f a)) ι x)
    (i : ι) (d : Cfg K Γ S x) (hd : d.state = some entry) (hp : C.pre i d) :
    R.runFrom d (C.time i d) = C.post i d ∧
      (∀ u < C.time i d, ∀ a : A, (R.runFrom d u).state ≠ some (f a)) ∧
      ∀ (j : Fin K) (u : ℕ), u ≤ C.time i d →
        (R.runFrom d u).workTapePos j ∈ Finset.Icc (C.lo i d j) (C.hi i d j) := by
  obtain ⟨hrun, hcut, henv⟩ := (segment_iff _ _ _ _ _ _).mp (C.segment i d hd hp)
  exact ⟨hrun, fun u hu a hs => hcut u hu ⟨a, hs.symm⟩,
    fun j u hu => (headBox_iff _ _ _).mp (henv u hu) j⟩

/-- The sweep rows' endpoint as the record literal the proofs below match on, assembled
from its published field equations. -/
private theorem recordStep_sweepPost_eq {K : ℕ} {Γ S : Type} {x : List Γ} (done : S)
    (a : Fin K) (v : List Γ → Cfg K Γ S x → Fin K → ℤ → Option Γ) (w : List Γ)
    (d : Cfg K Γ S x) :
    sweepPost done a v w d = { d with
      state := some done
      workTapes := fun j q =>
        if j = a ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then v w d j q
        else d.workTapes j q } := by
  apply Cfg.ext
  · rw [sweepPost_state]
  · rw [sweepPost_inputPos]
  · funext j q
    rw [sweepPost_workTapes]
  · funext j
    rw [sweepPost_workTapePos]
  · rw [sweepPost_output]

/-- The seek rows' endpoint as the record literal the proofs below match on, assembled
from its published field equations. -/
private theorem recordStep_seekPost_eq {K : ℕ} {Γ S : Type} {x : List Γ} (done : S)
    (i : Fin K) (p : ℤ) (d : Cfg K Γ S x) :
    seekPost done i p d =
      { d with state := some done, workTapePos := Function.update d.workTapePos i p } := by
  apply Cfg.ext
  · rw [seekPost_state]
  · rw [seekPost_inputPos]
  · funext j q
    rw [seekPost_workTapes]
  · funext j
    rw [seekPost_workTapePos]
  · rw [seekPost_output]

/-- A renamed configuration equals any target that shares its four data fields and carries
the renamed state, read field by field through the renaming's published equations. -/
private theorem recordStep_mapState_eq {K : ℕ} {Γ S S' : Type} {x : List Γ}
    (c : Cfg K Γ S x) (f : S → S') (d : Cfg K Γ S' x)
    (hs : c.state.map f = d.state) (hi : c.inputPos = d.inputPos)
    (hw : c.workTapes = d.workTapes) (hp : c.workTapePos = d.workTapePos)
    (ho : c.output = d.output) : c.mapState f = d := by
  apply Cfg.ext
  · rw [Cfg.mapState_state, hs]
  · rw [Cfg.mapState_inputPos, hi]
  · funext j q
    rw [Cfg.mapState_workTapes, hw]
  · funext j
    rw [Cfg.mapState_workTapePos, hp]
  · rw [Cfg.mapState_output, ho]

/-- Renaming the states of an explicit configuration record maps its state and keeps the
other four fields, as a rewrite rule for the endpoint conversions below. -/
private theorem recordStep_mapState_mk {K : ℕ} {Γ S S' : Type} {x : List Γ}
    (f : S → S') (st : Option S) (ip : Fin (x.length + 2))
    (wt : Fin K → ℤ → Option Γ) (wp : Fin K → ℤ) (o : List Γ) :
    (Cfg.mapState f ⟨st, ip, wt, wp, o⟩ : Cfg K Γ S' x) = ⟨st.map f, ip, wt, wp, o⟩ :=
  recordStep_mapState_eq _ _ _ rfl rfl rfl rfl rfl

/-- A tagged phase cannot be a verdict at a different index. -/
private theorem record_tag_ne {K : ℕ} {Γ I : Type} {Ph : I → Type} {x : List Γ}
    (i : I) (v : Σ i, Ph i) (hi : i ≠ v.1) (c : Cfg K Γ (Ph i) x) :
    (c.mapState (Sigma.mk i)).state ≠ some v := by
  cases hs : c.state with
  | none => simp [Cfg.mapState_state, hs]
  | some s =>
    intro h
    have he : (⟨i, s⟩ : Σ i, Ph i) = v := by simpa [Cfg.mapState_state, hs] using h
    exact hi (congrArg Sigma.fst he)

/-- Package the tagged prefix and dispatched endpoint supplied by `phaseHostTM_run`.
No transition or phase-host induction is repeated here. -/
private theorem recordStep_tagged_segment {K : ℕ} {Γ I : Type} {Ph : I → Type} {x : List Γ}
    {R : MultiTapeTM K Γ (Σ i, Ph i)} {yes no : Σ i, Ph i}
    {base : Fin K → ℤ} {radius : ℕ} {a b : Cfg K Γ (Σ i, Ph i) x}
    {i : I} {M : MultiTapeTM K Γ (Ph i)} {c : Cfg K Γ (Ph i) x} {t : ℕ}
    (hp : ∀ u ≤ t, R.runFrom a u = (M.runFrom c u).mapState (Sigma.mk i))
    (he : R.runFrom a (t + 1) = b) (hy : i ≠ yes.1) (hn : i ≠ no.1)
    (hb : ∀ u ≤ t, ∀ j, |(M.runFrom c u).workTapePos j - base j| ≤ (radius : ℤ))
    (hend : ∀ j, |b.workTapePos j - base j| ≤ (radius : ℤ)) :
    RecordSeg R yes no base radius a b (t + 1) := by
  rw [recordSeg_iff]
  refine ⟨he, ?_, ?_⟩
  · intro u hu
    rw [hp u (by omega)]
    exact ⟨record_tag_ne i yes hy _, record_tag_ne i no hn _⟩
  · intro u hu j
    by_cases ht : u ≤ t
    · rw [hp u ht, Cfg.mapState_workTapePos]
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
      rw [counterLoopOrbit, roundOrbit, Function.iterate_succ_apply']
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
  rw [counterLoopOrbit, roundOrbit, Function.iterate_succ_apply']
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
use the same R1 transport on dedicated digit banks. No lifted Bool row selects the record
tape; the rich scans and copies do select tape 0. -/
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
position, and have work-head radius one. This is the first `RecordSeg` of the construction.
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
    RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos 1 d
      {d with state := some ⟨⟨.stateSkip, {state := q}⟩, .run⟩} 5 := by
  let i : RecordStepIndex k Q T := ⟨.state, {}⟩
  let c : Cfg 4 (RecSym Q T) (ScanPhase (Option Q)) x :=
    ⟨some (.fwd none), d.inputPos, d.workTapes, d.workTapePos, d.output⟩
  let δ : Option Q → RecSym Q T → Option Q := fun _ γ => match γ with
    | .st a => a | _ => none
  obtain ⟨hrow, hcut, hheads⟩ := recordStep_contract_clauses_range
    (scanTM_contract (0 : Fin 4) (scanFold δ) scanKeep none x) [RecSym.st q] c rfl
    (by rw [scanTM_contract_pre]; exact hw)
  rw [scanTM_contract_time, scanTM_contract_post] at hrow
  simp only [scanTM_contract_time] at hcut hheads
  simp only [scanTM_contract_lo, scanTM_contract_hi] at hheads
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
  have hin : c.mapState (Sigma.mk i) = d :=
    recordStep_mapState_eq _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
  have hout : ({c with state := some (.done q)} : Cfg 4 (RecSym Q T) (ScanPhase (Option Q)) x).mapState
      (fun _ => out) = {d with state := some out} :=
    recordStep_mapState_eq _ _ _ rfl rfl rfl rfl rfl
  rw [hin] at phase
  have hend : (recordStepMachine M upd seek start finish).runFrom d 5 =
      {d with state := some out} := by
    simpa only [hout] using phase.2
  apply recordStep_tagged_segment phase.1 hend
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
    · rw [if_neg hj, if_neg hj] at hh
      have heq := le_antisymm (Finset.mem_Icc.mp hh).2 (Finset.mem_Icc.mp hh).1
      change |((recordStepRows M upd seek i).runFrom c u).workTapePos j - d.workTapePos j| ≤ 1
      rw [heq]
      simp [c]
  · intro j
    simp

/-- Package a record-step phase by the public host theorem and the inherited segment
bookkeeping. The endpoint radius follows from the last row prefix, since dispatch is
stationary. No host transition argument is repeated.
**Proof sketch.** Apply `phaseHostTM_run`; exclude both verdicts by their stage indices,
then use `recordStep_tagged_segment` with the row's trajectory bound. -/
private theorem recordStep_phase_run {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List (RecSym Q T)}
    (i : RecordStepIndex k Q T) (hi : ∀ b, i.1 ≠ .verdict b)
    (c c' : Cfg 4 (RecSym Q T) (recordStepPhase (S := S) i) x)
    (t : ℕ) (hr : (recordStepRows M upd seek i).runFrom c t = c')
    (s' : recordStepPhase (S := S) i) (hs : c'.state = some s')
    (out : RecordStepControl k Q T S) (ho : recordStepNext M start finish i s' = some out)
    (hcut : ∀ u < t, ∀ a, ((recordStepRows M upd seek i).runFrom c u).state = some a →
      recordStepNext M start finish i a = none)
    (base : Fin 4 → ℤ) (radius : ℕ)
    (hh : ∀ u ≤ t, ∀ j,
      |((recordStepRows M upd seek i).runFrom c u).workTapePos j - base j| ≤ (radius : ℤ)) :
    RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) base radius
      (c.mapState (Sigma.mk i)) (c'.mapState (fun _ => out)) (t + 1) := by
  obtain ⟨hp, he⟩ := phaseHostTM_run (recordStepRows M upd seek) recordStepEntry
    (recordStepNext M start finish) i c c' t hr s' hs out ho hcut
  exact recordStep_tagged_segment hp he
    (fun h => hi true (congrArg Prod.fst h))
    (fun h => hi false (congrArg Prod.fst h)) hh (fun j => by
      simpa only [hr, Cfg.mapState_workTapePos] using hh t le_rfl j)

/-- A scan whose pure result retains its word changes only the accumulator state.
This removes the identity rewrite in the public scan endpoint once for all read phases.
**Proof sketch.** Read the public scan contract through its field equations; inside its
write interval use the entry word hypothesis, and outside use the unchanged frame. Keep
its cut and head bounds. -/
private theorem recordStep_scan_preserves {A Γ : Type} {x : List Γ}
    (i : Fin 4) (δf δb : A → Γ → A × Γ) (a b : A) (w : List Γ)
    (c : Cfg 4 Γ (ScanPhase A) x) (hc : c.state = some (.fwd a))
    (hw : ∀ z : ℤ, -1 ≤ z → z ≤ (w.length : ℤ) →
      c.workTapes i (c.workTapePos i + z) = FinTM.bufferTape w z)
    (hf : scanResult δf δb a w = (b, w)) :
    (scanTM 4 i δf δb a).runFrom c (2 * w.length + 2) =
      {c with state := some (.done b)} ∧
    (∀ u < 2 * w.length + 2, ∀ v,
      ((scanTM 4 i δf δb a).runFrom c u).state ≠ some (.done v)) ∧
    (∀ j u, u ≤ 2 * w.length + 2 →
      if j = i then ((scanTM 4 i δf δb a).runFrom c u).workTapePos j ∈
        Finset.Icc (c.workTapePos j - 1) (c.workTapePos j + (w.length : ℤ))
      else ((scanTM 4 i δf δb a).runFrom c u).workTapePos j = c.workTapePos j) := by
  obtain ⟨he, ht, hh⟩ := recordStep_contract_clauses_range
    (scanTM_contract i δf δb a x) w c hc (by rw [scanTM_contract_pre]; exact hw)
  rw [scanTM_contract_time, scanTM_contract_post] at he
  simp only [scanTM_contract_time] at ht hh
  refine ⟨he.trans ?_, ht, ?_⟩
  · rw [hf]
    apply Cfg.ext <;> try rfl
    funext j z
    dsimp only
    split
    next h =>
      obtain ⟨rfl, hlo, hhi⟩ := h
      simpa using (hw (z - c.workTapePos j) (by omega) (by omega)).symm
    next => rfl
  · intro j u hu
    have h := hh j u hu
    simp only [scanTM_contract_lo, scanTM_contract_hi] at h
    by_cases hj : j = i
    · rw [if_pos hj]
      rw [if_pos hj, if_pos hj] at h
      exact h
    · rw [if_neg hj]
      rw [if_neg hj, if_neg hj] at h
      rw [Finset.mem_Icc] at h
      exact le_antisymm h.2 h.1

/-- Snapshots for reading the record: the record and frame stay intact, B and D carry
specified globally delimited words, and only the record head is displaced. -/
private def recordStepSnapshot {Γ A P : Type} {x : List Γ}
    (d : Cfg 4 Γ P x) (q : A) (p : ℤ) (b e : List Γ) : Cfg 4 Γ A x :=
  ⟨some q, d.inputPos,
    (fun j z => if j = 1 then FinTM.bufferTape b (z - d.workTapePos j)
      else if j = 3 then FinTM.bufferTape e (z - d.workTapePos j) else d.workTapes j z),
    (fun j => d.workTapePos j + if j = 0 then p else 0), d.output⟩

/-- With empty scratch words and zero displacement, the snapshot is its blank-scratch
entry configuration with only the named state changed. -/
private theorem recordStepSnapshot_empty {Γ A P : Type} {x : List Γ}
    (d : Cfg 4 Γ P x) (q : A)
    (hblank : ∀ j : Fin 4, j ≠ 0 → ∀ z, d.workTapes j z = none) :
    recordStepSnapshot d q 0 [] [] =
      (⟨some q, d.inputPos, d.workTapes, d.workTapePos, d.output⟩ : Cfg 4 Γ A x) := by
  apply Cfg.ext <;> try rfl
  · funext j z
    dsimp [recordStepSnapshot]
    split_ifs with h1 h3
    · simp [hblank j (by subst j; decide)]
    · simp [hblank j (by subst j; decide)]
    · rfl
  · funext j
    simp [recordStepSnapshot]

/-- The first five read phases reach the position skip with both digit copies installed.
The finite data correctly records the source state and the position width/zero tests.
**Proof sketch.** Reuse the first state segment; cite skip, the read-only scan specialization
and the two framed copies. The public phase theorem intercepts each row exit. The scan's
pure result is the existing position-fold lemma, with the existing binary decoder. All
heads stay within the read record or a width-sized scratch interval. -/
private theorem recordStep_read_prefix {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List Bool}
    (s : ℕ) (c : Cfg k Bool Q x) (τ : T)
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map (RecSym.digitEmb Q T)))
    (hd : d.state = some recordStepEntry) (hrec : RecordAt d 0 (cfgRecord s c τ))
    (hblank : ∀ j : Fin 4, j ≠ 0 → ∀ z, d.workTapes j z = none) :
    let w := (binDigits (posWidth x.length) c.inputPos.val).map (RecSym.digit (Q := Q) (T := T))
    let data : RecordStepData k Q T :=
      {state := c.state, widthOne := decide (posWidth x.length = 1),
       posZero := decide (c.inputPos.val = 0)}
    RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos
      ((joinFields (cfgRecord s c τ)).length + 1) d
      (recordStepSnapshot d (⟨⟨.positionSkip, data⟩, .run⟩ : RecordStepControl k Q T S) 2 w w)
      (6 * w.length + 17) := by
  classical
  dsimp only
  let w := (binDigits (posWidth x.length) c.inputPos.val).map (RecSym.digit (Q := Q) (T := T))
  let data : RecordStepData k Q T :=
    {state := c.state, widthOne := decide (posWidth x.length = 1),
     posZero := decide (c.inputPos.val = 0)}
  let cfg := recordStepSnapshot (A := RecordStepControl k Q T S) d
  let L := (joinFields (cfgRecord s c τ)).length
  have hwlen : w.length = posWidth x.length := by simp [w, binDigits]
  have hlen : 2 + w.length ≤ L := by
    have := fieldOffset_add_length_le (cfgRecord s c τ) 1 (by simp [cfgRecord_length])
    simpa [cfgRecord, fieldOffset, w, L] using this
  have stateword : ∀ z : ℤ, -1 ≤ z → z ≤ 1 →
      d.workTapes 0 (d.workTapePos 0 + z) = FinTM.bufferTape [RecSym.st c.state] z := by
    intro z hz hu
    rw [hrec z hz (by dsimp [L] at hlen; omega)]
    simpa [cfgRecord, fieldOffset] using
      fieldsTape_field (cfgRecord s c τ) 0 (by simp [cfgRecord_length]) z hz (by simpa using hu)
  have posword : ∀ z : ℤ, -1 ≤ z → z ≤ (w.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + 2 + z) = FinTM.bufferTape w z := by
    intro z hz hu
    rw [add_assoc, hrec (2 + z) (by omega) (by dsimp [L] at hlen; omega)]
    simpa [cfgRecord, fieldOffset, w] using
      fieldsTape_field (cfgRecord s c τ) 1 (by simp [cfgRecord_length]) z hz
        (by simpa [cfgRecord, w] using hu)
  have initial (q : RecordStepControl k Q T S) : cfg q 0 [] [] = {d with state := some q} :=
    recordStepSnapshot_empty d q hblank
  have h0 := recordStep_state_run M upd seek start finish d hd c.state stateword
  have h0' : RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1) d
      (cfg (⟨⟨.stateSkip, {state := c.state}⟩, .run⟩ : RecordStepControl k Q T S) 0 [] []) 5 := by
    rw [initial]
    exact Segment.mono h0 (fun _ hx => hx) (record_headBox_mono (by omega))
  have h1 : RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
      (cfg (⟨⟨.stateSkip, {state := c.state}⟩, .run⟩ : RecordStepControl k Q T S) 0 [] [])
      (cfg (⟨⟨.position, {state := c.state}⟩, .fwd (0, true)⟩ : RecordStepControl k Q T S) 2 [] []) 3 := by
    let a := recordStepSnapshot d SeekPhase.run 0 [] []
    obtain ⟨he, ht, hh⟩ := recordStep_contract_clauses (skipTM_contract (0 : Fin 4) _)
      [RecSym.st c.state] a rfl
      (by
        rw [skipTM_contract_pre]
        intro z hz hu
        simpa [a, recordStepSnapshot] using stateword z (by omega) (by simpa using hu))
    rw [skipTM_contract_time, skipTM_contract_post, recordStep_seekPost_eq] at he
    simp only [skipTM_contract_time] at ht hh
    have hout : (skipTM 4 0).runFrom a 2 = recordStepSnapshot d SeekPhase.done 2 [] [] := by
      refine he.trans ?_
      apply Cfg.ext <;> try rfl
      funext j
      by_cases hj : j = 0
      · subst j; simp [a, recordStepSnapshot]; omega
      · simp [a, recordStepSnapshot, hj, Function.update_of_ne]
    have phase := recordStep_phase_run M upd seek start finish
      ⟨.stateSkip, {state := c.state}⟩ (by intro b h; cases h) a
      (recordStepSnapshot d SeekPhase.done 2 [] []) 2 hout .done rfl
      (⟨⟨.position, {state := c.state}⟩, .fwd (0, true)⟩ : RecordStepControl k Q T S) rfl
      (by
        intro u hu q hq
        cases q with
        | done => exact (ht u hu hq).elim
        | run => rfl
        | gap => rfl
        | back => rfl)
      d.workTapePos (L + 1) (by
        intro u hu j
        have h := hh j u hu
        simp only [skipTM_contract_lo, skipTM_contract_hi] at h
        by_cases hj : j = 0
        · subst j
          simp only [↓reduceIte, Finset.mem_Icc] at h
          dsimp [a, recordStepSnapshot, recordStepRows] at h ⊢
          rw [abs_le]; constructor <;> omega
        · rw [if_neg hj] at h
          rw [Finset.mem_Icc] at h
          have heq := le_antisymm h.2 h.1
          change |((skipTM 4 0).runFrom a u).workTapePos j - d.workTapePos j| ≤ _
          rw [heq]
          simp [a, recordStepSnapshot]
          omega)
    exact phase
  have h2 : RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
      (cfg (⟨⟨.position, {state := c.state}⟩, .fwd (0, true)⟩ : RecordStepControl k Q T S) 2 [] [])
      (cfg (⟨⟨.copyB, data⟩, .sweep⟩ : RecordStepControl k Q T S) 2 [] []) (2 * w.length + 3) := by
    let a := recordStepSnapshot d (ScanPhase.fwd ((0 : Fin 3), true)) 2 [] []
    let result : Fin 3 × Bool := (⟨min 2 (posWidth x.length), by omega⟩, decide (c.inputPos.val = 0))
    have hvalue := record_digits_value (posWidth x.length) c.inputPos.val
      (lt_of_le_of_lt (by have := c.inputPos.isLt; omega) (record_pos_lt x.length))
    have hfold : scanResult (scanFold recordStepPosFold) scanKeep (0, true) w = (result, w) := by
      dsimp only [w]
      rw [recordStep_position_fold, hvalue]
      simp [result, binDigits]
    obtain ⟨he, ht, hh⟩ := recordStep_scan_preserves 0 (scanFold recordStepPosFold) scanKeep
      (0, true) result w a rfl (by
        intro z hz hu
        simpa [a, recordStepSnapshot] using posword z hz hu) hfold
    have hout : {{state := c.state : RecordStepData k Q T} with
        widthOne := result.1 == 1, posZero := result.2} = data := by
      have hw : ((⟨min 2 (posWidth x.length), by omega⟩ : Fin 3) == 1) =
          decide (posWidth x.length = 1) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, Fin.ext_iff, Fin.val_one, decide_eq_true_eq]
        omega
      simp only [result, hw]
      rfl
    have phase := recordStep_phase_run M upd seek start finish
      ⟨.position, {state := c.state}⟩ (by intro b h; cases h) a
      {a with state := some (.done result)} (2 * w.length + 2) he (.done result) rfl
      (⟨⟨.copyB, data⟩, .sweep⟩ : RecordStepControl k Q T S)
      (by exact congrArg (fun e : RecordStepData k Q T =>
        some (⟨⟨.copyB, e⟩, .sweep⟩ : RecordStepControl k Q T S)) hout)
      (by
        intro u hu q hq
        cases q with
        | done v => exact (ht u hu v hq).elim
        | fwd _ => rfl
        | bwd _ => rfl)
      d.workTapePos (L + 1) (by
        intro u hu j
        have h := hh j u hu
        by_cases hj : j = 0
        · subst j
          simp only [↓reduceIte, Finset.mem_Icc] at h
          dsimp [a, recordStepSnapshot, recordStepRows] at h ⊢
          rw [abs_le]; constructor <;> omega
        · rw [if_neg hj] at h
          change |((scanTM 4 0 (scanFold recordStepPosFold) scanKeep (0, true)).runFrom a u).workTapePos j - d.workTapePos j| ≤ _
          rw [h]
          simp [a, recordStepSnapshot, hj]
          omega)
    exact phase
  have copying (dst : Fin 4) (hdst : dst = 1 ∨ dst = 3)
      (b e : List (RecSym Q T)) (hb : dst = 1 → b = []) (he : dst = 3 → e = []) :
      let a := recordStepSnapshot d SweepPhase.sweep 2 b e
      (copyTM 4 0 dst).runFrom a (2 * w.length + 2) =
        recordStepSnapshot d SweepPhase.done 2 (if dst = 1 then w else b) (if dst = 3 then w else e) ∧
      (∀ u < 2 * w.length + 2, ((copyTM 4 0 dst).runFrom a u).state ≠ some .done) ∧
      (∀ u ≤ 2 * w.length + 2, ∀ j,
        |((copyTM 4 0 dst).runFrom a u).workTapePos j - d.workTapePos j| ≤ ((L + 1 : ℕ) : ℤ)) := by
    dsimp only
    let a := recordStepSnapshot d SweepPhase.sweep 2 b e
    have hne : (0 : Fin 4) ≠ dst := by rcases hdst with rfl | rfl <;> decide
    obtain ⟨hr, ht, hh⟩ := recordStep_contract_clauses (copyTM_contract 0 dst hne _) w a rfl
      (by
        rw [copyTM_contract_pre]
        intro z hz hu
        simpa [a, recordStepSnapshot] using posword z hz hu)
    rw [copyTM_contract_time, copyTM_contract_post, recordStep_sweepPost_eq] at hr
    simp only [copyTM_contract_time] at ht hh
    refine ⟨hr.trans ?_, ht, ?_⟩
    · have mask (p z : ℤ) :
          (if p ≤ z ∧ z < p + (w.length : ℤ) then FinTM.bufferTape w (z - p) else none) =
            FinTM.bufferTape w (z - p) := by
        split_ifs with h
        · rfl
        · symm
          unfold FinTM.bufferTape
          split_ifs with hz
          · apply List.getElem?_eq_none
            omega
          · rfl
      apply Cfg.ext <;> try rfl
      funext j z
      rcases hdst with rfl | rfl
      · have hb := hb rfl
        subst b
        fin_cases j <;> simp [a, recordStepSnapshot, mask]
      · have he := he rfl
        subst e
        fin_cases j <;> simp [a, recordStepSnapshot, mask]
    · intro u hu j
      have h := hh j u hu
      simp only [copyTM_contract_lo, copyTM_contract_hi] at h
      by_cases hj : j = 0 ∨ j = dst
      · rw [if_pos hj, if_pos hj] at h
        simp only [Finset.mem_Icc] at h
        dsimp [a, recordStepSnapshot] at h ⊢
        split_ifs at h <;> rw [abs_le] <;> constructor <;> omega
      · rw [if_neg hj, if_neg hj] at h
        rw [Finset.mem_Icc] at h
        have heq := le_antisymm h.2 h.1
        change |((copyTM 4 0 dst).runFrom a u).workTapePos j - d.workTapePos j| ≤ _
        rw [heq]
        simp [a, recordStepSnapshot, (not_or.mp hj).1]
        omega
  have h3 : RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
      (cfg (⟨⟨.copyB, data⟩, .sweep⟩ : RecordStepControl k Q T S) 2 [] [])
      (cfg (⟨⟨.copyD, data⟩, .sweep⟩ : RecordStepControl k Q T S) 2 w []) (2 * w.length + 3) := by
    obtain ⟨he, ht, hh⟩ := copying 1 (Or.inl rfl) [] [] (by simp) (by simp)
    simp only [↓reduceIte, show (1 : Fin 4) ≠ 3 by decide] at he
    exact recordStep_phase_run M upd seek start finish ⟨.copyB, data⟩ (by intro b h; cases h)
      (recordStepSnapshot d SweepPhase.sweep 2 [] [])
      (recordStepSnapshot d SweepPhase.done 2 w []) (2 * w.length + 2) he .done rfl
      (⟨⟨.copyD, data⟩, .sweep⟩ : RecordStepControl k Q T S) rfl
      (by intro u hu q hq; cases q with
          | done => exact (ht u hu hq).elim
          | sweep => rfl
          | rewind => rfl)
      d.workTapePos (L + 1) hh
  have h4 : RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
      (cfg (⟨⟨.copyD, data⟩, .sweep⟩ : RecordStepControl k Q T S) 2 w [])
      (cfg (⟨⟨.positionSkip, data⟩, .run⟩ : RecordStepControl k Q T S) 2 w w) (2 * w.length + 3) := by
    obtain ⟨he, ht, hh⟩ := copying 3 (Or.inr rfl) w [] (by simp) (by simp)
    simp only [show (3 : Fin 4) ≠ 1 by decide, ↓reduceIte] at he
    exact recordStep_phase_run M upd seek start finish ⟨.copyD, data⟩ (by intro b h; cases h)
      (recordStepSnapshot d SweepPhase.sweep 2 w [])
      (recordStepSnapshot d SweepPhase.done 2 w w) (2 * w.length + 2) he .done rfl
      (⟨⟨.positionSkip, data⟩, .run⟩ : RecordStepControl k Q T S) rfl
      (by intro u hu q hq; cases q with
          | done => exact (ht u hu hq).elim
          | sweep => rfl
          | rewind => rfl)
      d.workTapePos (L + 1) hh
  have total := Segment.trans (Segment.trans (Segment.trans (Segment.trans h0' h1) h2) h3) h4
  have time : 5 + 3 + (2 * w.length + 3) + (2 * w.length + 3) +
      (2 * w.length + 3) = 6 * w.length + 17 := by omega
  rw [time] at total
  exact total

/-- After the position fold and the first `r` tape fields, the finite data contains exactly
the source observations for those tapes. Unread slots retain the entry defaults. -/
private def recordStepReadData {k : ℕ} {Q T : Type} {x : List Bool}
    (s : ℕ) (c : Cfg k Bool Q x) (r : ℕ) : RecordStepData k Q T :=
  { state := c.state, widthOne := decide (posWidth x.length = 1),
    posZero := decide (c.inputPos.val = 0),
    symbols := fun i => if i.val < r then c.workTapes i (c.workTapePos i) else none,
    edgeLeft := fun i => decide (i.val < r ∧ c.workTapePos i = -(s : ℤ)),
    edgeRight := fun i => decide (i.val < r ∧ c.workTapePos i = (s : ℤ)) }

/-- Reading tape `i` fills precisely its slot in the observation prefix.
**Proof sketch.** The updated slot has index `i`; for every other slot, being below `i+1`
is the same as being below `i`. Apply this once to the three observation arrays. -/
private theorem recordStepReadData_succ {k : ℕ} {Q T : Type} {x : List Bool}
    (s : ℕ) (c : Cfg k Bool Q x) (i : Fin k) :
    {recordStepReadData (T := T) s c i.val with
      symbols := Function.update (recordStepReadData (T := T) s c i.val).symbols i
        (c.workTapes i (c.workTapePos i)),
      edgeLeft := Function.update (recordStepReadData (T := T) s c i.val).edgeLeft i
        (decide (c.workTapePos i = -(s : ℤ))),
      edgeRight := Function.update (recordStepReadData (T := T) s c i.val).edgeRight i
        (decide (c.workTapePos i = (s : ℤ)))} = recordStepReadData s c (i.val + 1) := by
  dsimp only [recordStepReadData]
  congr 1 <;> funext j <;> by_cases hj : j = i
  all_goals first
    | (subst j; simp)
    | (have hn : j.val ≠ i.val := fun h => hj (Fin.ext h)
       have he : j.val < i.val + 1 ↔ j.val < i.val := by omega
       simp [Function.update_of_ne hj, he])

/-- The exit selected after the complete read and return, before any native cycle or write. -/
private def recordStepReadExit {k : ℕ} {Q T S : Type} (data : RecordStepData k Q T) :
    RecordStepControl k Q T S :=
  if data.state.isNone then ⟨⟨.clearHaltB, data⟩, .sweep⟩
  else if data.widthOne then ⟨⟨.clearEmptyD, data⟩, .sweep⟩
  else ⟨⟨.fuel, data⟩, .fwd ()⟩

/-- The remaining read phases collect all tape observations and the tag, then return to
record start with B and D intact and every other tape and native component unchanged.
**Proof sketch.** Cross F1, then induct over source tapes, applying the existing tape fold
and one skip at each tape. Fold the singleton tag and perform the `k+2` reverse skips.
Each phase is a public row under the existing host; concatenate its `RecordSeg`. The
public field spans bound every record-head prefix and every per-phase time. -/
private theorem recordStep_read_fields {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List Bool}
    (s : ℕ) (c : Cfg k Bool Q x) (τ : T) (hc : c.InWindow s)
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map (RecSym.digitEmb Q T)))
    (hrec : RecordAt d 0 (cfgRecord s c τ)) :
    let fs := cfgRecord s c τ
    let w := (binDigits (posWidth x.length) c.inputPos.val).map (RecSym.digit (Q := Q) (T := T))
    ∃ t ≤ 10 * (k + 3) * ((joinFields fs).length + 1),
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos ((joinFields fs).length + 1)
        (recordStepSnapshot d (⟨⟨.positionSkip, recordStepReadData s c 0⟩, .run⟩ : RecordStepControl k Q T S) 2 w w)
        (recordStepSnapshot d (recordStepReadExit {recordStepReadData (T := T) s c k with tag := some τ}) 0 w w) t := by
  classical
  dsimp only
  let fs := cfgRecord s c τ
  let w := (binDigits (posWidth x.length) c.inputPos.val).map (RecSym.digit (Q := Q) (T := T))
  let L := (joinFields fs).length
  let cfg {A : Type} (q : A) (j : ℕ) := recordStepSnapshot d q (fieldOffset fs j) w w
  let dat := fun r => recordStepReadData (T := T) s c r
  have flen : fs.length = k + 3 := cfgRecord_length s c τ
  have field (j : ℕ) (hj : j < fs.length) (z : ℤ) (hz : -1 ≤ z) (hu : z ≤ (fs[j].length : ℤ)) :
      d.workTapes 0 (d.workTapePos 0 + (fieldOffset fs j : ℤ) + z) = FinTM.bufferTape fs[j] z := by
    have span := fieldOffset_add_length_le fs j hj
    rw [add_assoc, hrec _ (by omega) (by dsimp [fs] at *; omega)]
    exact fieldsTape_field fs j hj z hz hu
  have scan {A : Type} (f g : A → RecSym Q T → A × RecSym Q T) (a b : A)
      (j : ℕ) (hj : j < fs.length) (hp : scanResult f g a fs[j] = (b, fs[j])) :
      (scanTM 4 0 f g a).runFrom (cfg (.fwd a) j) (2 * fs[j].length + 2) = cfg (.done b) j ∧
      (∀ u < 2 * fs[j].length + 2, ∀ v,
        ((scanTM 4 0 f g a).runFrom (cfg (.fwd a) j) u).state ≠ some (.done v)) ∧
      (∀ u ≤ 2 * fs[j].length + 2, ∀ i,
        |((scanTM 4 0 f g a).runFrom (cfg (.fwd a) j) u).workTapePos i - d.workTapePos i| ≤ ((L + 1 : ℕ) : ℤ)) := by
    obtain ⟨he, ht, hh⟩ := recordStep_scan_preserves 0 f g a b fs[j] (cfg (.fwd a) j) rfl
      (by intro z hz hu; simpa [cfg, recordStepSnapshot] using field j hj z hz hu) hp
    refine ⟨he, ht, ?_⟩
    intro u hu i
    have h := hh i u hu
    by_cases hi : i = 0
    · subst i
      simp only [↓reduceIte, Finset.mem_Icc] at h
      have span := fieldOffset_add_length_le fs j hj
      dsimp [cfg, recordStepSnapshot] at h ⊢
      rw [abs_le]
      dsimp [L] at *
      constructor <;> omega
    · rw [if_neg hi] at h
      rw [h]
      simp [cfg, recordStepSnapshot, hi]
      omega
  have forward (j : ℕ) (hj : j < fs.length) :
      (skipTM 4 0).runFrom (cfg SeekPhase.run j) (fs[j].length + 1) = cfg SeekPhase.done (j + 1) ∧
      (∀ u < fs[j].length + 1, ((skipTM 4 0).runFrom (cfg SeekPhase.run j) u).state ≠ some .done) ∧
      (∀ u ≤ fs[j].length + 1, ∀ i,
        |((skipTM 4 0).runFrom (cfg SeekPhase.run j) u).workTapePos i - d.workTapePos i| ≤ ((L + 1 : ℕ) : ℤ)) := by
    obtain ⟨he, ht, hh⟩ := recordStep_contract_clauses (skipTM_contract (0 : Fin 4) _)
      fs[j] (cfg SeekPhase.run j) rfl
      (by
        rw [skipTM_contract_pre]
        intro z hz hu
        simpa [cfg, recordStepSnapshot] using field j hj z (by omega) hu)
    rw [skipTM_contract_time, skipTM_contract_post, recordStep_seekPost_eq] at he
    simp only [skipTM_contract_time] at ht hh
    refine ⟨he.trans ?_, ht, ?_⟩
    · apply Cfg.ext <;> try rfl
      funext i
      by_cases hi : i = 0
      · subst i
        simp [cfg, recordStepSnapshot, fieldOffset_succ fs j hj]
        omega
      · simp [cfg, recordStepSnapshot, hi, Function.update_of_ne]
    · intro u hu i
      have h := hh i u hu
      simp only [skipTM_contract_lo, skipTM_contract_hi] at h
      by_cases hi : i = 0
      · subst i
        simp only [↓reduceIte, Finset.mem_Icc] at h
        have span := fieldOffset_add_length_le fs j hj
        dsimp [cfg, recordStepSnapshot] at h ⊢
        rw [abs_le]
        dsimp [L] at *
        constructor <;> omega
      · rw [if_neg hi] at h
        rw [Finset.mem_Icc] at h
        rw [le_antisymm h.2 h.1]
        simp [cfg, recordStepSnapshot, hi]
        omega
  let readState (r : ℕ) : RecordStepControl k Q T S :=
    if hr : r < k then ⟨⟨.tapeRead ⟨r, hr⟩, dat r⟩, .fwd (false, none, false, false)⟩
    else ⟨⟨.tagRead, dat r⟩, .fwd none⟩
  have first : RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
      (cfg (⟨⟨.positionSkip, dat 0⟩, .run⟩ : RecordStepControl k Q T S) 1)
      (cfg (readState 0) 2) (fs[1].length + 2) := by
    obtain ⟨he, ht, hh⟩ := forward 1 (by omega)
    exact recordStep_phase_run M upd seek start finish ⟨.positionSkip, dat 0⟩
      (by intro b h; cases h) (cfg SeekPhase.run 1) (cfg SeekPhase.done 2)
      (fs[1].length + 1) he .done rfl (readState 0)
      (by simp [recordStepNext, recordStepFirstTape, readState])
      (by intro u hu q hq; cases q with
          | done => exact (ht u hu hq).elim
          | run => rfl
          | gap => rfl
          | back => rfl)
      d.workTapePos (L + 1) hh
  have round (r : ℕ) (hr : r < k) :
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
        (cfg (readState r) (r + 2)) (cfg (readState (r + 1)) (r + 3))
        (3 * fs[r + 2].length + 5) := by
    let i : Fin k := ⟨r, hr⟩
    let result := (true, c.workTapes i (c.workTapePos i),
      decide (c.workTapePos i = -(s : ℤ)), decide (c.workTapePos i = (s : ℤ)))
    have word : fs[r + 2] = (List.range (2 * s + 1)).map (fun (z : ℕ) =>
        RecSym.cell (c.workTapes i ((z : ℤ) - s)) (decide (c.workTapePos i = (z : ℤ) - s))) := by
      simp only [fs, cfgRecord, List.getElem_cons_succ, bind_pure_comp, Functor.map,
        List.map_map, Function.comp_def]
      rw [List.getElem_append_left (by simpa using hr)]
      simp [i]
    obtain ⟨he, ht, hh⟩ := scan (scanFold recordStepTapeFold) scanKeep
      (false, none, false, false) result (r + 2) (by omega)
      (by rw [word]; exact recordStep_tape_fold (T := T) s c hc i)
    have hread := recordStep_phase_run M upd seek start finish ⟨.tapeRead i, dat r⟩
      (by intro b h; cases h) (cfg (.fwd (false, none, false, false)) (r + 2))
      (cfg (.done result) (r + 2)) (2 * fs[r + 2].length + 2) he (.done result) rfl
      (⟨⟨.tapeSkip i, dat (r + 1)⟩, .run⟩ : RecordStepControl k Q T S)
      (by
        exact congrArg (fun e : RecordStepData k Q T =>
          some (⟨⟨.tapeSkip i, e⟩, .run⟩ : RecordStepControl k Q T S))
          (recordStepReadData_succ s c i))
      (by intro u hu q hq; cases q with
          | done v => exact (ht u hu v hq).elim
          | fwd _ => rfl
          | bwd _ => rfl)
      d.workTapePos (L + 1) hh
    obtain ⟨hf, hft, hfh⟩ := forward (r + 2) (by omega)
    have hskip := recordStep_phase_run M upd seek start finish ⟨.tapeSkip i, dat (r + 1)⟩
      (by intro b h; cases h) (cfg SeekPhase.run (r + 2)) (cfg SeekPhase.done (r + 3))
      (fs[r + 2].length + 1) hf .done rfl (readState (r + 1))
      (by by_cases h : r + 1 < k <;> simp [recordStepNext, readState, i, h])
      (by intro u hu q hq; cases q with
          | done => exact (hft u hu hq).elim
          | run => rfl
          | gap => rfl
          | back => rfl)
      d.workTapePos (L + 1) hfh
    have ht := Segment.trans hread hskip
    have time : (2 * fs[r + 2].length + 2 + 1) + (fs[r + 2].length + 1 + 1) =
        3 * fs[r + 2].length + 5 := by omega
    rw [time] at ht
    simpa only [readState, dif_pos hr] using ht
  have rounds : ∀ r ≤ k, ∃ t ≤ 5 * r * (L + 1),
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
        (cfg (readState 0) 2) (cfg (readState r) (r + 2)) t := by
    intro r hr
    induction r with
    | zero =>
      refine ⟨0, by omega, Segment.zero ((record_headBox_iff _ _ _).mpr ?_)⟩
      intro i
      have span := fieldOffset_add_length_le fs 2 (by omega)
      simp only [cfg, recordStepSnapshot]
      split_ifs <;> rw [abs_le] <;> dsimp [L] at * <;> constructor <;> omega
    | succ r ih =>
      obtain ⟨t, ht, hrun⟩ := ih (by omega)
      have span := fieldOffset_add_length_le fs (r + 2) (by omega)
      refine ⟨t + (3 * fs[r + 2].length + 5), ?_, Segment.trans hrun (round r (by omega))⟩
      have hb : 3 * fs[r + 2].length + 5 ≤ 5 * (L + 1) := by dsimp [L]; omega
      calc
        _ ≤ 5 * r * (L + 1) + 5 * (L + 1) := Nat.add_le_add ht hb
        _ = _ := by ring
  let data := {dat k with tag := some τ}
  let backState (j : ℕ) (hj : j ≤ k + 2) : RecordStepControl k Q T S :=
    if h : 0 < j then ⟨⟨.readBack ⟨j - 1, by omega⟩, data⟩, .run⟩
    else recordStepReadExit data
  have tag : RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
      (cfg (readState k) (k + 2)) (cfg (backState (k + 2) le_rfl) (k + 2)) 5 := by
    have word : fs[k + 2] = [RecSym.tag τ] := by simp [fs, cfgRecord]
    let δ : Option T → RecSym Q T → Option T := fun _ γ => match γ with
      | .tag v => some v | _ => none
    obtain ⟨he, ht, hh⟩ := scan (scanFold δ) scanKeep none (some τ) (k + 2) (by omega)
      (by rw [word, scanResult_fold]; rfl)
    simp only [word, List.length_cons, List.length_nil] at he ht hh
    have hp := recordStep_phase_run M upd seek start finish ⟨.tagRead, dat k⟩
      (by intro b h; cases h) (cfg (.fwd none) (k + 2)) (cfg (.done (some τ)) (k + 2))
      4 he (.done (some τ)) rfl (backState (k + 2) le_rfl)
      (by simp [recordStepNext, backState, data])
      (by intro u hu q hq; cases q with
          | done v => exact (ht u hu v hq).elim
          | fwd _ => rfl
          | bwd _ => rfl)
      d.workTapePos (L + 1) hh
    simpa only [readState, lt_self_iff_false, ↓reduceDIte] using hp
  have backward (j : ℕ) (hj : j < k + 2) :
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
        (cfg (backState (j + 1) (by omega)) (j + 1)) (cfg (backState j (by omega)) j)
        (fs[j].length + 4) := by
    have jf : j < fs.length := by omega
    have hoff := fieldOffset_succ fs j jf
    obtain ⟨he, ht, hh⟩ := recordStep_contract_clauses (skipBackTM_contract (0 : Fin 4) _)
      fs[j] (cfg SeekPhase.run (j + 1)) rfl
      (by
        rw [skipBackTM_contract_pre]
        intro z hz hu
        have hpos : (cfg SeekPhase.run (j + 1)).workTapePos 0 - (fs[j].length : ℤ) - 1 =
            d.workTapePos 0 + (fieldOffset fs j : ℤ) := by
          simp [cfg, recordStepSnapshot, hoff]
          omega
        change d.workTapes 0 ((cfg SeekPhase.run (j + 1)).workTapePos 0 - (fs[j].length : ℤ) - 1 + z) = _
        rw [hpos]
        exact field j jf z hz hu)
    rw [skipBackTM_contract_time, skipBackTM_contract_post, recordStep_seekPost_eq] at he
    simp only [skipBackTM_contract_time] at ht hh
    have hout : (skipBackTM 4 0).runFrom (cfg SeekPhase.run (j + 1)) (fs[j].length + 3) =
        cfg SeekPhase.done j := by
      refine he.trans ?_
      apply Cfg.ext <;> try rfl
      funext i
      by_cases hi : i = 0
      · subst i
        simp [cfg, recordStepSnapshot, hoff]
        omega
      · simp [cfg, recordStepSnapshot, hi, Function.update_of_ne]
    have hp := recordStep_phase_run M upd seek start finish
      ⟨.readBack ⟨j, hj⟩, data⟩ (by intro b h; cases h)
      (cfg SeekPhase.run (j + 1)) (cfg SeekPhase.done j) (fs[j].length + 3) hout .done rfl
      (backState j (by omega))
      (by
        dsimp [recordStepNext, backState, recordStepReadExit]
        split_ifs <;> rfl)
      (by intro u hu q hq; cases q with
          | done => exact (ht u hu hq).elim
          | run => rfl
          | gap => rfl
          | back => rfl)
      d.workTapePos (L + 1) (by
        intro u hu i
        have h := hh i u hu
        simp only [skipBackTM_contract_lo, skipBackTM_contract_hi] at h
        by_cases hi : i = 0
        · subst i
          simp only [↓reduceIte, Finset.mem_Icc] at h
          have span := fieldOffset_add_length_le fs (j + 1) (by omega)
          dsimp [cfg, recordStepSnapshot, recordStepRows] at h ⊢
          rw [abs_le]
          dsimp [L] at *
          constructor <;> omega
        · rw [if_neg hi] at h
          rw [Finset.mem_Icc] at h
          change |((skipBackTM 4 0).runFrom (cfg SeekPhase.run (j + 1)) u).workTapePos i - d.workTapePos i| ≤ _
          rw [le_antisymm h.2 h.1]
          simp [cfg, recordStepSnapshot, hi]
          omega)
    simpa [backState, Nat.add_sub_cancel] using hp
  have backs : ∀ j (hj : j ≤ k + 2), ∃ t ≤ 4 * j * (L + 1),
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
        (cfg (backState j hj) j) (cfg (backState 0 (by omega)) 0) t := by
    intro j hj
    induction j with
    | zero =>
      refine ⟨0, by omega, Segment.zero ((record_headBox_iff _ _ _).mpr ?_)⟩
      intro i
      simp [cfg, recordStepSnapshot, fieldOffset]
      omega
    | succ j ih =>
      obtain ⟨t, ht, hrun⟩ := ih (by omega)
      have span := fieldOffset_add_length_le fs j (by omega)
      refine ⟨fs[j].length + 4 + t, ?_, Segment.trans (backward j (by omega)) hrun⟩
      have hb : fs[j].length + 4 ≤ 4 * (L + 1) := by dsimp [L]; omega
      calc
        _ ≤ 4 * (L + 1) + 4 * j * (L + 1) := Nat.add_le_add hb ht
        _ = _ := by ring
  obtain ⟨tr, htr, hr⟩ := rounds k le_rfl
  obtain ⟨tb, htb, hb⟩ := backs (k + 2) le_rfl
  refine ⟨fs[1].length + 2 + tr + 5 + tb, ?_, ?_⟩
  · have span := fieldOffset_add_length_le fs 1 (by omega)
    have hf : fs[1].length + 2 ≤ 2 * (L + 1) := by dsimp [L]; omega
    calc
      _ ≤ 2 * (L + 1) + 5 * k * (L + 1) + 5 * (L + 1) + 4 * (k + 2) * (L + 1) := by
        omega
      _ ≤ 10 * (k + 3) * (L + 1) := by nlinarith [Nat.zero_le (k * (L + 1))]
  · have total := Segment.trans (Segment.trans (Segment.trans first hr) tag) hb
    simpa only [cfg, fs, fieldOffset_cons_succ, fieldOffset, List.take_zero, List.map_nil,
      List.sum_nil, List.length_cons, List.length_nil, zero_add, Nat.cast_ofNat,
      Nat.cast_zero, backState, Nat.lt_irrefl, ↓reduceDIte] using total

/-- The complete R1--R6 read segment, with exact source observations, both position-digit
copies, restored heads, and unchanged native position/output/record frame.
**Proof sketch.** Concatenate the checked prefix and field loop. Each has radius `L+1`;
the prefix costs at most `17(L+1)` and the remaining read at most `10(k+3)(L+1)`. -/
private theorem recordStep_read_all {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List Bool}
    (s : ℕ) (c : Cfg k Bool Q x) (τ : T) (hc : c.InWindow s)
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map (RecSym.digitEmb Q T)))
    (hd : d.state = some recordStepEntry) (hrec : RecordAt d 0 (cfgRecord s c τ))
    (hblank : ∀ j : Fin 4, j ≠ 0 → ∀ z, d.workTapes j z = none) :
    let w := (binDigits (posWidth x.length) c.inputPos.val).map (RecSym.digit (Q := Q) (T := T))
    ∃ t ≤ (10 * (k + 3) + 17) * ((joinFields (cfgRecord s c τ)).length + 1),
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos
        ((joinFields (cfgRecord s c τ)).length + 1) d
        (recordStepSnapshot d (recordStepReadExit {recordStepReadData (T := T) s c k with tag := some τ}) 0 w w) t := by
  dsimp only
  have hp := recordStep_read_prefix M upd seek start finish s c τ d hd hrec hblank
  obtain ⟨t, ht, hr⟩ := recordStep_read_fields M upd seek start finish s c τ hc d hrec
  have dat0 : recordStepReadData (T := T) s c 0 =
      {state := c.state, widthOne := decide (posWidth x.length = 1), posZero := decide (c.inputPos.val = 0)} := by
    simp [recordStepReadData]
  rw [dat0] at hr
  refine ⟨_, ?_, Segment.trans hp hr⟩
  have span := fieldOffset_add_length_le (cfgRecord s c τ) 1 (by simp [cfgRecord_length])
  change 2 + ((binDigits (posWidth x.length) c.inputPos.val).map
    (RecSym.digit (Q := Q) (T := T))).length ≤ (joinFields (cfgRecord s c τ)).length at span
  simp only [List.length_map, binDigits, List.length_range] at span
  have hw : 6 * ((binDigits (posWidth x.length) c.inputPos.val).map
      (RecSym.digit (Q := Q) (T := T))).length + 17 ≤
      17 * ((joinFields (cfgRecord s c τ)).length + 1) := by
    simp only [List.length_map, binDigits, List.length_range]
    omega
  calc
    _ ≤ 17 * ((joinFields (cfgRecord s c τ)).length + 1) +
      10 * (k + 3) * ((joinFields (cfgRecord s c τ)).length + 1) := Nat.add_le_add hw ht
    _ = _ := by ring

/-- Clearing B or D in a normalized snapshot erases that entire scratch word, preserves
all other components, and retains the framed clear row's first exit and trajectory.
**Proof sketch.** Read the public clear contract at the selected globally buffered word.
Outside the erased interval the old buffer is already blank, so the endpoint is the empty
buffer. -/
private theorem recordStep_clear_snapshot {Γ P : Type} {x : List Γ}
    (d : Cfg 4 Γ P x) (p : ℤ) (b e w : List Γ) (dst : Fin 4)
    (hdst : dst = 1 ∨ dst = 3) (hb : dst = 1 → b = w) (he : dst = 3 → e = w) :
    let a := recordStepSnapshot d SweepPhase.sweep p b e
    (clearTM 4 dst).runFrom a (2 * w.length + 2) =
      recordStepSnapshot d SweepPhase.done p (if dst = 1 then [] else b) (if dst = 3 then [] else e) ∧
    (∀ u < 2 * w.length + 2, ((clearTM 4 dst).runFrom a u).state ≠ some .done) ∧
    (∀ j u, u ≤ 2 * w.length + 2 →
      if j = dst then ((clearTM 4 dst).runFrom a u).workTapePos j ∈
        Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
      else ((clearTM 4 dst).runFrom a u).workTapePos j = a.workTapePos j) := by
  dsimp only
  let a := recordStepSnapshot d SweepPhase.sweep p b e
  have hw : ∀ z : ℤ, -1 ≤ z → z ≤ (w.length : ℤ) →
      a.workTapes dst (a.workTapePos dst + z) = FinTM.bufferTape w z := by
    intro z _ _
    rcases hdst with rfl | rfl
    · simp [a, recordStepSnapshot, hb rfl]
    · simp [a, recordStepSnapshot, he rfl]
  obtain ⟨hr, ht, hh⟩ := recordStep_contract_clauses (clearTM_contract dst x) w a rfl
    (by rw [clearTM_contract_pre]; exact hw)
  rw [clearTM_contract_time, clearTM_contract_post, recordStep_sweepPost_eq] at hr
  simp only [clearTM_contract_time] at ht hh
  refine ⟨hr.trans ?_, ht, ?_⟩
  · have erased (h z : ℤ) :
        (if h ≤ z ∧ z < h + (w.length : ℤ) then none else FinTM.bufferTape w (z - h)) = none := by
      split_ifs with hspan
      · rfl
      · unfold FinTM.bufferTape
        split_ifs with hz
        · apply List.getElem?_eq_none
          omega
        · rfl
    apply Cfg.ext <;> try rfl
    funext j z
    rcases hdst with rfl | rfl
    · have hb := hb rfl
      subst b
      fin_cases j <;> simp [a, recordStepSnapshot, erased]
    · have he := he rfl
      subst e
      fin_cases j <;> simp [a, recordStepSnapshot, erased]
  · intro j u hu
    have h := hh j u hu
    simp only [clearTM_contract_lo, clearTM_contract_hi] at h
    by_cases hj : j = dst
    · subst j
      rw [if_pos rfl, if_pos rfl] at h
      rcases hdst with rfl | rfl <;> simpa [a, recordStepSnapshot] using h
    · rw [if_neg hj, if_neg hj] at h
      rw [Finset.mem_Icc] at h
      rw [if_neg hj]
      exact le_antisymm h.2 h.1

/-- The absolute head radius of a scratch clear at the record entry.
**Proof sketch.** Convert the shared clear specialization's selected interval into an
absolute displacement; every other head is stationary in the zero-offset snapshot. -/
private theorem recordStep_clear_heads {Γ P : Type} {x : List Γ}
    (d : Cfg 4 Γ P x) (b e w : List Γ) (dst : Fin 4)
    (hdst : dst = 1 ∨ dst = 3) (hb : dst = 1 → b = w) (he : dst = 3 → e = w) :
    ∀ u ≤ 2 * w.length + 2, ∀ j,
      |((clearTM 4 dst).runFrom (recordStepSnapshot d .sweep 0 b e) u).workTapePos j -
        d.workTapePos j| ≤ ((w.length + 1 : ℕ) : ℤ) := by
  intro u hu j
  have h := (recordStep_clear_snapshot d 0 b e w dst hdst hb he).2.2 j u hu
  by_cases hj : j = dst
  · rw [if_pos hj] at h
    simp only [Finset.mem_Icc] at h
    rw [abs_le]; constructor <;> omega
  · rw [if_neg hj] at h
    rw [h]
    simp [recordStepSnapshot]
    omega

/-- On a halted source, the read exit clears both digit copies and reaches yes without
changing any record cell or native component. The two clear phases cost `4|w|+6`.
**Proof sketch.** Instantiate the shared scratch-clear specialization twice and the public
phase host twice; concatenate. The selected scratch heads have radius `|w|+1`. -/
private theorem recordStep_halt_run {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List (RecSym Q T)}
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) x)
    (w : List (RecSym Q T)) (data : RecordStepData k Q T) (halted : data.state = none) :
    RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (w.length + 1)
      (recordStepSnapshot d (recordStepReadExit data) 0 w w)
      (recordStepSnapshot d (recordStepVerdict true : RecordStepControl k Q T S) 0 [] [])
      (4 * w.length + 6) := by
  have clear (dst : Fin 4) (hdst : dst = 1 ∨ dst = 3)
      (b e : List (RecSym Q T)) (hb : dst = 1 → b = w) (he : dst = 3 → e = w) :=
    recordStep_clear_snapshot d 0 b e w dst hdst hb he
  have bounds (dst : Fin 4) (hdst : dst = 1 ∨ dst = 3)
      (b e : List (RecSym Q T)) (hb : dst = 1 → b = w) (he : dst = 3 → e = w) :=
    recordStep_clear_heads d b e w dst hdst hb he
  obtain ⟨hB, cutB, _⟩ := clear 1 (Or.inl rfl) w w (by simp) (by simp)
  have pB := recordStep_phase_run M upd seek start finish ⟨.clearHaltB, data⟩
    (by intro b h; cases h) (recordStepSnapshot d .sweep 0 w w)
    (recordStepSnapshot d .done 0 [] w) (2 * w.length + 2) (by simpa using hB) .done rfl
    (⟨⟨.clearHaltD, data⟩, .sweep⟩ : RecordStepControl k Q T S) rfl
    (by intro u hu q hq; cases q with
        | done => exact (cutB u hu hq).elim
        | sweep => rfl
        | rewind => rfl)
    d.workTapePos (w.length + 1) (bounds 1 (Or.inl rfl) w w (by simp) (by simp))
  obtain ⟨hD, cutD, _⟩ := clear 3 (Or.inr rfl) [] w (by simp) (by simp)
  have pD := recordStep_phase_run M upd seek start finish ⟨.clearHaltD, data⟩
    (by intro b h; cases h) (recordStepSnapshot d .sweep 0 [] w)
    (recordStepSnapshot d .done 0 [] []) (2 * w.length + 2) (by simpa using hD) .done rfl
    (recordStepVerdict true : RecordStepControl k Q T S) rfl
    (by intro u hu q hq; cases q with
        | done => exact (cutD u hu hq).elim
        | sweep => rfl
        | rewind => rfl)
    d.workTapePos (w.length + 1) (bounds 3 (Or.inr rfl) [] w (by simp) (by simp))
  have ht := Segment.trans pB pD
  have time : (2 * w.length + 2 + 1) + (2 * w.length + 2 + 1) = 4 * w.length + 6 := by omega
  rw [time] at ht
  simpa [recordStepReadExit, halted, recordStep_mapState_mk, recordStepSnapshot] using ht

/-- Transport a framed seek and its full first-return/radius contract to a selected digit
bank in the rich record host. Only native position and control change at the endpoint;
all rich frame cells and the arbitrary output prefix are restored.
**Proof sketch.** Decode the two selected tapes, apply the supplied public seek contract,
and use `recordStep_transport` for every prefix. Its time-zero instance identifies the
unchanged frame at the endpoint. Selected heads use the seek bound and unselected heads
are fixed by the public embedding layout. -/
private theorem recordStep_seek_transport {Q T S : Type} [DecidableEq Q] [DecidableEq T]
    (seek : MultiTapeTM 2 Bool S) (start finish : S) (C : ℕ) {x : List Bool}
    (p : ℕ) (w : List Bool) (hpx : p ≤ x.length + 1)
    (hspec : ∀ c : Cfg 2 Bool S x, c.state = some start →
      (∀ z : ℤ, -1 ≤ z → z ≤ (w.length : ℤ) →
        c.workTapes 0 (c.workTapePos 0 + z) = FinTM.bufferTape w z) →
      (∀ z, c.workTapes 1 z = none) →
      ∃ t ≤ C * (w.length + c.inputPos.val + p + 1),
        (∀ u < t, (seek.runFrom c u).state ≠ some finish) ∧
        (∀ u ≤ t, ∀ j, |(seek.runFrom c u).workTapePos j - c.workTapePos j| ≤
          ((C * (w.length + 1) : ℕ) : ℤ)) ∧
        (seek.runFrom c t).state = some finish ∧ (seek.runFrom c t).inputPos.val = p ∧
        (seek.runFrom c t).workTapes = c.workTapes ∧
        (seek.runFrom c t).workTapePos = c.workTapePos ∧ (seek.runFrom c t).output = c.output)
    (ι : Fin 2 ↪ Fin 4)
    (d : Cfg 4 (RecSym Q T) S (x.map (RecSym.digitEmb Q T)))
    (hd : d.state = some start)
    (hdig : ∀ i z γ, d.workTapes (ι i) z = some γ → ∃ b, γ = (RecSym.digitEmb Q T) b)
    (hw : ∀ z : ℤ, -1 ≤ z → z ≤ (w.length : ℤ) →
      d.workTapes (ι 0) (d.workTapePos (ι 0) + z) = FinTM.bufferTape (w.map (RecSym.digitEmb Q T)) z)
    (hblank : ∀ z, d.workTapes (ι 1) z = none) :
    ∃ t ≤ C * (w.length + d.inputPos.val + p + 1),
      (∀ u < t, ((embedEmitTM ι (seek.liftSymbols (RecSym.digitEmb Q T))).runFrom d u).state ≠ some finish) ∧
      (∀ u ≤ t, ∀ j,
        |((embedEmitTM ι (seek.liftSymbols (RecSym.digitEmb Q T))).runFrom d u).workTapePos j -
          d.workTapePos j| ≤ ((C * (w.length + 1) : ℕ) : ℤ)) ∧
      (embedEmitTM ι (seek.liftSymbols (RecSym.digitEmb Q T))).runFrom d t =
        {d with state := some finish, inputPos := ⟨p, by simp; omega⟩} := by
  let e := RecSym.digitEmb Q T
  let c : Cfg 2 Bool S x := ⟨d.state, Fin.cast (by simp) d.inputPos,
    (fun i z => (d.workTapes (ι i) z).bind (decodeBool e)), (fun i => d.workTapePos (ι i)), []⟩
  obtain ⟨t, ht, cut, heads, state, pos, tapes, positions, output⟩ := hspec c hd
    (by
      intro z hz hu
      change (d.workTapes (ι 0) (d.workTapePos (ι 0) + z)).bind (decodeBool e) = _
      rw [hw z hz hu]
      exact FinTM.bufferTape_map_decode e w z)
    (by intro z; simp [c, hblank])
  have row : seek.runFrom c t = {c with state := some finish, inputPos := ⟨p, by omega⟩} :=
    Cfg.ext state (Fin.ext pos) tapes positions output
  have zero := recordStep_transport seek e ι d hdig 0
  change d = embedEmitCfg ι d.workTapes d.workTapePos d.output (c.liftSymbols e) at zero
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · intro u hu
    rw [recordStep_transport seek e ι d hdig u]
    exact cut u hu
  · intro u hu j
    rw [recordStep_transport seek e ι d hdig u]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos]
      exact heads u hu i
    · have hf := ((embedEmitTM_frame ι (seek.liftSymbols e) d.workTapes d.workTapePos d.output
        ((seek.runFrom c u).liftSymbols e) 0).1 j hj).2
      change (embedEmitCfg ι d.workTapes d.workTapePos d.output ((seek.runFrom c u).liftSymbols e)).workTapePos j = d.workTapePos j at hf
      rw [hf]
      simp only [sub_self, abs_zero]
      exact_mod_cast Nat.zero_le (C * (w.length + 1))
  · rw [recordStep_transport seek e ι d hdig t]
    change embedEmitCfg ι d.workTapes d.workTapePos d.output ((seek.runFrom c t).liftSymbols e) = _
    rw [row]
    apply Cfg.ext
    · rfl
    · apply Fin.ext; rfl
    · have h := congrArg (fun a : Cfg 4 (RecSym Q T) S (x.map e) => a.workTapes) zero.symm
      exact h
    · have h := congrArg (fun a : Cfg 4 (RecSym Q T) S (x.map e) => a.workTapePos) zero.symm
      exact h
    · have h := congrArg (fun a : Cfg 4 (RecSym Q T) S (x.map e) => a.output) zero.symm
      exact h

/-- A map scan on a scratch snapshot replaces its selected word by the mapped word.
The other buffers and the record frame are untouched, with the original scan cut and heads.
**Proof sketch.** Specialize the public scan to `scanMap`; its result is the public map
identity. Both old and mapped words are blank outside the same interval, which turns the
framed update into the globally buffered snapshot. -/
private theorem recordStep_map_snapshot {Γ P : Type} {x : List Γ}
    (d : Cfg 4 Γ P x) (p : ℤ) (b e w : List Γ) (f : Γ → Γ) (dst : Fin 4)
    (hdst : dst = 1 ∨ dst = 3) (hb : dst = 1 → b = w) (he : dst = 3 → e = w) :
    let a := recordStepSnapshot d (ScanPhase.fwd ()) p b e
    (scanTM 4 dst (scanMap f) scanKeep ()).runFrom a (2 * w.length + 2) =
      recordStepSnapshot d (ScanPhase.done ()) p
        (if dst = 1 then w.map f else b) (if dst = 3 then w.map f else e) ∧
    (∀ u < 2 * w.length + 2, ∀ v,
      ((scanTM 4 dst (scanMap f) scanKeep ()).runFrom a u).state ≠ some (.done v)) ∧
    (∀ j u, u ≤ 2 * w.length + 2 →
      if j = dst then ((scanTM 4 dst (scanMap f) scanKeep ()).runFrom a u).workTapePos j ∈
        Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
      else ((scanTM 4 dst (scanMap f) scanKeep ()).runFrom a u).workTapePos j = a.workTapePos j) := by
  dsimp only
  let a := recordStepSnapshot d (ScanPhase.fwd ()) p b e
  have hw : ∀ z : ℤ, -1 ≤ z → z ≤ (w.length : ℤ) →
      a.workTapes dst (a.workTapePos dst + z) = FinTM.bufferTape w z := by
    intro z _ _
    rcases hdst with rfl | rfl
    · simp [a, recordStepSnapshot, hb rfl]
    · simp [a, recordStepSnapshot, he rfl]
  obtain ⟨hr, ht, hh⟩ := recordStep_contract_clauses_range
    (scanTM_contract dst (scanMap f) scanKeep () x) w a rfl
    (by rw [scanTM_contract_pre]; exact hw)
  rw [scanTM_contract_time, scanTM_contract_post] at hr
  simp only [scanTM_contract_time] at ht hh
  rw [scanResult_map] at hr
  refine ⟨hr.trans ?_, ht, ?_⟩
  · have mapped (h z : ℤ) :
        (if h ≤ z ∧ z < h + (w.length : ℤ) then FinTM.bufferTape (w.map f) (z - h)
          else FinTM.bufferTape w (z - h)) = FinTM.bufferTape (w.map f) (z - h) := by
      split_ifs with hspan
      · rfl
      · by_cases hz : 0 ≤ z - h
        · have hn : w.length ≤ (z - h).toNat := by omega
          simp only [FinTM.bufferTape, if_pos hz, List.getElem?_eq_none hn,
            List.getElem?_eq_none (by simpa using hn : (w.map f).length ≤ (z - h).toNat)]
        · simp only [FinTM.bufferTape, if_neg hz]
    apply Cfg.ext <;> try rfl
    funext j z
    rcases hdst with rfl | rfl
    · have hb := hb rfl
      subst b
      fin_cases j <;> simp [a, recordStepSnapshot, mapped]
    · have he := he rfl
      subst e
      fin_cases j <;> simp [a, recordStepSnapshot, mapped]
  · intro j u hu
    have h := hh j u hu
    simp only [scanTM_contract_lo, scanTM_contract_hi] at h
    by_cases hj : j = dst
    · subst j
      rw [if_pos rfl, if_pos rfl] at h
      rcases hdst with rfl | rfl <;> simpa [a, recordStepSnapshot] using h
    · rw [if_neg hj, if_neg hj] at h
      rw [Finset.mem_Icc] at h
      rw [if_neg hj]
      exact le_antisymm h.2 h.1

/-- The live empty-input branch clears D without any native movement and enters dispatch.
**Proof sketch.** The width-one branch already knows the input symbol is blank. Apply the
shared D-clear specialization and the public host phase; B is retained for the position
rewrite or for rejection cleanup. -/
private theorem recordStep_empty_run {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List (RecSym Q T)}
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) x)
    (w : List (RecSym Q T)) (data : RecordStepData k Q T)
    (live : data.state ≠ none) (empty : data.widthOne = true) :
    RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (w.length + 1)
      (recordStepSnapshot d (recordStepReadExit data) 0 w w)
      (recordStepSnapshot d (recordStepApply M {data with input := none}) 0 w [])
      (2 * w.length + 3) := by
  obtain ⟨he, ht, hh⟩ := recordStep_clear_snapshot d 0 w w w 3 (Or.inr rfl) (by simp) (by simp)
  have hphase := recordStep_phase_run M upd seek start finish ⟨.clearEmptyD, data⟩
    (by intro b h; cases h) (recordStepSnapshot d .sweep 0 w w)
    (recordStepSnapshot d .done 0 w []) (2 * w.length + 2) (by simpa using he) .done rfl
    (recordStepApply M {data with input := none}) rfl
    (by intro u hu q hq; cases q with
        | done => exact (ht u hu hq).elim
        | sweep => rfl
        | rewind => rfl)
    d.workTapePos (w.length + 1) (recordStep_clear_heads d w w w 3 (Or.inr rfl) (by simp) (by simp))
  simpa [recordStepReadExit, live, empty, recordStep_mapState_mk, recordStepSnapshot] using hphase

/-- Rejection clears B and returns no before any record rewrite.
**Proof sketch.** The finite outside test selects the B-clear row. Its framed contract and
one public host dispatch restore the empty scratch bank without changing the record. -/
private theorem recordStep_reject_run {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List (RecSym Q T)}
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) x)
    (w : List (RecSym Q T)) (data : RecordStepData k Q T) (outside : recordStepOutside M data = true) :
    RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (w.length + 1)
      (recordStepSnapshot d (recordStepApply M data) 0 w [])
      (recordStepSnapshot d (recordStepVerdict false : RecordStepControl k Q T S) 0 [] [])
      (2 * w.length + 3) := by
  obtain ⟨he, ht, hh⟩ := recordStep_clear_snapshot d 0 w [] w 1 (Or.inl rfl) (by simp) (by simp)
  have hphase := recordStep_phase_run M upd seek start finish ⟨.clearRejectB, data⟩
    (by intro b h; cases h) (recordStepSnapshot d .sweep 0 w [])
    (recordStepSnapshot d .done 0 [] []) (2 * w.length + 2) (by simpa using he) .done rfl
    (recordStepVerdict false : RecordStepControl k Q T S) rfl
    (by intro u hu q hq; cases q with
        | done => exact (ht u hu hq).elim
        | sweep => rfl
        | rewind => rfl)
    d.workTapePos (w.length + 1) (recordStep_clear_heads d w [] w 1 (Or.inl rfl) (by simp) (by simp))
  simpa [recordStepApply, outside, recordStep_mapState_mk, recordStepSnapshot] using hphase

/-- Save's proved Bool countdown transported onto D, with every rich frame cell preserved.
It returns the native head to zero, replaces D by the residual fuel, restores its head,
and retains both first-exit cuts and the width-only work-head radius.
**Proof sketch.** The public counter layout identifies the decoded singleton bank with
Save's input. Apply the inherited save contract and transport every prefix through the
existing R1 wrapper. Both residual and entry fuel are blank outside their common width;
selected-tape and unselected-frame APIs identify the rich endpoint. -/
private theorem recordStep_save_transport {Q T : Type} [DecidableEq Q] [DecidableEq T]
    {x : List Bool} (d : Cfg 4 (RecSym Q T) (CounterLoopState Bool) (x.map (RecSym.digitEmb Q T)))
    (hd : d.state = some (.dec .run)) (hp : d.inputPos.val ≤ x.length) (w : List Bool)
    (hwval : Nat.ofDigits 2 (w.map Bool.toNat) = 2 ^ w.length - 1)
    (hfuel : d.inputPos.val < Nat.ofDigits 2 (w.map Bool.toNat))
    (hword : ∀ z, d.workTapes 3 z = FinTM.bufferTape (w.map (RecSym.digitEmb Q T)) (z - d.workTapePos 3)) :
    ∃ t ≤ 5 * (d.inputPos.val + 1) + 2 * w.length,
      let R := embedEmitTM (recordStepDigitBank 2)
        ((counterLoopTM recordStepSave false (some true)).liftSymbols (RecSym.digitEmb Q T))
      R.runFrom d t =
        {d with
          state := some .escape
          inputPos := 0
          workTapes := fun j z => if j = 3 then
            FinTM.bufferTape ((counterWord w (d.inputPos.val + 1)).map (RecSym.digitEmb Q T))
              (z - d.workTapePos 3) else d.workTapes j z} ∧
      (∀ u < t, (R.runFrom d u).state ≠ some .done ∧ (R.runFrom d u).state ≠ some .escape) ∧
      (∀ u ≤ t, ∀ j, |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ ((w.length + 1 : ℕ) : ℤ)) ∧
      Nat.ofDigits 2 (((counterWord w (d.inputPos.val + 1)).map not).map Bool.toNat) = d.inputPos.val + 1 := by
  let e := RecSym.digitEmb Q T
  let ι := recordStepDigitBank 2
  let B := counterLoopTM recordStepSave false (some true)
  let c : Cfg 0 Bool Bool x := ⟨some false, Fin.cast (by simp) d.inputPos, Fin.elim0, Fin.elim0, []⟩
  let ct := fun z => FinTM.bufferTape w (z - d.workTapePos 3)
  let raw : Cfg 1 Bool (CounterLoopState Bool) x :=
    ⟨d.state, Fin.cast (by simp) d.inputPos,
      (fun i z => (d.workTapes (ι i) z).bind (decodeBool e)), (fun i => d.workTapePos (ι i)), []⟩
  have decoded : raw = counterLoopCfg (some (.dec .run)) c ct (d.workTapePos 3) := by
    rw [counter_cfg_eq]
    apply Cfg.ext
    · exact hd
    · rfl
    · funext i z
      have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst i
      change (d.workTapes 3 z).bind (decodeBool e) = FinTM.bufferTape w (z - d.workTapePos 3)
      rw [hword]
      exact FinTM.bufferTape_map_decode e w _
    · funext i
      have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst i
      rfl
    · rfl
  have digits : ∀ i z γ, d.workTapes (ι i) z = some γ → ∃ b, γ = e b := by
    intro i z γ h
    change d.workTapes 3 z = some γ at h
    rw [hword, FinTM.bufferTape_map] at h
    cases hb : FinTM.bufferTape w (z - d.workTapePos 3) with
    | none => simp [hb] at h
    | some b => exact ⟨b, by simpa [hb] using h.symm⟩
  obtain ⟨t, ht, he, hc, hh, hv⟩ := recordStep_save_run c rfl hp w hwval hfuel ct (d.workTapePos 3)
    (by intro z _ _; simp [ct])
  have row : B.runFrom raw t =
      (⟨some .escape, 0, (fun _ z => FinTM.bufferTape (counterWord w (d.inputPos.val + 1))
        (z - d.workTapePos 3)), (fun _ => d.workTapePos 3), []⟩ : Cfg 1 Bool (CounterLoopState Bool) x) := by
    rw [decoded, he, counter_cfg_eq]
    apply Cfg.ext <;> try rfl
    · funext i z
      have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst i
      change (if d.workTapePos 3 ≤ z ∧ z < d.workTapePos 3 + (w.length : ℤ) then
        FinTM.bufferTape (counterWord w (d.inputPos.val + 1)) (z - d.workTapePos 3)
        else FinTM.bufferTape w (z - d.workTapePos 3)) = _
      split_ifs with hz
      · rfl
      · by_cases hn : 0 ≤ z - d.workTapePos 3
        · have hl : w.length ≤ (z - d.workTapePos 3).toNat := by omega
          simp only [FinTM.bufferTape, if_pos hn, List.getElem?_eq_none hl,
            List.getElem?_eq_none (by simpa only [counterWord_length] using hl :
              (counterWord w (d.inputPos.val + 1)).length ≤ (z - d.workTapePos 3).toNat)]
        · simp only [FinTM.bufferTape, if_neg hn]
    · funext i
      have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst i
      rfl
  have tr (u : ℕ) := recordStep_transport B e ι d digits u
  have frame (u : ℕ) (j : Fin 4) (hj : j ≠ 3) :=
    (embedEmitTM_frame ι (B.liftSymbols e) d.workTapes d.workTapePos d.output
      ((B.runFrom raw u).liftSymbols e) 0).1 j
      (by rintro ⟨i, hi⟩; exact hj hi.symm)
  refine ⟨t, ht, ?_, ?_, ?_, hv⟩
  · rw [tr t]
    change embedEmitCfg ι d.workTapes d.workTapePos d.output ((B.runFrom raw t).liftSymbols e) = _
    apply Cfg.ext
    · simp [row, embedEmitCfg, Cfg.liftSymbols]
    · apply Fin.ext
      simp [row, embedEmitCfg, Cfg.liftSymbols]
    · funext j z
      by_cases hj : j = 3
      · subst j
        change (embedEmitCfg ι d.workTapes d.workTapePos d.output
          ((B.runFrom raw t).liftSymbols e)).workTapes (ι 0) z = _
        rw [embedEmitCfg_selected_tape, row]
        simpa [Cfg.liftSymbols] using (FinTM.bufferTape_map e (counterWord w (d.inputPos.val + 1))
          (z - d.workTapePos 3)).symm
      · have h := (frame t j hj).1
        change (embedEmitCfg ι d.workTapes d.workTapePos d.output
          ((B.runFrom raw t).liftSymbols e)).workTapes j = d.workTapes j at h
        simpa [hj] using congrFun h z
    · funext j
      by_cases hj : j = 3
      · subst j
        change (embedEmitCfg ι d.workTapes d.workTapePos d.output
          ((B.runFrom raw t).liftSymbols e)).workTapePos (ι 0) = _
        rw [embedEmitCfg_selected_pos, row]
        rfl
      · exact (frame t j hj).2
    · simp [row, embedEmitCfg, Cfg.liftSymbols]
  · intro u hu
    rw [tr u]
    change (B.runFrom raw u).state ≠ some .done ∧ (B.runFrom raw u).state ≠ some .escape
    rw [decoded]
    exact hc u hu
  · intro u hu j
    rw [tr u]
    by_cases hj : j = 3
    · subst j
      change |(embedEmitCfg ι d.workTapes d.workTapePos d.output
        ((B.runFrom raw u).liftSymbols e)).workTapePos (ι 0) - d.workTapePos 3| ≤ _
      rw [embedEmitCfg_selected_pos]
      have h := hh u hu
      change (B.runFrom (counterLoopCfg (some (.dec .run)) c ct (d.workTapePos 3)) u).workTapePos 0 ∈ _ at h
      rw [← decoded] at h
      simp only [Finset.mem_Icc] at h
      change |(B.runFrom raw u).workTapePos 0 - d.workTapePos 3| ≤ _
      rw [abs_le]; constructor <;> omega
    · have h := (frame u j hj).2
      change (embedEmitCfg ι d.workTapes d.workTapePos d.output
        ((B.runFrom raw u).liftSymbols e)).workTapePos j = d.workTapePos j at h
      rw [h]
      simp
      omega

/-- Fuel, probe and save composed inside the existing host. The native head reaches zero,
D holds the residual all-one counter, and the saved boundary flag and starting position
are exposed for the later complement/restore phases.
**Proof sketch.** Map the copied position word to all ones. The native probe reduces its
position to at most the input length; the strict width reserve then permits the transported
Save escape. Intercept each row's exit and concatenate the three host segments. -/
private theorem recordStep_prepare_native {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List Bool}
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map (RecSym.digitEmb Q T)))
    (w : List Bool) (data : RecordStepData k Q T)
    (live : data.state ≠ none) (wide : data.widthOne = false)
    (hx : 0 < x.length) (reserve : x.length + 1 < 2 ^ w.length) :
    ∃ (b : Bool) (q t : ℕ), b = decide (d.inputPos.val = x.length + 1) ∧
      q = (if b then x.length else d.inputPos.val) ∧ q ≤ x.length ∧
      t ≤ 6 * w.length + 5 * x.length + 12 ∧
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (w.length + 1)
        (recordStepSnapshot d (recordStepReadExit data) 0
          (w.map (RecSym.digitEmb Q T)) (w.map (RecSym.digitEmb Q T)))
        (recordStepSnapshot {d with inputPos := 0}
          (⟨⟨.seek, {data with nativeRight := b}⟩, start⟩ : RecordStepControl k Q T S) 0
          (w.map (RecSym.digitEmb Q T))
          ((counterWord (List.replicate w.length true) (q + 1)).map (RecSym.digitEmb Q T))) t := by
  let e := RecSym.digitEmb Q T
  let fuel := List.replicate w.length true
  let digits := w.map e
  have len : digits.length = w.length := by simp [digits]
  have fv : Nat.ofDigits 2 (fuel.map Bool.toNat) = 2 ^ fuel.length - 1 := by
    have h := recordStep_complement_value (List.replicate w.length false)
    simpa [fuel] using h
  have fuelmap : digits.map (fun _ => RecSym.digit (Q := Q) (T := T) true) = fuel.map e := by
    simp [digits, fuel, Function.comp_def, e, RecSym.digitEmb]
  obtain ⟨mf, cf, hf⟩ := recordStep_map_snapshot d 0 digits digits digits
    (fun _ => RecSym.digit true) 3 (Or.inr rfl) (by simp) (by simp)
  have pf := recordStep_phase_run M upd seek start finish ⟨.fuel, data⟩
    (by intro b h; cases h) (recordStepSnapshot d (.fwd ()) 0 digits digits)
    (recordStepSnapshot d (.done ()) 0 digits (fuel.map e)) (2 * w.length + 2)
    (by simpa [len, fuelmap] using mf) (.done ()) rfl
    (⟨⟨.probe, data⟩, .start⟩ : RecordStepControl k Q T S) rfl
    (by intro u hu a ha; cases a with
        | done v => exact (cf u (by simpa [len] using hu) v ha).elim
        | fwd v => rfl
        | bwd v => rfl)
    d.workTapePos (w.length + 1) (by
      intro u hu j
      have h := hf j u (by simpa [len] using hu)
      by_cases hj : j = 3
      · rw [if_pos hj] at h
        simp only [Finset.mem_Icc, len] at h
        rw [abs_le]; constructor <;> omega
      · rw [if_neg hj] at h
        change |((scanTM 4 3 (scanMap (fun _ => RecSym.digit true)) scanKeep ()).runFrom
          (recordStepSnapshot d (.fwd ()) 0 digits digits) u).workTapePos j - d.workTapePos j| ≤ _
        rw [h]
        simp [recordStepSnapshot]
        omega)
  let dp := recordStepSnapshot d RecordStepProbe.start 0 digits (fuel.map e)
  obtain ⟨tp, htp, b, p, ep, cp, hb, hq, hp⟩ := recordStep_probe_run (by simpa using hx) dp rfl
  have hpx : p.val ≤ x.length := by
    have hd := d.inputPos.isLt
    simp only [List.length_map] at hb hq hd
    change p.val = (if b then x.length else d.inputPos.val) at hq
    by_cases hright : b = true
    · simp [hright] at hq
      omega
    · have bn : b = false := Bool.eq_false_iff.mpr hright
      have hn : d.inputPos.val ≠ x.length + 1 := by
        intro he
        have : b = true := by simpa [dp, recordStepSnapshot, he] using hb
        contradiction
      simp [bn] at hq
      omega
  let dq := {d with inputPos := p}
  have pp := recordStep_phase_run M upd seek start finish ⟨.probe, data⟩
    (by intro b h; cases h) dp (recordStepSnapshot dq (.done b) 0 digits (fuel.map e)) tp
    (by simpa [dp, dq, recordStepSnapshot] using ep) (.done b) rfl
    (⟨⟨.save, {data with nativeRight := b}⟩, .dec .run⟩ : RecordStepControl k Q T S) rfl
    (by intro u hu a ha; cases a with
        | done v => exact (cp u hu v ha).elim
        | start => rfl
        | peek => rfl)
    d.workTapePos (w.length + 1) (by
      intro u hu j
      change |(recordStepProbe.runFrom dp u).workTapePos j - d.workTapePos j| ≤ _
      rw [hp u hu]
      simp [dp, recordStepSnapshot]
      omega)
  let ds := recordStepSnapshot dq (CounterLoopState.dec .run : CounterLoopState Bool) 0 digits (fuel.map e)
  obtain ⟨ts, hts, es, cs, hs, _⟩ := recordStep_save_transport ds rfl hpx fuel fv
    (by
      rw [fv]
      change p.val < 2 ^ fuel.length - 1
      simp only [fuel, List.length_replicate]
      omega)
    (by intro z; simp [ds, recordStepSnapshot, e])
  let residual := (counterWord fuel (p.val + 1)).map e
  have ps := recordStep_phase_run M upd seek start finish ⟨.save, {data with nativeRight := b}⟩
    (by intro b h; cases h) ds
    (recordStepSnapshot {d with inputPos := 0} .escape 0 digits residual) ts
    (by
      refine es.trans ?_
      apply Cfg.ext <;> try rfl
      funext j z
      fin_cases j <;> simp [ds, dq, recordStepSnapshot, residual, e]) .escape rfl
    (⟨⟨.seek, {data with nativeRight := b}⟩, start⟩ : RecordStepControl k Q T S) rfl
    (by
      intro u hu a ha
      cases a with
      | escape => exact ((cs u hu).2 ha).elim
      | done => rfl
      | dec a => rfl
      | body a => rfl)
    d.workTapePos (w.length + 1) (by
      intro u hu j
      have h := hs u hu j
      simpa [ds, recordStepSnapshot, fuel, dq] using h)
  refine ⟨b, p.val, (2 * w.length + 2 + 1) + (tp + 1) + (ts + 1), ?_, ?_, hpx, ?_, ?_⟩
  · simpa [dp, recordStepSnapshot] using hb
  · simpa [List.length_map] using hq
  · change ts ≤ 5 * (p.val + 1) + 2 * fuel.length at hts
    simp only [fuel, List.length_replicate] at hts
    omega
  · have total := Segment.trans (Segment.trans pf pp) ps
    simpa [recordStepReadExit, live, wide, recordStep_mapState_mk, recordStepSnapshot,
      digits, residual, dq, dp, ds, fuel] using total

/-- The recorded seek and stationary Read, composed with their two host dispatches.
The observed symbol is exactly the source configuration's input symbol, while D and the
record frame survive intact and Cs is restored blank by the public seek contract.
**Proof sketch.** Apply the rich seek transport to B/Cs, then the native Read contract.
Input-symbol lifting and decoding identify the observation at the recorded position;
the seek radius covers both phases since Read keeps every work head fixed. -/
private theorem recordStep_seek_read {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) (C : ℕ) {x : List Bool}
    (c : Cfg k Bool Q x) (w : List Bool)
    (hspec : ∀ a : Cfg 2 Bool S x, a.state = some start →
      (∀ z : ℤ, -1 ≤ z → z ≤ (w.length : ℤ) →
        a.workTapes 0 (a.workTapePos 0 + z) = FinTM.bufferTape w z) →
      (∀ z, a.workTapes 1 z = none) →
      ∃ t ≤ C * (w.length + a.inputPos.val + c.inputPos.val + 1),
        (∀ u < t, (seek.runFrom a u).state ≠ some finish) ∧
        (∀ u ≤ t, ∀ j, |(seek.runFrom a u).workTapePos j - a.workTapePos j| ≤
          ((C * (w.length + 1) : ℕ) : ℤ)) ∧
        (seek.runFrom a t).state = some finish ∧ (seek.runFrom a t).inputPos.val = c.inputPos.val ∧
        (seek.runFrom a t).workTapes = a.workTapes ∧
        (seek.runFrom a t).workTapePos = a.workTapePos ∧ (seek.runFrom a t).output = a.output)
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map (RecSym.digitEmb Q T)))
    (blank : ∀ z, d.workTapes 2 z = none) (saved : List (RecSym Q T)) (data : RecordStepData k Q T) :
    ∃ t ≤ C * (w.length + d.inputPos.val + c.inputPos.val + 1) + 3,
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (C * (w.length + 1))
        (recordStepSnapshot d (⟨⟨.seek, data⟩, start⟩ : RecordStepControl k Q T S) 0
          (w.map (RecSym.digitEmb Q T)) saved)
        (recordStepSnapshot {d with inputPos := Fin.cast (by simp) c.inputPos}
          (⟨⟨.complement, {data with input := c.inputSymbol}⟩, .fwd ()⟩ : RecordStepControl k Q T S) 0
          (w.map (RecSym.digitEmb Q T)) saved) t := by
  let e := RecSym.digitEmb Q T
  let a := recordStepSnapshot d start 0 (w.map e) saved
  let d' : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map e) :=
    {d with inputPos := Fin.cast (by simp) c.inputPos}
  have dig : ∀ i z γ, a.workTapes (recordStepSeekBank false i) z = some γ → ∃ b, γ = e b := by
    intro i z γ h
    fin_cases i
    · change FinTM.bufferTape (w.map e) (z - d.workTapePos 1) = some γ at h
      rw [FinTM.bufferTape_map] at h
      cases hz : FinTM.bufferTape w (z - d.workTapePos 1) with
      | none => simp [hz] at h
      | some b => exact ⟨b, by simpa [hz] using h.symm⟩
    · simp [a, recordStepSnapshot, recordStepSeekBank, blank] at h
  obtain ⟨ts, hts, esCut, esHeads, es⟩ := recordStep_seek_transport seek start finish C
    c.inputPos.val w (by have := c.inputPos.isLt; omega) hspec (recordStepSeekBank false) a rfl dig
    (by intro z _ _; simp [a, recordStepSnapshot, recordStepSeekBank, e])
    (by intro z; simp [a, recordStepSnapshot, recordStepSeekBank, blank])
  have ps := recordStep_phase_run M upd seek start finish ⟨.seek, data⟩
    (by intro b h; cases h) a (recordStepSnapshot d' finish 0 (w.map e) saved) ts
    (by
      refine es.trans ?_
      apply Cfg.ext <;> rfl) finish rfl
    (⟨⟨.read, data⟩, none⟩ : RecordStepControl k Q T S)
    (by simp [recordStepNext])
    (by
      intro u hu q hq
      have hn : q ≠ finish := by intro he; subst q; exact esCut u hu hq
      simp [recordStepNext, hn])
    d.workTapePos (C * (w.length + 1)) (by
      intro u hu j
      simpa [a, recordStepSnapshot] using esHeads u hu j)
  let r := recordStepSnapshot d' (none : Option (Option Bool)) 0 (w.map e) saved
  have input : r.inputSymbol.bind (decodeBool e) = c.inputSymbol := by
    change (c.liftSymbols e).inputSymbol.bind (decodeBool e) = c.inputSymbol
    rw [Cfg.liftSymbols_inputSymbol]
    cases c.inputSymbol <;> simp [decodeBool_apply]
  obtain ⟨er, cr⟩ := recordStep_read_run r rfl
  have fixed (u : ℕ) : (recordStepRead.runFrom r u).workTapePos = r.workTapePos :=
    (recordStep_native_frame recordStepRead (fun _ _ => 0)
      (fun _ inp => some (inp.bind (decodeBool e))) (by intro q inp work; rfl) r u).2.1
  have pr := recordStep_phase_run M upd seek start finish ⟨.read, data⟩
    (by intro b h; cases h) r (recordStepSnapshot d' (some c.inputSymbol) 0 (w.map e) saved) 1
    (by
      change r.inputSymbol.bind (decodeBool (RecSym.digitEmb Q T)) = c.inputSymbol at input
      rw [input] at er
      exact er) (some c.inputSymbol) rfl
    (⟨⟨.complement, {data with input := c.inputSymbol}⟩, .fwd ()⟩ : RecordStepControl k Q T S) rfl
    (by intro u hu q hq; cases q with
        | some v => exact (cr u hu v hq).elim
        | none => rfl)
    d.workTapePos (C * (w.length + 1)) (by
      intro u hu j
      change |(recordStepRead.runFrom r u).workTapePos j - d.workTapePos j| ≤ _
      rw [fixed u]
      simp [r, d', recordStepSnapshot])
  refine ⟨(ts + 1) + (1 + 1), by change ts ≤ C * (w.length + d.inputPos.val + c.inputPos.val + 1) at hts; omega, ?_⟩
  simpa [a, r, d', recordStep_mapState_mk, recordStepSnapshot] using Segment.trans ps pr

/-- Carry and borrow on a dedicated digit tape preserve the rich frame and native data.
The same transport serves D's saved-position borrow and both F1 arithmetic branches.
**Proof sketch.** Select the public framed carry or borrow contract on the decoded
singleton bank. The existing R1 wrapper transports its entire prefix. Equal word lengths
turn the framed replacement into a global buffer; the R1 frame preserves every other tape. -/
private theorem recordStep_arithmetic_transport {Q T : Type} [DecidableEq Q] [DecidableEq T]
    {x : List Bool} (increase : Bool) (i : Fin 3) (w v : List Bool)
    (hv : (if increase then incFixed w else decFixed w) = some v) (hlen : v.length = w.length)
    (d : Cfg 4 (RecSym Q T) FlagPhase (x.map (RecSym.digitEmb Q T)))
    (hd : d.state = some .run)
    (hw : ∀ z, d.workTapes (recordStepDigitBank i 0) z =
      FinTM.bufferTape (w.map (RecSym.digitEmb Q T)) (z - d.workTapePos (recordStepDigitBank i 0))) :
    ∃ t ≤ 2 * w.length + 2,
      let R := embedEmitTM (recordStepDigitBank i)
        ((if increase then incrementTM 1 0 else decrementTM 1 0).liftSymbols (RecSym.digitEmb Q T))
      R.runFrom d t =
        {d with
          state := some (.done true)
          workTapes := fun j z =>
            if j = recordStepDigitBank i 0 then
              FinTM.bufferTape (v.map (RecSym.digitEmb Q T)) (z - d.workTapePos j)
            else d.workTapes j z} ∧
      (∀ u < t, ∀ b, (R.runFrom d u).state ≠ some (.done b)) ∧
      (∀ u ≤ t, ∀ j, |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ ((w.length + 1 : ℕ) : ℤ)) := by
  let e := RecSym.digitEmb Q T
  let bank := recordStepDigitBank i
  let row := if increase then incrementTM 1 0 else decrementTM 1 0
  let p := (w.takeWhile (if increase then id else not)).length
  let raw : Cfg 1 Bool FlagPhase x := ⟨d.state, Fin.cast (by simp) d.inputPos,
    (fun j z => (d.workTapes (bank j) z).bind (decodeBool e)), (fun j => d.workTapePos (bank j)), []⟩
  have rawTape (j : Fin 1) (z : ℤ) :
      raw.workTapes j z = FinTM.bufferTape w (z - raw.workTapePos j) := by
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change (d.workTapes (bank 0) z).bind (decodeBool e) = _
    rw [hw]
    exact FinTM.bufferTape_map_decode e w _
  have delim : ∀ z : ℤ, -1 ≤ z → z ≤ (w.length : ℤ) →
      raw.workTapes 0 (raw.workTapePos 0 + z) = FinTM.bufferTape w z := by
    intro z _ _
    simp only [rawTape, add_sub_cancel_left]
  have spec : row.runFrom raw (2 * p + 2) =
      {raw with
        state := some (.done true)
        workTapes := fun j z =>
          if j = 0 ∧ raw.workTapePos j ≤ z ∧ z < raw.workTapePos j + (w.length : ℤ)
            then FinTM.bufferTape v (z - raw.workTapePos j) else raw.workTapes j z} ∧
      (∀ u < 2 * p + 2, ∀ b, (row.runFrom raw u).state ≠ some (.done b)) ∧
      (∀ (j : Fin 1) (u : ℕ), u ≤ 2 * p + 2 →
        if j = 0 then (row.runFrom raw u).workTapePos j ∈
          Finset.Icc (raw.workTapePos j - 1) (raw.workTapePos j + (p : ℤ))
        else (row.runFrom raw u).workTapePos j = raw.workTapePos j) := by
    cases increase
    · exact decrementTM_run_succ_ofCfg 0 w v hv raw hd delim
    · exact incrementTM_run_succ_ofCfg 0 w v hv raw hd delim
  let last : Cfg 1 Bool FlagPhase x :=
    {raw with state := some (.done true), workTapes := fun j z => FinTM.bufferTape v (z - raw.workTapePos j)}
  have result : row.runFrom raw (2 * p + 2) = last := by
    rw [spec.1]
    apply Cfg.ext <;> try rfl
    funext j z
    have hj : j = 0 := Subsingleton.elim _ _
    simp only [hj, true_and]
    dsimp only [last]
    split_ifs with hz
    · rfl
    · rw [rawTape]
      by_cases hneg : 0 ≤ z - raw.workTapePos 0
      · have hlarge : w.length ≤ (z - raw.workTapePos 0).toNat := by omega
        simp only [FinTM.bufferTape, if_pos hneg, List.getElem?_eq_none hlarge,
          List.getElem?_eq_none (by omega : v.length ≤ (z - raw.workTapePos 0).toNat)]
      · simp only [FinTM.bufferTape, if_neg hneg]
  have digits : ∀ j z γ, d.workTapes (bank j) z = some γ → ∃ b, γ = e b := by
    intro j z γ h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rw [hw, FinTM.bufferTape_map] at h
    change (FinTM.bufferTape w (z - d.workTapePos (bank 0))).map e = some γ at h
    cases hcell : FinTM.bufferTape w (z - d.workTapePos (bank 0)) with
    | none => simp [hcell] at h
    | some b => exact ⟨b, by simpa [hcell] using h.symm⟩
  have tr (u : ℕ) := recordStep_transport row e bank d digits u
  have untouched (u : ℕ) (j : Fin 4) (hj : j ≠ bank 0) :=
    (embedEmitTM_frame bank (row.liftSymbols e) d.workTapes d.workTapePos d.output
      ((row.runFrom raw u).liftSymbols e) 0).1 j (by
        rintro ⟨a, ha⟩
        exact hj (ha ▸ congrArg bank (Subsingleton.elim a 0)))
  have hp : p ≤ w.length := (List.takeWhile_sublist _).length_le
  refine ⟨2 * p + 2, by omega, ?_, ?_, ?_⟩
  · rw [tr, result]
    apply Cfg.ext
    · rfl
    · apply Fin.ext; rfl
    · funext j z
      by_cases hj : j = bank 0
      · subst j
        rw [embedEmitCfg_selected_tape]
        simpa [last, raw, bank, e, Cfg.liftSymbols] using (FinTM.bufferTape_map e v (z - d.workTapePos (bank 0))).symm
      · have h := (untouched (2 * p + 2) j hj).1
        rw [result] at h
        simpa only [← show bank = recordStepDigitBank i from rfl, if_neg hj, MultiTapeTM.runFrom_zero] using congrFun h z
    · funext j
      by_cases hj : j = bank 0
      · subst j
        rw [embedEmitCfg_selected_pos]
        rfl
      · have h := (untouched (2 * p + 2) j hj).2
        rw [result] at h
        exact h
    · simp [embedEmitCfg, last, raw, Cfg.liftSymbols]
  · intro u hu b
    rw [tr]
    exact spec.2.1 u hu b
  · intro u hu j
    rw [tr]
    by_cases hj : j = bank 0
    · subst j
      rw [embedEmitCfg_selected_pos]
      have h := spec.2.2 0 u hu
      change (row.runFrom raw u).workTapePos 0 ∈ Finset.Icc (raw.workTapePos 0 - 1) (raw.workTapePos 0 + (p : ℤ)) at h
      simp only [Finset.mem_Icc] at h
      change |(row.runFrom raw u).workTapePos 0 - raw.workTapePos 0| ≤ _
      rw [abs_le]; constructor <;> omega
    · have h := (untouched u j hj).2
      change (embedEmitCfg bank d.workTapes d.workTapePos d.output
        ((row.runFrom raw u).liftSymbols e)).workTapePos j = d.workTapePos j at h
      rw [h]
      simp
      omega


/-- Complement and the optional borrow turn the residual fuel into the saved position.
No native movement occurs, and both scratch heads return to their entry positions.
**Proof sketch.** The inherited fuel-complement identity determines the mapped word.
The right-boundary flag skips the borrow; otherwise the public predecessor contract,
through the shared arithmetic transport, changes q+1 to q. Intercept both row exits. -/
private theorem recordStep_restore_digits {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List Bool}
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map (RecSym.digitEmb Q T)))
    (b : List (RecSym Q T)) (data : RecordStepData k Q T) (W q p : ℕ)
    (hq : q + 1 < 2 ^ W) (hp : p = if data.nativeRight then q + 1 else q) :
    ∃ t ≤ 4 * W + 6,
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (W + 1)
        (recordStepSnapshot d (⟨⟨.complement, data⟩, .fwd ()⟩ : RecordStepControl k Q T S) 0 b
          ((counterWord (List.replicate W true) (q + 1)).map (RecSym.digitEmb Q T)))
        (recordStepSnapshot d (⟨⟨.restore, data⟩, start⟩ : RecordStepControl k Q T S) 0 b
          ((binDigits W p).map (RecSym.digitEmb Q T))) t := by
  let e := RecSym.digitEmb Q T
  let fuel := List.replicate W true
  let residual := (counterWord fuel (q + 1)).map e
  let successor := (binDigits W (q + 1)).map e
  let complement : RecSym Q T → RecSym Q T := fun γ => match γ with
    | .digit b => .digit (!b) | γ => γ
  have len : residual.length = W := by simp [residual, fuel, counterWord_length]
  have mapped : residual.map complement = successor := by
    have fv : Nat.ofDigits 2 (fuel.map Bool.toNat) = 2 ^ fuel.length - 1 := by
      simpa [fuel] using recordStep_complement_value (List.replicate W false)
    have hs := recordStep_saved_digits fuel q fv (by simpa [fuel] using hq)
    have hmap : residual.map complement = ((counterWord fuel (q + 1)).map not).map e := by
      simp [residual, List.map_map, Function.comp_def, complement, e, RecSym.digitEmb]
    rw [hmap, hs]
    simp only [successor, fuel, List.length_replicate]
  obtain ⟨em, cm, hm⟩ := recordStep_map_snapshot d 0 b residual residual complement 3
    (Or.inr rfl) (by simp) (by simp)
  let next : RecordStepControl k Q T S := if data.nativeRight then ⟨⟨.restore, data⟩, start⟩
    else ⟨⟨.decrementD, data⟩, .run⟩
  have pm := recordStep_phase_run M upd seek start finish ⟨.complement, data⟩
    (by intro b h; cases h) (recordStepSnapshot d (.fwd ()) 0 b residual)
    (recordStepSnapshot d (.done ()) 0 b successor) (2 * W + 2)
    (by simpa [len, mapped] using em) (.done ()) rfl next
    (by cases h : data.nativeRight <;> simp [recordStepNext, next, h])
    (by intro u hu a ha; cases a with
        | done v => exact (cm u (by simpa [len] using hu) v ha).elim
        | fwd v => rfl
        | bwd v => rfl)
    d.workTapePos (W + 1) (by
      intro u hu j
      have h := hm j u (by simpa [len] using hu)
      by_cases hj : j = 3
      · rw [if_pos hj] at h
        simp only [Finset.mem_Icc, len] at h
        rw [abs_le]; constructor <;> omega
      · rw [if_neg hj] at h
        change |((scanTM 4 3 (scanMap complement) scanKeep ()).runFrom
          (recordStepSnapshot d (.fwd ()) 0 b residual) u).workTapePos j - d.workTapePos j| ≤ _
        rw [h]
        simp [recordStepSnapshot]
        omega)
  cases flag : data.nativeRight with
  | true =>
    have hp' : p = q + 1 := by simpa [flag] using hp
    refine ⟨2 * W + 2 + 1, by omega, ?_⟩
    simpa [next, flag, hp', successor, residual, fuel, e, recordStep_mapState_mk, recordStepSnapshot] using pm
  | false =>
    have hp' : p = q := by simpa [flag] using hp
    let a := recordStepSnapshot d FlagPhase.run 0 b successor
    obtain ⟨td, htd, ed, cd, hd⟩ := recordStep_arithmetic_transport false 2
      (binDigits W (q + 1)) (binDigits W q) (recordStep_digits_succ W q hq).2
      (by simp [binDigits]) a rfl (by intro z; simp [a, recordStepSnapshot, recordStepDigitBank, successor, e])
    have pd := recordStep_phase_run M upd seek start finish ⟨.decrementD, data⟩
      (by intro b h; cases h) a (recordStepSnapshot d (.done true) 0 b ((binDigits W q).map e)) td
      (by
        refine ed.trans ?_
        apply Cfg.ext <;> try rfl
        funext j z
        fin_cases j <;> simp [a, recordStepSnapshot, recordStepDigitBank, e]) (.done true) rfl
      (⟨⟨.restore, data⟩, start⟩ : RecordStepControl k Q T S) rfl
      (by intro u hu a ha; cases a with
          | done v => exact (cd u hu v ha).elim
          | run => rfl
          | rewind v => rfl)
      d.workTapePos (W + 1) (by
        intro u hu j
        simpa [a, recordStepSnapshot, binDigits] using hd u hu j)
    have pm' : RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (W + 1)
        (recordStepSnapshot d (⟨⟨.complement, data⟩, .fwd ()⟩ : RecordStepControl k Q T S) 0 b residual)
        (a.mapState (Sigma.mk (⟨.decrementD, data⟩ : RecordStepIndex k Q T))) (2 * W + 2 + 1) := by
      simpa [a, next, flag, recordStep_mapState_mk, recordStepSnapshot] using pm
    refine ⟨(2 * W + 2 + 1) + (td + 1), ?_, ?_⟩
    · simp only [binDigits, List.length_map, List.length_range] at htd
      omega
    · simpa [hp', residual, fuel, e, recordStep_mapState_mk, recordStepSnapshot] using Segment.trans pm' pd


/-- The public input-seek witness's contract, retained verbatim as a private parameter
for the native-cycle composition. This abbreviation adds no machine or proof. -/
private def RecordStepSeekSpec {S : Type} (seek : MultiTapeTM 2 Bool S) (start finish : S) (C : ℕ) : Prop :=
  ∀ {x : List Bool} (p : ℕ) (w : List Bool), Nat.ofDigits 2 (w.map Bool.toNat) = p →
    p ≤ x.length + 1 → ∀ a : Cfg 2 Bool S x, a.state = some start →
    (∀ z : ℤ, -1 ≤ z → z ≤ (w.length : ℤ) →
      a.workTapes 0 (a.workTapePos 0 + z) = FinTM.bufferTape w z) →
    (∀ z, a.workTapes 1 z = none) →
    ∃ t ≤ C * (w.length + a.inputPos.val + p + 1),
      (∀ u < t, (seek.runFrom a u).state ≠ some finish) ∧
      (∀ u ≤ t, ∀ j, |(seek.runFrom a u).workTapePos j - a.workTapePos j| ≤
        ((C * (w.length + 1) : ℕ) : ℤ)) ∧
      (seek.runFrom a t).state = some finish ∧ (seek.runFrom a t).inputPos.val = p ∧
      (seek.runFrom a t).workTapes = a.workTapes ∧
      (seek.runFrom a t).workTapePos = a.workTapePos ∧ (seek.runFrom a t).output = a.output

/-- I6–I9 restore the arbitrary native entry position and erase D globally.
The record, B, Cs and output are unchanged; all heads return, with width-only work radius.
**Proof sketch.** Compose the complemented saved digits and optional borrow with the
public seek on D/Cs. Its exact endpoint restores the original native position and blank
Cs. Clear D with the existing scratch specialization and dispatch to the apply stage. -/
private theorem recordStep_restore_native {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) (C : ℕ)
    (hseek : RecordStepSeekSpec seek start finish C) {x : List Bool}
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map (RecSym.digitEmb Q T)))
    (pos : Fin ((x.map (RecSym.digitEmb Q T)).length + 2))
    (b : List (RecSym Q T)) (data : RecordStepData k Q T) (W q : ℕ)
    (blank : ∀ z, d.workTapes 2 z = none)
    (hq : q + 1 < 2 ^ W) (hp : d.inputPos.val = if data.nativeRight then q + 1 else q) :
    ∃ t ≤ C * (W + pos.val + d.inputPos.val + 1) + 6 * W + 10,
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos ((C + 1) * (W + 1))
        (recordStepSnapshot {d with inputPos := pos}
          (⟨⟨.complement, data⟩, .fwd ()⟩ : RecordStepControl k Q T S) 0 b
          ((counterWord (List.replicate W true) (q + 1)).map (RecSym.digitEmb Q T)))
        (recordStepSnapshot d (recordStepApply M data) 0 b []) t := by
  let e := RecSym.digitEmb Q T
  let cur := {d with inputPos := pos}
  let w := binDigits W d.inputPos.val
  have len : w.length = W := by simp [w, binDigits]
  have hval : d.inputPos.val < 2 ^ W := by
    cases flag : data.nativeRight <;> simp [flag] at hp <;> omega
  have hpx : d.inputPos.val ≤ x.length + 1 := by
    have := d.inputPos.isLt
    simp only [List.length_map] at this
    omega
  obtain ⟨ta, hta, pa⟩ := recordStep_restore_digits M upd seek start finish cur b data W q d.inputPos.val hq hp
  let a := recordStepSnapshot cur start 0 b (w.map e)
  have dig : ∀ i z γ, a.workTapes (recordStepSeekBank true i) z = some γ → ∃ v, γ = e v := by
    intro i z γ h
    fin_cases i
    · change FinTM.bufferTape (w.map e) (z - d.workTapePos 3) = some γ at h
      rw [FinTM.bufferTape_map] at h
      cases hz : FinTM.bufferTape w (z - d.workTapePos 3) with
      | none => simp [hz] at h
      | some v => exact ⟨v, by simpa [hz] using h.symm⟩
    · simp [a, cur, recordStepSnapshot, recordStepSeekBank, blank] at h
  obtain ⟨ts, hts, cs, hs, es⟩ := recordStep_seek_transport seek start finish C d.inputPos.val w hpx
    (hseek _ w (record_digits_value W _ hval) hpx) (recordStepSeekBank true) a rfl dig
    (by intro z _ _; simp [a, cur, recordStepSnapshot, recordStepSeekBank, e])
    (by intro z; simp [a, cur, recordStepSnapshot, recordStepSeekBank, blank])
  have ps := recordStep_phase_run M upd seek start finish ⟨.restore, data⟩
    (by intro b h; cases h) a (recordStepSnapshot d finish 0 b (w.map e)) ts
    (by
      refine es.trans ?_
      apply Cfg.ext <;> rfl) finish rfl
    (⟨⟨.clearD, data⟩, .sweep⟩ : RecordStepControl k Q T S)
    (by simp [recordStepNext])
    (by
      intro u hu q hq
      have hn : q ≠ finish := fun he => cs u hu (he ▸ hq)
      simp [recordStepNext, hn])
    d.workTapePos (C * (W + 1)) (by
      intro u hu j
      simpa [a, cur, recordStepSnapshot, len] using hs u hu j)
  obtain ⟨ec, cc, _⟩ := recordStep_clear_snapshot d 0 b (w.map e) (w.map e) 3
    (Or.inr rfl) (by simp) (by simp)
  have pc := recordStep_phase_run M upd seek start finish ⟨.clearD, data⟩
    (by intro b h; cases h) (recordStepSnapshot d .sweep 0 b (w.map e))
    (recordStepSnapshot d .done 0 b []) (2 * W + 2) (by simpa [len] using ec) .done rfl
    (recordStepApply M data) rfl
    (by intro u hu q hq; cases q with
        | done => exact (cc u (by simpa [len] using hu) hq).elim
        | sweep => rfl
        | rewind => rfl)
    d.workTapePos (W + 1) (by
      simpa [len] using recordStep_clear_heads d b (w.map e) (w.map e) 3
        (Or.inr rfl) (by simp) (by simp))
  have small : W + 1 ≤ (C + 1) * (W + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have seekBound : C * (W + 1) ≤ (C + 1) * (W + 1) := Nat.mul_le_mul_right _ (by omega)
  have pa' := Segment.mono pa (fun _ hx => hx) (record_headBox_mono small)
  have ps' := Segment.mono ps (fun _ hx => hx) (record_headBox_mono seekBound)
  have pc' := Segment.mono pc (fun _ hx => hx) (record_headBox_mono small)
  have total := Segment.trans pa' (by
    simpa [a, cur, w, recordStep_mapState_mk, recordStepSnapshot] using Segment.trans ps' pc')
  refine ⟨ta + ((ts + 1) + (2 * W + 2 + 1)), ?_, ?_⟩
  · change ts ≤ C * (w.length + pos.val + d.inputPos.val + 1) at hts
    rw [len] at hts
    omega
  · simpa [cur, recordStep_mapState_mk, recordStepSnapshot] using total


/-- The whole live-source native cycle, including empty input, ends at apply dispatch.
It reads the source's input symbol, restores the arbitrary host input position and output,
and leaves only B nonblank. The work radius depends only on the position-word width.
**Proof sketch.** Width one takes the already proved empty-input clear. Otherwise join
fuel/probe/save, recorded seek/read, and complement/borrow/restore/clear. The probe flag
identifies the original right boundary; the shared digit decoder supplies both seeks. -/
private theorem recordStep_live_native {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) (C : ℕ)
    (hseek : RecordStepSeekSpec seek start finish C) {x : List Bool}
    (c : Cfg k Bool Q x)
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map (RecSym.digitEmb Q T)))
    (data : RecordStepData k Q T) (live : data.state ≠ none)
    (width : data.widthOne = decide (posWidth x.length = 1))
    (blank : ∀ z, d.workTapes 2 z = none) :
    ∃ (b : Bool) (t : ℕ), t ≤ 20 * (C + 1) * (posWidth x.length + x.length + 1) ∧
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos
        ((C + 1) * (posWidth x.length + 1))
        (recordStepSnapshot d (recordStepReadExit data) 0
          ((binDigits (posWidth x.length) c.inputPos.val).map (RecSym.digitEmb Q T))
          ((binDigits (posWidth x.length) c.inputPos.val).map (RecSym.digitEmb Q T)))
        (recordStepSnapshot d (recordStepApply M {data with nativeRight := b, input := c.inputSymbol}) 0
          ((binDigits (posWidth x.length) c.inputPos.val).map (RecSym.digitEmb Q T)) []) t := by
  let e := RecSym.digitEmb Q T
  let W := posWidth x.length
  let w := binDigits W c.inputPos.val
  have len : w.length = W := by simp [w, binDigits]
  have small : W + 1 ≤ (C + 1) * (W + 1) := Nat.le_mul_of_pos_left _ (by omega)
  by_cases empty : x.length = 0
  · have one : data.widthOne = true := by
      rw [width, decide_eq_true_eq]
      exact (recordStep_width_one x.length).mpr empty
    have inp : c.inputSymbol = none := by
      apply (recordStep_input_blank c).mpr
      have h := c.inputPos.isLt
      omega
    have run := recordStep_empty_run M upd seek start finish d (w.map e) data live one
    refine ⟨data.nativeRight, 2 * W + 3, ?_, ?_⟩
    · have hC : 1 ≤ C + 1 := by omega
      change 2 * W + 3 ≤ 20 * (C + 1) * (W + x.length + 1)
      nlinarith
    · have widened := Segment.mono run (fun _ hx => hx)
        (record_headBox_mono (r' := (C + 1) * (W + 1)) (by
          simpa only [List.length_map, len] using small))
      simpa [inp, len, w, W, e] using widened
  · have hx : 0 < x.length := by omega
    have wide : data.widthOne = false := by
      rw [width, decide_eq_false_iff_not]
      exact fun h => empty ((recordStep_width_one x.length).mp h)
    obtain ⟨b, q, tp, hb, hq, hqx, htp, prep⟩ := recordStep_prepare_native M upd seek start finish d w data
      live wide hx (by simpa [len, W] using record_pos_lt x.length)
    have hcp : c.inputPos.val ≤ x.length + 1 := by have := c.inputPos.isLt; omega
    have hdp : d.inputPos.val ≤ x.length + 1 := by
      have := d.inputPos.isLt
      simp only [List.length_map] at this
      omega
    have hv : Nat.ofDigits 2 (w.map Bool.toNat) = c.inputPos.val :=
      record_digits_value W _ (lt_of_le_of_lt hcp (record_pos_lt x.length))
    let data' := {data with nativeRight := b, input := c.inputSymbol}
    let saved := (counterWord (List.replicate w.length true) (q + 1)).map e
    obtain ⟨ts, hts, read⟩ := recordStep_seek_read M upd seek start finish C c w
      (hseek _ w hv hcp) {d with inputPos := 0} blank saved {data with nativeRight := b}
    have restored : d.inputPos.val = if data'.nativeRight then q + 1 else q := by
      cases b
      · simpa [data'] using hq.symm
      · have hd : d.inputPos.val = x.length + 1 := by simpa using hb.symm
        simpa [data', hq] using hd
    obtain ⟨tr, htr, restore⟩ := recordStep_restore_native M upd seek start finish C hseek d
      (Fin.cast (by simp) c.inputPos) (w.map e) data' W q blank
      (lt_of_le_of_lt (by omega : q + 1 ≤ x.length + 1) (record_pos_lt x.length)) restored
    have prep' := Segment.mono prep (fun _ hx => hx)
      (record_headBox_mono (r' := (C + 1) * (W + 1)) (by
        simpa only [List.length_map, len] using small))
    have read' := Segment.mono read (fun _ hx => hx)
      (record_headBox_mono (r' := (C + 1) * (W + 1)) (by
        rw [len]
        exact Nat.mul_le_mul_right (W + 1) (by omega : C ≤ C + 1)))
    have first := Segment.trans prep' read'
    have total := Segment.trans first (by
      simpa [data', saved, len, recordStepSnapshot, e] using restore)
    refine ⟨b, tp + ts + tr, ?_, ?_⟩
    · change tp ≤ 6 * w.length + 5 * x.length + 12 at htp
      change ts ≤ C * (w.length + 0 + c.inputPos.val + 1) + 3 at hts
      change tr ≤ C * (W + c.inputPos.val + d.inputPos.val + 1) + 6 * W + 10 at htr
      rw [len] at htp hts
      change tp + ts + tr ≤ 20 * (C + 1) * (W + x.length + 1)
      nlinarith
    · simpa [w, W, e, data', recordStepSnapshot] using total


/-- The fully collected observations select exactly the source transition and its window test.
The saved native-boundary flag does not affect either decision.
**Proof sketch.** At a live source state all tape slots have been read. Substitute their
symbols and boundary flags, then apply the inherited outward-move/window equivalence. -/
private theorem recordStep_observed_action {k : ℕ} {Q T : Type} {x : List Bool}
    (M : MultiTapeTM k Bool Q) (s : ℕ) (c : Cfg k Bool Q x) (τ : T) (b : Bool)
    (hc : c.InWindow s) (live : c.state ≠ none) :
    let data := {recordStepReadData (T := T) s c k with tag := some τ, nativeRight := b, input := c.inputSymbol}
    (recordStepAction M data).apply c = M.step c ∧
      (recordStepAction M data).output = M.outputSymbol c ∧
      (recordStepOutside M data = false ↔ (M.step c).InWindow s) := by
  dsimp only
  let data := {recordStepReadData (T := T) s c k with tag := some τ, nativeRight := b, input := c.inputSymbol}
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp live
  have symbols : data.symbols = c.workTapeSymbols := by
    funext i
    simp [data, recordStepReadData, Cfg.workTapeSymbols]
  have action : recordStepAction M data = M.tr q c.inputSymbol c.workTapeSymbols := by
    dsimp only [recordStepAction]
    change (match c.state with
      | some q => M.tr q c.inputSymbol data.symbols
      | none => _) = _
    rw [hq, symbols]
  have step : (recordStepAction M data).apply c = M.step c := by
    rw [action, MultiTapeTM.step, hq]
  refine ⟨step, ?_, ?_⟩
  · rw [action, MultiTapeTM.outputSymbol, hq]
  · rw [← step, recordStep_window s c hc]
    simp [recordStepOutside, data, recordStepReadData, not_exists, not_or]


/-- The two record-tape scans write the old marked cell and shift its mark exactly once.
They leave the head at the same field, ready for its skip, with all other data framed.
**Proof sketch.** Apply the public map scan to the marked write, then the public scan
contract for the move's delay transducer. The inherited tape-word identity identifies
their composite word with the source action's field. Both exits are intercepted by
the existing host, and both trajectories stay in the same delimited field. -/
private theorem recordStep_tape_run {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List Bool}
    (s : ℕ) (c : Cfg k Bool Q x) (hc : c.InWindow s) (data : RecordStepData k Q T) (i : Fin k)
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map (RecSym.digitEmb Q T)))
    (hw : ∀ z : ℤ, -1 ≤ z → z ≤ (2 * s + 1 : ℕ) →
      d.workTapes 0 (d.workTapePos 0 + z) = FinTM.bufferTape
        ((List.range (2 * s + 1)).map fun (r : ℕ) =>
          RecSym.cell (c.workTapes i ((r : ℤ) - s)) (decide (c.workTapePos i = (r : ℤ) - s))) z) :
    RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (2 * s + 2)
      {d with state := some ⟨⟨.writeTape i, data⟩, .fwd ()⟩}
      {d with
        state := some ⟨⟨.skipNewTape i, data⟩, .run⟩
        workTapes := fun j z =>
          if j = 0 ∧ d.workTapePos j ≤ z ∧ z < d.workTapePos j + (2 * s + 1 : ℕ) then
            FinTM.bufferTape ((List.range (2 * s + 1)).map fun (r : ℕ) =>
              RecSym.cell (((recordStepAction M data).apply c).workTapes i ((r : ℤ) - s))
                (decide (((recordStepAction M data).apply c).workTapePos i = (r : ℤ) - s)))
              (z - d.workTapePos j)
          else d.workTapes j z} (4 * (2 * s + 1) + 6) := by
  let old : List (RecSym Q T) := (List.range (2 * s + 1)).map fun (r : ℕ) =>
    .cell (c.workTapes i ((r : ℤ) - s)) (decide (c.workTapePos i = (r : ℤ) - s))
  let a := recordStepAction M data
  let write := recordStepWriteCell (Q := Q) (T := T) (a.workTapes i).1
  let written := old.map write
  let patch := fun (v : List (RecSym Q T)) (j : Fin 4) (z : ℤ) =>
    if j = 0 ∧ d.workTapePos j ≤ z ∧ z < d.workTapePos j + (old.length : ℤ)
      then FinTM.bufferTape v (z - d.workTapePos j) else d.workTapes j z
  let first : Cfg 4 (RecSym Q T) (ScanPhase Unit) (x.map (RecSym.digitEmb Q T)) :=
    ⟨some (.fwd ()), d.inputPos, d.workTapes, d.workTapePos, d.output⟩
  have len : old.length = 2 * s + 1 := by simp [old]
  have wlen : written.length = old.length := by simp [written]
  obtain ⟨e1, c1, h1⟩ := recordStep_contract_clauses_range
    (scanTM_contract (0 : Fin 4) (scanMap write) scanKeep () _) old first rfl
    (by rw [scanTM_contract_pre]; simpa only [first, len] using hw)
  rw [scanTM_contract_time, scanTM_contract_post] at e1
  simp only [scanTM_contract_time, scanTM_contract_lo, scanTM_contract_hi] at c1 h1
  rw [scanResult_map] at e1
  let middle : Cfg 4 (RecSym Q T) (ScanPhase Bool) (x.map (RecSym.digitEmb Q T)) :=
    ⟨some (.fwd false), d.inputPos, patch written, d.workTapePos, d.output⟩
  have midword : ∀ z : ℤ, -1 ≤ z → z ≤ (written.length : ℤ) →
      middle.workTapes 0 (middle.workTapePos 0 + z) = FinTM.bufferTape written z := by
    intro z hz hu
    dsimp only [middle, patch]
    split_ifs with hin
    · simp
    · have hend : z = -1 ∨ z = (old.length : ℤ) := by rw [wlen] at hu; omega
      rw [hw z hz (by simpa only [← len, wlen] using hu)]
      rcases hend with rfl | rfl
      · simp
      · simp [FinTM.bufferTape, wlen, len]
  let f : Bool → RecSym Q T → Bool × RecSym Q T := match (a.workTapes i).2 with
    | .pos => scanShift recordStepGetMark recordStepSetMark | _ => scanKeep
  let g : Bool → RecSym Q T → Bool × RecSym Q T := match (a.workTapes i).2 with
    | .neg => scanShift recordStepGetMark recordStepSetMark | _ => scanKeep
  let result := scanResult f g false written
  obtain ⟨e2, c2, h2⟩ := recordStep_contract_clauses_range
    (scanTM_contract (0 : Fin 4) f g false _) written middle rfl
    (by rw [scanTM_contract_pre]; exact midword)
  rw [scanTM_contract_time, scanTM_contract_post] at e2
  simp only [scanTM_contract_time, scanTM_contract_lo, scanTM_contract_hi] at c2 h2
  have word : result.2 = (List.range (2 * s + 1)).map fun (r : ℕ) =>
      RecSym.cell ((a.apply c).workTapes i ((r : ℤ) - s))
        (decide ((a.apply c).workTapePos i = (r : ℤ) - s)) := by
    have h := recordStep_tape_word (T := T) s c hc a i
    dsimp only at h
    rw [scanResult_map] at h
    cases hm : (a.workTapes i).2 <;> simpa [result, f, g, hm, written, write, old] using h
  have bounded {A : Type} (row : MultiTapeTM 4 (RecSym Q T) A)
      (base : Cfg 4 (RecSym Q T) A (x.map (RecSym.digitEmb Q T))) (n : ℕ)
      (he : base.workTapePos = d.workTapePos)
      (hh : ∀ j u, u ≤ n → (row.runFrom base u).workTapePos j ∈
        Finset.Icc (if j = 0 then base.workTapePos j - 1 else base.workTapePos j)
          (if j = 0 then base.workTapePos j + (old.length : ℤ) else base.workTapePos j)) :
      ∀ u ≤ n, ∀ j, |(row.runFrom base u).workTapePos j - d.workTapePos j| ≤ ((2 * s + 2 : ℕ) : ℤ) := by
    intro u hu j
    have h := hh j u hu
    rw [he] at h
    split_ifs at h with hj
    · simp only [Finset.mem_Icc, len] at h
      rw [abs_le]; constructor <;> omega
    · rw [Finset.mem_Icc] at h
      rw [le_antisymm h.2 h.1]
      simp
      omega
  have p1 := recordStep_phase_run M upd seek start finish ⟨.writeTape i, data⟩
    (by intro b h; cases h) first
    (⟨some (.done ()), d.inputPos, patch written, d.workTapePos, d.output⟩) (2 * old.length + 2)
    e1 (.done ()) rfl (⟨⟨.shiftTape i, data⟩, .fwd false⟩ : RecordStepControl k Q T S) rfl
    (by intro u hu q hq; cases q with
        | done v => exact (c1 u hu v hq).elim
        | fwd v => rfl
        | bwd v => rfl)
    d.workTapePos (2 * s + 2) (bounded _ first _ rfl h1)
  have row2 : recordStepRows M upd seek ⟨.shiftTape i, data⟩ = scanTM 4 0 f g false := by
    cases hm : (a.workTapes i).2 <;> simp [recordStepRows, f, g, a] at hm ⊢ <;> rw [hm]
  let final : Cfg 4 (RecSym Q T) (ScanPhase Bool) (x.map (RecSym.digitEmb Q T)) :=
    ⟨some (.done result.1), d.inputPos, patch result.2, d.workTapePos, d.output⟩
  have end2 : (recordStepRows M upd seek ⟨.shiftTape i, data⟩).runFrom middle (2 * old.length + 2) = final := by
    rw [row2, ← wlen, e2]
    apply Cfg.ext <;> try rfl
    funext j z
    dsimp only [final, middle, patch]
    rw [wlen]
    split_ifs <;> rfl
  have p2 := recordStep_phase_run M upd seek start finish ⟨.shiftTape i, data⟩
    (by intro b h; cases h) middle final (2 * old.length + 2) end2 (.done result.1) rfl
    (⟨⟨.skipNewTape i, data⟩, .run⟩ : RecordStepControl k Q T S) rfl
    (by intro u hu q hq; cases q with
        | done v =>
          rw [row2] at hq
          exact (c2 u (by simpa only [wlen] using hu) v hq).elim
        | fwd v => rfl
        | bwd v => rfl)
    d.workTapePos (2 * s + 2) (by
      rw [row2]
      exact bounded _ middle _ rfl (by simpa only [wlen] using h2))
  have total := Segment.trans p1 p2
  have time : (2 * old.length + 2 + 1) + (2 * old.length + 2 + 1) = 4 * (2 * s + 1) + 6 := by omega
  rw [time] at total
  simpa [first, middle, final, patch, recordStep_mapState_mk, word, a, len] using total


/-- Copy the changed position digits from B into F1, then erase B globally.
The record and scratch heads, native position and output are restored before the F1 skip.
**Proof sketch.** The public framed copy changes only the destination interval. Its
source buffer survives, so the shared B-clear specialization applies immediately.
Compose both existing-host phases, including their dispatches and common width radius. -/
private theorem recordStep_copyback_run {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List (RecSym Q T)}
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) x)
    (w : List (RecSym Q T)) (data : RecordStepData k Q T) :
    let changed := {d with workTapes := fun j z =>
      if j = 0 ∧ d.workTapePos j ≤ z ∧ z < d.workTapePos j + (w.length : ℤ)
        then FinTM.bufferTape w (z - d.workTapePos j) else d.workTapes j z}
    RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (w.length + 1)
      (recordStepSnapshot d (⟨⟨.copyBack, data⟩, .sweep⟩ : RecordStepControl k Q T S) 0 w [])
      (recordStepSnapshot changed (⟨⟨.skipNewPos, data⟩, .run⟩ : RecordStepControl k Q T S) 0 [] [])
      (4 * w.length + 6) := by
  dsimp only
  let changed := {d with workTapes := fun j z =>
    if j = 0 ∧ d.workTapePos j ≤ z ∧ z < d.workTapePos j + (w.length : ℤ)
      then FinTM.bufferTape w (z - d.workTapePos j) else d.workTapes j z}
  let a := recordStepSnapshot d SweepPhase.sweep 0 w []
  obtain ⟨ec, cc, hc⟩ := recordStep_contract_clauses (copyTM_contract 1 0 (by decide) _) w a rfl
    (by rw [copyTM_contract_pre]; intro z _ _; simp [a, recordStepSnapshot])
  rw [copyTM_contract_time, copyTM_contract_post, recordStep_sweepPost_eq] at ec
  simp only [copyTM_contract_time, copyTM_contract_lo, copyTM_contract_hi] at cc hc
  have apos : a.workTapePos = d.workTapePos := by funext j; simp [a, recordStepSnapshot]
  have pc := recordStep_phase_run M upd seek start finish ⟨.copyBack, data⟩
    (by intro b h; cases h) a (recordStepSnapshot changed .done 0 w []) (2 * w.length + 2)
    (by
      refine ec.trans ?_
      apply Cfg.ext <;> try rfl
      funext j z
      fin_cases j <;> simp [a, changed, recordStepSnapshot]) .done rfl
    (⟨⟨.clearB, data⟩, .sweep⟩ : RecordStepControl k Q T S) rfl
    (by intro u hu q hq; cases q with
        | done => exact (cc u hu hq).elim
        | sweep => rfl
        | rewind => rfl)
    d.workTapePos (w.length + 1) (by
      intro u hu j
      have h := hc j u hu
      change |((copyTM 4 1 0).runFrom a u).workTapePos j - d.workTapePos j| ≤ _
      by_cases hj : j = 1 ∨ j = 0
      · rw [if_pos hj, if_pos hj] at h
        simp only [Finset.mem_Icc] at h
        rw [apos] at h
        rw [abs_le]; constructor <;> omega
      · rw [if_neg hj, if_neg hj] at h
        rw [Finset.mem_Icc] at h
        rw [le_antisymm h.2 h.1]
        simp [a, recordStepSnapshot]
        omega)
  obtain ⟨ee, ce, _⟩ := recordStep_clear_snapshot changed 0 w [] w 1
    (Or.inl rfl) (by simp) (by simp)
  have pe := recordStep_phase_run M upd seek start finish ⟨.clearB, data⟩
    (by intro b h; cases h) (recordStepSnapshot changed .sweep 0 w [])
    (recordStepSnapshot changed .done 0 [] []) (2 * w.length + 2) (by simpa using ee) .done rfl
    (⟨⟨.skipNewPos, data⟩, .run⟩ : RecordStepControl k Q T S) rfl
    (by intro u hu q hq; cases q with
        | done => exact (ce u hu hq).elim
        | sweep => rfl
        | rewind => rfl)
    d.workTapePos (w.length + 1) (recordStep_clear_heads changed w [] w 1
      (Or.inl rfl) (by simp) (by simp))
  have total := Segment.trans pc pe
  have time : (2 * w.length + 2 + 1) + (2 * w.length + 2 + 1) = 4 * w.length + 6 := by omega
  rw [time] at total
  simpa [a, changed, recordStep_mapState_mk, recordStepSnapshot] using total


/-- The successful record rewrite returns from its tag to the record start and yes.
The k+2 inverse skips preserve the completed record and all native components.
**Proof sketch.** Induct on the last field still to cross. Each public inverse-skip
contract is framed by the completed record and its public field offsets. Intercept its
exit, then apply the induction hypothesis; the final skip dispatches directly to yes. -/
private theorem recordStep_write_back {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List (RecSym Q T)}
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) x)
    (fs : List (List (RecSym Q T))) (hlen : fs.length = k + 3)
    (hrec : RecordAt d 0 fs) (data : RecordStepData k Q T) :
    ∃ t ≤ 4 * (k + 2) * ((joinFields fs).length + 1),
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos ((joinFields fs).length + 1)
        (recordStepSnapshot d
          (⟨⟨.writeBack ⟨k + 1, by omega⟩, data⟩, .run⟩ : RecordStepControl k Q T S)
          (fieldOffset fs (k + 2)) [] [])
        (recordStepSnapshot d (recordStepVerdict true : RecordStepControl k Q T S) 0 [] []) t := by
  let L := (joinFields fs).length
  let cfg {A : Type} (q : A) (r : ℕ) := recordStepSnapshot d q (fieldOffset fs r) [] []
  have returns (r : ℕ) (hr : r < k + 2) : ∃ t ≤ 4 * (r + 1) * (L + 1),
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
        (cfg (⟨⟨.writeBack ⟨r, hr⟩, data⟩, .run⟩ : RecordStepControl k Q T S) (r + 1))
        (cfg (recordStepVerdict true : RecordStepControl k Q T S) 0) t := by
    induction r using Nat.strong_induction_on with | h r ih =>
    have jr : r < fs.length := by omega
    have stepOffset := fieldOffset_succ fs r jr
    have startField : (cfg SeekPhase.run (r + 1)).workTapePos 0 - (fs[r].length : ℤ) - 1 =
        d.workTapePos 0 + (fieldOffset fs r : ℤ) := by
      simp [cfg, recordStepSnapshot, stepOffset]
      omega
    obtain ⟨run, cut, heads⟩ := recordStep_contract_clauses (skipBackTM_contract (0 : Fin 4) _)
      fs[r] (cfg SeekPhase.run (r + 1)) rfl (by
      rw [skipBackTM_contract_pre]
      intro z hz hu
      change d.workTapes 0 ((cfg SeekPhase.run (r + 1)).workTapePos 0 - (fs[r].length : ℤ) - 1 + z) = _
      rw [startField, add_assoc]
      have span := fieldOffset_add_length_le fs r jr
      rw [hrec _ (by omega) (by dsimp [L] at *; omega)]
      exact fieldsTape_field fs r jr z hz hu)
    rw [skipBackTM_contract_time, skipBackTM_contract_post, recordStep_seekPost_eq] at run
    simp only [skipBackTM_contract_time, skipBackTM_contract_lo, skipBackTM_contract_hi]
      at cut heads
    have reached : (skipBackTM 4 0).runFrom (cfg SeekPhase.run (r + 1)) (fs[r].length + 3) =
        cfg SeekPhase.done r := by
      rw [run]
      apply Cfg.ext <;> try rfl
      funext j
      by_cases hj : j = 0
      · subst j
        simpa [cfg, recordStepSnapshot] using startField
      · simp [cfg, recordStepSnapshot, hj, Function.update_of_ne]
    let next : RecordStepControl k Q T S := if h : 0 < r then
      ⟨⟨.writeBack ⟨r - 1, by omega⟩, data⟩, .run⟩ else recordStepVerdict true
    have segment := recordStep_phase_run M upd seek start finish ⟨.writeBack ⟨r, hr⟩, data⟩
      (by intro b h; cases h) (cfg SeekPhase.run (r + 1)) (cfg SeekPhase.done r)
      (fs[r].length + 3) reached .done rfl next (by dsimp [recordStepNext, next]; split_ifs <;> rfl)
      (by intro u hu q hq; cases q with
          | done => exact (cut u hu hq).elim
          | run => rfl
          | gap => rfl
          | back => rfl)
      d.workTapePos (L + 1) (by
        intro u hu j
        have h := heads j u hu
        by_cases hj : j = 0
        · subst j
          simp only [↓reduceIte, Finset.mem_Icc] at h
          have span := fieldOffset_add_length_le fs (r + 1) (by omega)
          dsimp [cfg, recordStepSnapshot] at h ⊢
          rw [abs_le]
          dsimp [L] at *
          constructor <;> omega
        · rw [if_neg hj] at h
          rw [Finset.mem_Icc] at h
          change |((skipBackTM 4 0).runFrom (cfg SeekPhase.run (r + 1)) u).workTapePos j - d.workTapePos j| ≤ _
          rw [le_antisymm h.2 h.1]
          simp [cfg, recordStepSnapshot, hj]
          omega)
    have cost : fs[r].length + 4 ≤ 4 * (L + 1) := by
      have span := fieldOffset_add_length_le fs r jr
      dsimp [L]
      omega
    cases r with
    | zero =>
      refine ⟨fs[0].length + 4, by simpa using cost, ?_⟩
      simpa [cfg, next, recordStep_mapState_mk, recordStepSnapshot] using segment
    | succ r =>
      obtain ⟨t, ht, done⟩ := ih r (by omega) (by omega)
      refine ⟨fs[r + 1].length + 4 + t, ?_, ?_⟩
      · calc
          _ ≤ 4 * (L + 1) + 4 * (r + 1) * (L + 1) := Nat.add_le_add cost ht
          _ = _ := by ring
      · have segment' : RecordSeg (recordStepMachine M upd seek start finish)
            (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
            (cfg (⟨⟨.writeBack ⟨r + 1, hr⟩, data⟩, .run⟩ : RecordStepControl k Q T S) (r + 2))
            (cfg (⟨⟨.writeBack ⟨r, by omega⟩, data⟩, .run⟩ : RecordStepControl k Q T S) (r + 1))
            (fs[r + 1].length + 4) := by
          simpa [cfg, next, recordStep_mapState_mk, recordStepSnapshot] using segment
        exact Segment.trans segment' done
  simpa [cfg, L, fieldOffset] using returns (k + 1) (by omega)


/-- The clamped F1 update uses the dedicated B tape, copies back only after arithmetic,
and clears B before returning to the record traversal.
**Proof sketch.** The inherited position-digit identity separates the two clamps and
stationary move from genuine carry/borrow. The shared arithmetic transport and copy-back
segment handle changed digits; the public clear handles unchanged digits. The original
field contract identifies the unchanged framed patch in the clamped cases. -/
private theorem recordStep_position_run {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List Bool}
    (c : Cfg k Bool Q x) (data : RecordStepData k Q T)
    (hinput : data.input = c.inputSymbol) (hzero : data.posZero = decide (c.inputPos.val = 0))
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map (RecSym.digitEmb Q T)))
    (hw : ∀ z : ℤ, -1 ≤ z → z ≤ (posWidth x.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + z) = FinTM.bufferTape
        ((binDigits (posWidth x.length) c.inputPos.val).map (RecSym.digitEmb Q T)) z) :
    let a := recordStepAction M data
    let w := binDigits (posWidth x.length) c.inputPos.val
    let v := binDigits (posWidth x.length) (a.apply c).inputPos.val
    let entry : RecordStepControl k Q T S := match a.inputTape with
      | .zero => ⟨⟨.clearB, data⟩, .sweep⟩
      | .neg => if data.posZero then ⟨⟨.clearB, data⟩, .sweep⟩ else ⟨⟨.decB, data⟩, .run⟩
      | .pos => if data.input.isNone && !data.posZero then ⟨⟨.clearB, data⟩, .sweep⟩
          else ⟨⟨.incB, data⟩, .run⟩
    let changed := {d with workTapes := fun j z =>
      if j = 0 ∧ d.workTapePos j ≤ z ∧ z < d.workTapePos j + (posWidth x.length : ℤ)
        then FinTM.bufferTape (v.map (RecSym.digitEmb Q T)) (z - d.workTapePos j) else d.workTapes j z}
    ∃ t ≤ 6 * posWidth x.length + 9,
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (posWidth x.length + 1)
        (recordStepSnapshot d entry 0 (w.map (RecSym.digitEmb Q T)) [])
        (recordStepSnapshot changed (⟨⟨.skipNewPos, data⟩, .run⟩ : RecordStepControl k Q T S) 0 [] []) t := by
  dsimp only
  let a := recordStepAction M data
  let W := posWidth x.length
  let e := RecSym.digitEmb Q T
  let w := binDigits W c.inputPos.val
  let v := binDigits W (a.apply c).inputPos.val
  let changed := {d with workTapes := fun j z =>
    if j = 0 ∧ d.workTapePos j ≤ z ∧ z < d.workTapePos j + (W : ℤ)
      then FinTM.bufferTape (v.map e) (z - d.workTapePos j) else d.workTapes j z}
  have wl : w.length = W := by simp [w, binDigits]
  have vl : v.length = W := by simp [v, binDigits]
  have clear (hv : v = w) :
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (W + 1)
        (recordStepSnapshot d (⟨⟨.clearB, data⟩, .sweep⟩ : RecordStepControl k Q T S) 0 (w.map e) [])
        (recordStepSnapshot changed (⟨⟨.skipNewPos, data⟩, .run⟩ : RecordStepControl k Q T S) 0 [] [])
        (2 * W + 3) := by
    have unchanged : changed = d := by
      apply Cfg.ext <;> try rfl
      funext j z
      dsimp only [changed]
      split_ifs with h
      · obtain ⟨rfl, hlo, hhi⟩ := h
        have hf := hw (z - d.workTapePos 0) (by omega) (by change _ ≤ (W : ℤ); omega)
        rw [hv]
        simpa only [add_sub_cancel] using hf.symm
      · rfl
    obtain ⟨run, cut, _⟩ := recordStep_clear_snapshot d 0 (w.map e) [] (w.map e) 1
      (Or.inl rfl) (by simp) (by simp)
    have phase := recordStep_phase_run M upd seek start finish ⟨.clearB, data⟩
      (by intro b h; cases h) (recordStepSnapshot d .sweep 0 (w.map e) [])
      (recordStepSnapshot d .done 0 [] []) (2 * (w.map e).length + 2)
      (by simpa using run) .done rfl
      (⟨⟨.skipNewPos, data⟩, .run⟩ : RecordStepControl k Q T S) rfl
      (by intro u hu q hq; cases q with
          | done => exact (cut u hu hq).elim
          | sweep => rfl
          | rewind => rfl)
      d.workTapePos ((w.map e).length + 1)
      (recordStep_clear_heads d (w.map e) [] (w.map e) 1 (Or.inl rfl) (by simp) (by simp))
    simpa [unchanged, recordStep_mapState_mk, recordStepSnapshot, wl] using phase
  have arithmetic (increase : Bool) (hv : (if increase then incFixed w else decFixed w) = some v) :
      ∃ t ≤ 6 * W + 9,
        RecordSeg (recordStepMachine M upd seek start finish)
          (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (W + 1)
          (recordStepSnapshot d (if increase then
            (⟨⟨.incB, data⟩, .run⟩ : RecordStepControl k Q T S) else ⟨⟨.decB, data⟩, .run⟩) 0 (w.map e) [])
          (recordStepSnapshot changed (⟨⟨.skipNewPos, data⟩, .run⟩ : RecordStepControl k Q T S) 0 [] []) t := by
    let raw := recordStepSnapshot d FlagPhase.run 0 (w.map e) []
    let last := recordStepSnapshot d (FlagPhase.done true) 0 (v.map e) []
    obtain ⟨t, ht, run, cut, heads⟩ := recordStep_arithmetic_transport increase 0 w v hv
      (by omega) raw rfl (by intro z; simp [raw, recordStepSnapshot, recordStepDigitBank, e])
    have endrun : (embedEmitTM (recordStepDigitBank 0)
        ((if increase then incrementTM 1 0 else decrementTM 1 0).liftSymbols e)).runFrom raw t = last := by
      refine run.trans ?_
      apply Cfg.ext <;> try rfl
      funext j z
      fin_cases j <;> simp [raw, last, recordStepSnapshot, recordStepDigitBank, e]
    have phase : RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (W + 1)
        (recordStepSnapshot d (if increase then
          (⟨⟨.incB, data⟩, .run⟩ : RecordStepControl k Q T S) else ⟨⟨.decB, data⟩, .run⟩) 0 (w.map e) [])
        (recordStepSnapshot d (⟨⟨.copyBack, data⟩, .sweep⟩ : RecordStepControl k Q T S) 0 (v.map e) []) (t + 1) := by
      have radius : ∀ u ≤ t, ∀ j,
          |((embedEmitTM (recordStepDigitBank 0)
            ((if increase then incrementTM 1 0 else decrementTM 1 0).liftSymbols e)).runFrom raw u).workTapePos j -
            d.workTapePos j| ≤ ((W + 1 : ℕ) : ℤ) := by
        intro u hu j
        simpa [raw, recordStepSnapshot, wl] using heads u hu j
      cases increase
      · have h := recordStep_phase_run M upd seek start finish ⟨.decB, data⟩
          (by intro b h; cases h) raw last t endrun (.done true) rfl
          (⟨⟨.copyBack, data⟩, .sweep⟩ : RecordStepControl k Q T S) rfl
          (by intro u hu q hq; cases q with
              | done v => exact (cut u hu v hq).elim
              | run => rfl
              | rewind v => rfl)
          d.workTapePos (W + 1) radius
        simpa [raw, last, recordStep_mapState_mk, recordStepSnapshot] using h
      · have h := recordStep_phase_run M upd seek start finish ⟨.incB, data⟩
          (by intro b h; cases h) raw last t endrun (.done true) rfl
          (⟨⟨.copyBack, data⟩, .sweep⟩ : RecordStepControl k Q T S) rfl
          (by intro u hu q hq; cases q with
              | done v => exact (cut u hu v hq).elim
              | run => rfl
              | rewind v => rfl)
          d.workTapePos (W + 1) radius
        simpa [raw, last, recordStep_mapState_mk, recordStepSnapshot] using h
    have copied := recordStep_copyback_run M upd seek start finish d (v.map e) data
    have copied' : RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (W + 1)
        (recordStepSnapshot d (⟨⟨.copyBack, data⟩, .sweep⟩ : RecordStepControl k Q T S) 0 (v.map e) [])
        (recordStepSnapshot changed (⟨⟨.skipNewPos, data⟩, .run⟩ : RecordStepControl k Q T S) 0 [] []) (4 * W + 6) := by
      simpa [changed, vl] using copied
    refine ⟨t + 1 + (4 * W + 6), ?_, Segment.trans phase copied'⟩
    rw [wl] at ht
    omega
  have digits := recordStep_position_digits c a.inputTape
  change (match a.inputTape with
    | .zero => some w
    | .neg => if c.inputPos.val = 0 then some w else decFixed w
    | .pos => if c.inputSymbol.isNone && !(decide (c.inputPos.val = 0)) then some w else incFixed w) = some v at digits
  cases hm : a.inputTape with
  | zero =>
    simp only [hm] at digits
    refine ⟨2 * W + 3, by omega, ?_⟩
    simpa only [show (recordStepAction M data).inputTape = .zero from hm] using clear (Option.some.inj digits).symm
  | neg =>
    by_cases hz : c.inputPos.val = 0
    · simp only [hm, hz, ↓reduceIte] at digits
      refine ⟨2 * W + 3, by omega, ?_⟩
      simpa [a, W, e, w, v, changed, hm, hzero, hz] using clear (Option.some.inj digits).symm
    · simp only [hm, if_neg hz] at digits
      simpa [a, W, e, w, v, changed, hm, hzero, hz] using arithmetic false digits
  | pos =>
    by_cases hr : (c.inputSymbol.isNone && !(decide (c.inputPos.val = 0))) = true
    · simp only [hm, if_pos hr] at digits
      refine ⟨2 * W + 3, by omega, ?_⟩
      simpa only [a, W, e, w, v, changed, hm, hinput, hzero, hr, ↓reduceIte] using clear (Option.some.inj digits).symm
    · simp only [hm, if_neg hr] at digits
      simpa only [a, W, e, w, v, changed, hm, hinput, hzero, hr, ↓reduceIte] using arithmetic true digits

/-- The successful apply phases rewrite every fixed-width field and return to yes.
**Proof sketch.** Maintain a prefix already equal to the final record, with the untouched
suffix still equal to the original record. Public field offsets and framed contracts
advance this prefix through state, clamped position, work-tape fields and tag. All field
widths agree. Finally the proved inverse skips restore the record head and return yes. -/
private theorem recordStep_apply_run {k : ℕ} {Q T S : Type}
    [DecidableEq Q] [DecidableEq T] [DecidableEq S]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (seek : MultiTapeTM 2 Bool S) (start finish : S) {x : List Bool}
    (s : ℕ) (c : Cfg k Bool Q x) (τ : T) (hc : c.InWindow s)
    (data : RecordStepData k Q T) (hinput : data.input = c.inputSymbol)
    (hzero : data.posZero = decide (c.inputPos.val = 0)) (htag : data.tag = some τ)
    (d : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map (RecSym.digitEmb Q T)))
    (hrec : RecordAt d 0 (cfgRecord s c τ))
    (blank : ∀ j : Fin 4, j ≠ 0 → ∀ z, d.workTapes j z = none) :
    ∃ t ≤ 40 * (k + 3) * ((joinFields (cfgRecord s c τ)).length + 1),
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos
        ((joinFields (cfgRecord s c τ)).length + 1)
        (recordStepSnapshot d (⟨⟨.writeState, data⟩, .fwd ()⟩ : RecordStepControl k Q T S) 0
          ((binDigits (posWidth x.length) c.inputPos.val).map (RecSym.digitEmb Q T)) [])
        {d with
          state := some (recordStepVerdict true)
          workTapes := fun j z =>
            if j = 0 ∧ d.workTapePos j ≤ z ∧ z < d.workTapePos j + ((joinFields (cfgRecord s c τ)).length : ℤ)
              then fieldsTape (cfgRecord s ((recordStepAction M data).apply c)
                (upd τ (recordStepAction M data).output)) (z - d.workTapePos j)
              else d.workTapes j z} t := by
  let a := recordStepAction M data
  let fs := cfgRecord s c τ
  let gs := cfgRecord s (a.apply c) (upd τ a.output)
  let L := (joinFields fs).length
  let w := (binDigits (posWidth x.length) c.inputPos.val).map (RecSym.digitEmb Q T)
  let cfg {A : Type} (q : A) (head cut : ℕ) (b : List (RecSym Q T)) :=
    recordStepSnapshot {d with
      workTapes := fun j z =>
        if j = 0 ∧ d.workTapePos j ≤ z ∧ z < d.workTapePos j + (cut : ℤ)
          then fieldsTape gs (z - d.workTapePos j) else d.workTapes j z} q (head : ℤ) b []
  have snap {A B : Type} (q : A) (q' : B) (head cut p : ℕ) (b : List (RecSym Q T)) :
      recordStepSnapshot (cfg q head cut []) q' (p : ℤ) b [] = cfg q' (head + p) cut b := by
    apply Cfg.ext <;> try rfl
    · funext j z
      fin_cases j <;> simp [cfg, recordStepSnapshot]
    · funext j
      fin_cases j <;> simp [cfg, recordStepSnapshot, Nat.cast_add, add_assoc]
  have snap0 {A B : Type} (q : A) (q' : B) (head cut : ℕ) (b : List (RecSym Q T)) :
      recordStepSnapshot (cfg q head cut []) q' 0 b [] = cfg q' head cut b := by
    simpa only [Nat.cast_zero, Nat.add_zero] using snap q q' head cut 0 b
  have flen : fs.length = k + 3 := cfgRecord_length s c τ
  have glen : gs.length = k + 3 := cfgRecord_length s (a.apply c) (upd τ a.output)
  have lengths : fs.map List.length = gs.map List.length := by
    simp [fs, gs, cfgRecord, binDigits, List.map_map, Function.comp_def]
  have sizes : fs.map (fun u => u.length + 1) = gs.map (fun u => u.length + 1) := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map (fun n => n + 1)) lengths
  have offsets (j : ℕ) : fieldOffset fs j = fieldOffset gs j := by
    simpa only [fieldOffset, List.map_take] using congrArg (fun ns : List ℕ => (ns.take j).sum) sizes
  have sameLength : (joinFields gs).length = L := by
    have hf := length_joinFields_add_one fs (by intro h; simp [h] at flen)
    have hg := length_joinFields_add_one gs (by intro h; simp [h] at glen)
    rw [flen] at hf
    rw [glen, ← offsets] at hg
    dsimp [L]
    omega
  have len (j : ℕ) (hj : j < k + 3) : (gs[j]'(by omega)).length = (fs[j]'(by omega)).length := by
    have h := congrArg (fun ns : List ℕ => ns[j]?) lengths
    simpa [List.getElem?_eq_getElem (by omega : j < fs.length),
      List.getElem?_eq_getElem (by omega : j < gs.length)] using h.symm
  have oldField (j : ℕ) (hj : j < k + 3) (z : ℤ) (hz : -1 ≤ z) (hu : z ≤ (fs[j]'(by omega)).length) :
      d.workTapes 0 (d.workTapePos 0 + fieldOffset fs j + z) = FinTM.bufferTape fs[j] z := by
    have span := fieldOffset_add_length_le fs j (by omega)
    rw [add_assoc, hrec _ (by omega) (by dsimp [fs] at *; omega)]
    exact fieldsTape_field fs j (by omega) z hz hu
  have newField (j : ℕ) (hj : j < k + 3) (z : ℤ) (hz : -1 ≤ z) (hu : z ≤ (fs[j]'(by omega)).length) :
      fieldsTape gs ((fieldOffset fs j : ℤ) + z) = FinTM.bufferTape (gs[j]'(by omega)) z := by
    rw [offsets]
    exact fieldsTape_field gs j (by omega) z hz (by simpa only [len j hj] using hu)
  have field {A : Type} (q : A) (j : ℕ) (hj : j < k + 3) (b : List (RecSym Q T))
      (z : ℤ) (hz : -1 ≤ z) (hu : z ≤ (fs[j]'(by omega)).length) :
      (cfg q (fieldOffset fs j) (fieldOffset fs j) b).workTapes 0
        ((cfg q (fieldOffset fs j) (fieldOffset fs j) b).workTapePos 0 + z) = FinTM.bufferTape fs[j] z := by
    change (if 0 = (0 : Fin 4) ∧ d.workTapePos 0 ≤ d.workTapePos 0 + (fieldOffset fs j : ℤ) + z ∧
        d.workTapePos 0 + (fieldOffset fs j : ℤ) + z < d.workTapePos 0 + (fieldOffset fs j : ℤ)
      then fieldsTape gs (d.workTapePos 0 + (fieldOffset fs j : ℤ) + z - d.workTapePos 0)
      else d.workTapes 0 (d.workTapePos 0 + (fieldOffset fs j : ℤ) + z)) = _
    split_ifs with h
    · have hz' : z = -1 := by omega
      have arg : d.workTapePos 0 + (fieldOffset fs j : ℤ) + z - d.workTapePos 0 =
          (fieldOffset fs j : ℤ) + z := by omega
      rw [arg, newField j hj z hz hu, hz']
      simp
    · exact oldField j hj z hz hu
  have extend {A : Type} (q : A) (j : ℕ) (hj : j < k + 3) (b : List (RecSym Q T)) :
      {cfg q (fieldOffset fs j) (fieldOffset fs j) b with
        workTapes := fun i z =>
          if i = 0 ∧ (cfg q (fieldOffset fs j) (fieldOffset fs j) b).workTapePos i ≤ z ∧
              z < (cfg q (fieldOffset fs j) (fieldOffset fs j) b).workTapePos i + (fs[j].length : ℤ)
            then FinTM.bufferTape (gs[j]'(by omega))
              (z - (cfg q (fieldOffset fs j) (fieldOffset fs j) b).workTapePos i)
            else (cfg q (fieldOffset fs j) (fieldOffset fs j) b).workTapes i z} =
        cfg q (fieldOffset fs j) (fieldOffset fs (j + 1)) b := by
    apply Cfg.ext <;> try rfl
    funext i z
    by_cases hi : i = 0
    · subst i
      have off := fieldOffset_succ fs j (by omega)
      have new (hz : (fieldOffset fs j : ℤ) ≤ z - d.workTapePos 0)
          (hu : z - d.workTapePos 0 ≤ (fieldOffset fs j : ℤ) + fs[j].length) :
          fieldsTape gs (z - d.workTapePos 0) =
            FinTM.bufferTape (gs[j]'(by omega)) (z - (d.workTapePos 0 + (fieldOffset fs j : ℤ))) := by
        have arg : z - d.workTapePos 0 = (fieldOffset fs j : ℤ) +
            (z - (d.workTapePos 0 + (fieldOffset fs j : ℤ))) := by omega
        conv_lhs => rw [arg]
        exact newField j hj _ (by omega) (by omega)
      dsimp only [cfg, recordStepSnapshot]
      simp only [show (0 : Fin 4) ≠ 1 by decide, show (0 : Fin 4) ≠ 3 by decide,
        ↓reduceIte, true_and]
      split_ifs with hwrite hold hnew hnew
      · exact (new (by omega) (by omega)).symm
      · omega
      · rfl
      · omega
      · have hz : z = d.workTapePos 0 + (fieldOffset fs j : ℤ) + fs[j].length := by omega
        have hf := oldField j hj (fs[j].length : ℤ) (by omega) le_rfl
        rw [← hz] at hf
        rw [new (by omega) (by omega)]
        have arg : z - (d.workTapePos 0 + (fieldOffset fs j : ℤ)) = fs[j].length := by omega
        rw [arg, ← len j hj]
        simpa [FinTM.bufferTape] using hf
      · rfl
    · simp [cfg, recordStepSnapshot, hi]
  have processed {A : Type} (q : A) (j : ℕ) (hj : j < k + 3) (b : List (RecSym Q T))
      (z : ℤ) (hz : -1 ≤ z) (hu : z ≤ (fs[j]'(by omega)).length) :
      (cfg q (fieldOffset fs j) (fieldOffset fs (j + 1)) b).workTapes 0
        ((cfg q (fieldOffset fs j) (fieldOffset fs (j + 1)) b).workTapePos 0 + z) =
          FinTM.bufferTape (gs[j]'(by omega)) z := by
    have off := fieldOffset_succ fs j (by omega)
    change (if 0 = (0 : Fin 4) ∧ d.workTapePos 0 ≤ d.workTapePos 0 + (fieldOffset fs j : ℤ) + z ∧
        d.workTapePos 0 + (fieldOffset fs j : ℤ) + z < d.workTapePos 0 + (fieldOffset fs (j + 1) : ℤ)
      then fieldsTape gs (d.workTapePos 0 + (fieldOffset fs j : ℤ) + z - d.workTapePos 0)
      else d.workTapes 0 (d.workTapePos 0 + (fieldOffset fs j : ℤ) + z)) = _
    have arg : d.workTapePos 0 + (fieldOffset fs j : ℤ) + z - d.workTapePos 0 =
        (fieldOffset fs j : ℤ) + z := by omega
    split_ifs with h
    · rw [arg]
      exact newField j hj z hz hu
    · have hz' : z = -1 := by rw [off] at h; omega
      rw [oldField j hj z hz hu, hz']
      simp
  have shift {A : Type} (q : A) (head cut : ℕ) (b : List (RecSym Q T))
      {u v : Cfg 4 (RecSym Q T) (RecordStepControl k Q T S) (x.map (RecSym.digitEmb Q T))}
      {t r : ℕ} (h : RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false)
        (cfg q head cut b).workTapePos r u v t) (bound : head + r ≤ L + 1) :
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1) u v t := by
    apply Segment.mono h (fun _ hx => hx)
    intro p hp
    rw [record_headBox_iff] at hp ⊢
    intro i
    have h' := hp i
    have delta : |(cfg q head cut b).workTapePos i - d.workTapePos i| ≤ (head : ℤ) := by
      simp only [cfg, recordStepSnapshot, add_sub_cancel_left]
      split_ifs <;> simp
    rw [abs_le] at h' delta ⊢
    constructor <;> omega
  have mapRaw (j : ℕ) (hj : j < k + 3) (b : List (RecSym Q T))
      (f : RecSym Q T → RecSym Q T) (word : (fs[j]'(by omega)).map f = gs[j]'(by omega)) :
      let raw := cfg (ScanPhase.fwd ()) (fieldOffset fs j) (fieldOffset fs j) b
      let row := scanTM 4 0 (scanMap f) scanKeep ()
      row.runFrom raw (2 * fs[j].length + 2) = cfg (ScanPhase.done ()) (fieldOffset fs j) (fieldOffset fs (j + 1)) b ∧
      (∀ u < 2 * fs[j].length + 2, ∀ v, (row.runFrom raw u).state ≠ some (.done v)) ∧
      (∀ u ≤ 2 * fs[j].length + 2, ∀ i, |(row.runFrom raw u).workTapePos i - d.workTapePos i| ≤ ((L + 1 : ℕ) : ℤ)) := by
    dsimp only
    obtain ⟨run, cut, heads⟩ := recordStep_contract_clauses_range
      (scanTM_contract (0 : Fin 4) (scanMap f) scanKeep () _) fs[j]
      (cfg (ScanPhase.fwd ()) (fieldOffset fs j) (fieldOffset fs j) b) rfl
      (by rw [scanTM_contract_pre]; exact field _ j hj b)
    rw [scanTM_contract_time, scanTM_contract_post] at run
    simp only [scanTM_contract_time, scanTM_contract_lo, scanTM_contract_hi] at cut heads
    rw [scanResult_map, word] at run
    refine ⟨run.trans (extend (ScanPhase.done ()) j hj b), cut, ?_⟩
    intro u hu i
    have h := heads i u hu
    by_cases hi : i = 0
    · subst i
      simp only [↓reduceIte, Finset.mem_Icc] at h
      have span := fieldOffset_add_length_le fs j (by omega)
      dsimp [cfg, recordStepSnapshot] at h ⊢
      rw [abs_le]
      dsimp [L] at *
      constructor <;> omega
    · rw [if_neg hi, if_neg hi] at h
      rw [Finset.mem_Icc] at h
      rw [le_antisymm h.2 h.1]
      simp [cfg, recordStepSnapshot, hi]
      omega
  have skipRaw (j : ℕ) (hj : j < k + 2) (b : List (RecSym Q T)) :
      let raw := cfg SeekPhase.run (fieldOffset fs j) (fieldOffset fs (j + 1)) b
      (skipTM 4 0).runFrom raw (fs[j]'(by omega)).length.succ =
        cfg SeekPhase.done (fieldOffset fs (j + 1)) (fieldOffset fs (j + 1)) b ∧
      (∀ u < fs[j].length + 1, ((skipTM 4 0).runFrom raw u).state ≠ some .done) ∧
      (∀ u ≤ fs[j].length + 1, ∀ i, |((skipTM 4 0).runFrom raw u).workTapePos i - d.workTapePos i| ≤ ((L + 1 : ℕ) : ℤ)) := by
    dsimp only
    obtain ⟨run, cut, heads⟩ := recordStep_contract_clauses (skipTM_contract (0 : Fin 4) _)
      (gs[j]'(by omega))
      (cfg SeekPhase.run (fieldOffset fs j) (fieldOffset fs (j + 1)) b) rfl
      (by
        rw [skipTM_contract_pre]
        intro z hz hu
        exact processed _ j (by omega) b z (by omega) (by simpa only [len j (by omega)] using hu))
    rw [skipTM_contract_time, skipTM_contract_post, recordStep_seekPost_eq] at run
    simp only [skipTM_contract_time, skipTM_contract_lo, skipTM_contract_hi] at cut heads
    rw [len j (by omega)] at run cut heads
    refine ⟨run.trans ?_, cut, ?_⟩
    · apply Cfg.ext <;> try rfl
      funext i
      by_cases hi : i = 0
      · subst i
        simp [cfg, recordStepSnapshot, fieldOffset_succ fs j (by omega)]
        omega
      · simp [cfg, recordStepSnapshot, hi, Function.update_of_ne]
    · intro u hu i
      have h := heads i u hu
      by_cases hi : i = 0
      · subst i
        simp only [↓reduceIte, Finset.mem_Icc] at h
        have span := fieldOffset_add_length_le fs j (by omega)
        dsimp [cfg, recordStepSnapshot] at h ⊢
        rw [abs_le]
        dsimp [L] at *
        constructor <;> omega
      · rw [if_neg hi] at h
        rw [Finset.mem_Icc] at h
        rw [le_antisymm h.2 h.1]
        simp [cfg, recordStepSnapshot, hi]
        omega
  let posEntry : RecordStepControl k Q T S := match a.inputTape with
    | .zero => ⟨⟨.clearB, data⟩, .sweep⟩
    | .neg => if data.posZero then ⟨⟨.clearB, data⟩, .sweep⟩ else ⟨⟨.decB, data⟩, .run⟩
    | .pos => if data.input.isNone && !data.posZero then ⟨⟨.clearB, data⟩, .sweep⟩ else ⟨⟨.incB, data⟩, .run⟩
  have stateRun : RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
      (cfg (⟨⟨.writeState, data⟩, .fwd ()⟩ : RecordStepControl k Q T S) 0 0 w)
      (cfg posEntry (fieldOffset fs 1) (fieldOffset fs 1) w) 8 := by
    have first : fs[0]'(by omega) = [RecSym.st c.state] := by rfl
    have last : gs[0]'(by omega) = [RecSym.st a.state] := by rfl
    obtain ⟨run, cut, heads⟩ := mapRaw 0 (by omega) w (fun _ => .st a.state) (by rw [first, last]; rfl)
    simp only [first, List.length_cons, List.length_nil] at run cut heads
    have pm := recordStep_phase_run M upd seek start finish ⟨.writeState, data⟩
      (by intro b h; cases h) (cfg (.fwd ()) 0 0 w) (cfg (.done ()) 0 (fieldOffset fs 1) w)
      4 run (.done ()) rfl (⟨⟨.skipNewState, data⟩, .run⟩ : RecordStepControl k Q T S) rfl
      (by intro u hu q hq; cases q with
          | done v => exact (cut u hu v hq).elim
          | fwd v => rfl
          | bwd v => rfl)
      d.workTapePos (L + 1) heads
    obtain ⟨run, cut, heads⟩ := skipRaw 0 (by omega) w
    simp only [first, List.length_cons, List.length_nil] at run cut heads
    have ps := recordStep_phase_run M upd seek start finish ⟨.skipNewState, data⟩
      (by intro b h; cases h) (cfg .run 0 (fieldOffset fs 1) w)
      (cfg .done (fieldOffset fs 1) (fieldOffset fs 1) w) 2 run .done rfl posEntry (by
        cases h : (recordStepAction M data).inputTape <;> simp [recordStepNext, posEntry, a, h] <;> split_ifs <;> rfl)
      (by intro u hu q hq; cases q with
          | done => exact (cut u hu hq).elim
          | run => rfl
          | gap => rfl
          | back => rfl)
      d.workTapePos (L + 1) heads
    exact Segment.trans pm ps
  let tapeState (r : ℕ) : RecordStepControl k Q T S := if h : r < k then
    ⟨⟨.writeTape ⟨r, h⟩, data⟩, .fwd ()⟩ else ⟨⟨.writeTag, data⟩, .fwd ()⟩
  have positionRun : ∃ t ≤ 8 * (L + 1),
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
        (cfg posEntry (fieldOffset fs 1) (fieldOffset fs 1) w)
        (cfg (tapeState 0) (fieldOffset fs 2) (fieldOffset fs 2) []) t := by
    let base := cfg posEntry (fieldOffset fs 1) (fieldOffset fs 1) []
    have word : fs[1]'(by omega) = w := by rfl
    have wide : w.length = posWidth x.length := by simp [w, binDigits]
    have last : gs[1]'(by omega) =
        (binDigits (posWidth x.length) (a.apply c).inputPos.val).map (RecSym.digitEmb Q T) := by rfl
    obtain ⟨t, ht, hrun⟩ := recordStep_position_run M upd seek start finish c data hinput hzero base
      (by
        intro z hz hu
        change base.workTapes 0 (base.workTapePos 0 + z) = FinTM.bufferTape w z
        simpa only [base, word] using field posEntry 1 (by omega) [] z hz (by simpa only [word, wide] using hu))
    have endeq : (recordStepSnapshot {base with
        workTapes := fun j z =>
          if j = 0 ∧ base.workTapePos j ≤ z ∧ z < base.workTapePos j + (posWidth x.length : ℤ)
            then FinTM.bufferTape (gs[1]'(by omega)) (z - base.workTapePos j) else base.workTapes j z}
        (⟨⟨.skipNewPos, data⟩, .run⟩ : RecordStepControl k Q T S) 0 [] []) =
          cfg (⟨⟨.skipNewPos, data⟩, .run⟩ : RecordStepControl k Q T S) (fieldOffset fs 1) (fieldOffset fs 2) [] := by
      have h := congrArg (fun base => recordStepSnapshot base
        (⟨⟨.skipNewPos, data⟩, .run⟩ : RecordStepControl k Q T S) 0 [] []) (extend posEntry 1 (by omega) [])
      simpa only [word, wide, snap0, Nat.add_zero] using h
    have segment : RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) base.workTapePos (posWidth x.length + 1)
        (cfg posEntry (fieldOffset fs 1) (fieldOffset fs 1) w)
        (cfg (⟨⟨.skipNewPos, data⟩, .run⟩ : RecordStepControl k Q T S) (fieldOffset fs 1) (fieldOffset fs 2) []) t := by
      change RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) base.workTapePos (posWidth x.length + 1)
        (recordStepSnapshot base posEntry 0 w [])
        (recordStepSnapshot {base with
          workTapes := fun j z =>
            if j = 0 ∧ base.workTapePos j ≤ z ∧ z < base.workTapePos j + (posWidth x.length : ℤ)
              then FinTM.bufferTape (gs[1]'(by omega)) (z - base.workTapePos j) else base.workTapes j z}
          (⟨⟨.skipNewPos, data⟩, .run⟩ : RecordStepControl k Q T S) 0 [] []) t at hrun
      rw [endeq] at hrun
      simpa only [base, snap0, Nat.add_zero] using hrun
    have span := fieldOffset_add_length_le fs 1 (by omega)
    have hwide : fieldOffset fs 1 + (posWidth x.length + 1) ≤ L + 1 := by
      rw [word, wide] at span
      dsimp [L]
      omega
    have pm := shift posEntry (fieldOffset fs 1) (fieldOffset fs 1) [] segment hwide
    obtain ⟨run, cut, heads⟩ := skipRaw 1 (by omega) []
    have ps := recordStep_phase_run M upd seek start finish ⟨.skipNewPos, data⟩
      (by intro b h; cases h) (cfg .run (fieldOffset fs 1) (fieldOffset fs 2) [])
      (cfg .done (fieldOffset fs 2) (fieldOffset fs 2) []) (fs[1].length + 1) run .done rfl
      (tapeState 0) (by simp [recordStepNext, recordStepFirstTape, tapeState])
      (by intro u hu q hq; cases q with
          | done => exact (cut u hu hq).elim
          | run => rfl
          | gap => rfl
          | back => rfl)
      d.workTapePos (L + 1) heads
    refine ⟨t + (fs[1].length + 2), ?_, Segment.trans pm ps⟩
    have off1 : fieldOffset fs 1 = 2 := by rfl
    rw [word, wide, off1] at span
    rw [word, wide]
    dsimp [L] at *
    omega
  have round (r : ℕ) (hr : r < k) :
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
        (cfg (tapeState r) (fieldOffset fs (r + 2)) (fieldOffset fs (r + 2)) [])
        (cfg (tapeState (r + 1)) (fieldOffset fs (r + 3)) (fieldOffset fs (r + 3)) [])
        (5 * (2 * s + 1) + 8) := by
    let i : Fin k := ⟨r, hr⟩
    have word : fs[r + 2]'(by omega) = (List.range (2 * s + 1)).map fun (z : ℕ) =>
        RecSym.cell (c.workTapes i ((z : ℤ) - s)) (decide (c.workTapePos i = (z : ℤ) - s)) := by
      simp only [fs, cfgRecord, List.getElem_cons_succ, bind_pure_comp, Functor.map,
        List.map_map, Function.comp_def]
      rw [List.getElem_append_left (by simpa using hr)]
      simp [i]
    have last : gs[r + 2]'(by omega) = (List.range (2 * s + 1)).map fun (z : ℕ) =>
        RecSym.cell ((a.apply c).workTapes i ((z : ℤ) - s)) (decide ((a.apply c).workTapePos i = (z : ℤ) - s)) := by
      simp only [gs, cfgRecord, List.getElem_cons_succ, bind_pure_comp, Functor.map,
        List.map_map, Function.comp_def]
      rw [List.getElem_append_left (by simpa using hr)]
      simp [i]
    have wide : (fs[r + 2]'(by omega)).length = 2 * s + 1 := by simp [word]
    let base := cfg (tapeState r) (fieldOffset fs (r + 2)) (fieldOffset fs (r + 2)) []
    have tape := recordStep_tape_run M upd seek start finish s c hc data i base
      (by
        intro z hz hu
        have hf := field (tapeState r) (r + 2) (by omega) [] z hz (by simpa only [wide] using hu)
        simpa only [base, word] using hf)
    have patched := extend (⟨⟨.skipNewTape i, data⟩, .run⟩ : RecordStepControl k Q T S) (r + 2) (by omega) []
    have segment : RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) base.workTapePos (2 * s + 2)
        (cfg (tapeState r) (fieldOffset fs (r + 2)) (fieldOffset fs (r + 2)) [])
        (cfg (⟨⟨.skipNewTape i, data⟩, .run⟩ : RecordStepControl k Q T S)
          (fieldOffset fs (r + 2)) (fieldOffset fs (r + 3)) []) (4 * (2 * s + 1) + 6) := by
      rw [← patched]
      simpa [base, tapeState, hr, i, cfg, recordStepSnapshot, wide, last, a] using tape
    have span := fieldOffset_add_length_le fs (r + 2) (by omega)
    have pm := shift (tapeState r) (fieldOffset fs (r + 2)) (fieldOffset fs (r + 2)) [] segment
      (by rw [wide] at span; dsimp [L]; omega)
    obtain ⟨run, cut, heads⟩ := skipRaw (r + 2) (by omega) []
    have ps := recordStep_phase_run M upd seek start finish ⟨.skipNewTape i, data⟩
      (by intro b h; cases h) (cfg .run (fieldOffset fs (r + 2)) (fieldOffset fs (r + 3)) [])
      (cfg .done (fieldOffset fs (r + 3)) (fieldOffset fs (r + 3)) []) (fs[r + 2].length + 1) run .done rfl
      (tapeState (r + 1)) (by dsimp [recordStepNext, tapeState, i]; split_ifs <;> rfl)
      (by intro u hu q hq; cases q with
          | done => exact (cut u hu hq).elim
          | run => rfl
          | gap => rfl
          | back => rfl)
      d.workTapePos (L + 1) heads
    have joined := Segment.trans pm ps
    convert joined using 1
    omega
  have tapes : ∀ r ≤ k, ∃ t ≤ 8 * r * (L + 1),
      RecordSeg (recordStepMachine M upd seek start finish)
        (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
        (cfg (tapeState 0) (fieldOffset fs 2) (fieldOffset fs 2) [])
        (cfg (tapeState r) (fieldOffset fs (r + 2)) (fieldOffset fs (r + 2)) []) t := by
    intro r hr
    induction r with
    | zero =>
      refine ⟨0, by omega, Segment.zero ((record_headBox_iff _ _ _).mpr ?_)⟩
      intro j
      have span := fieldOffset_add_length_le fs 2 (by omega)
      simp only [cfg, recordStepSnapshot]
      split_ifs <;> rw [abs_le] <;> dsimp [L] at * <;> constructor <;> omega
    | succ r ih =>
      obtain ⟨t, ht, hrun⟩ := ih (by omega)
      have span := fieldOffset_add_length_le fs (r + 2) (by omega)
      have size : (fs[r + 2]'(by omega)).length = 2 * s + 1 := by
        simp [fs, cfgRecord, List.getElem_append_left, show r < k by omega]
      have cost : 5 * (2 * s + 1) + 8 ≤ 8 * (L + 1) := by rw [size] at span; dsimp [L]; omega
      refine ⟨t + (5 * (2 * s + 1) + 8), ?_, Segment.trans hrun (round r (by omega))⟩
      calc
        _ ≤ 8 * r * (L + 1) + 8 * (L + 1) := Nat.add_le_add ht cost
        _ = _ := by ring
  have tag : RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
      (cfg (tapeState k) (fieldOffset fs (k + 2)) (fieldOffset fs (k + 2)) [])
      (cfg (⟨⟨.writeBack ⟨k + 1, by omega⟩, data⟩, .run⟩ : RecordStepControl k Q T S)
        (fieldOffset fs (k + 2)) (fieldOffset fs (k + 3)) []) 5 := by
    have first : fs[k + 2]'(by omega) = [RecSym.tag τ] := by simp [fs, cfgRecord]
    have last : gs[k + 2]'(by omega) = [RecSym.tag (upd τ a.output)] := by simp [gs, cfgRecord]
    let f : RecSym Q T → RecSym Q T := fun γ => match data.tag with
      | some v => RecSym.tag (upd v a.output) | none => γ
    obtain ⟨run, cut, heads⟩ := mapRaw (k + 2) (by omega) [] f (by simp [first, last, f, htag])
    simp only [first, List.length_cons, List.length_nil] at run cut heads
    have phase := recordStep_phase_run M upd seek start finish ⟨.writeTag, data⟩
      (by intro b h; cases h) (cfg (.fwd ()) (fieldOffset fs (k + 2)) (fieldOffset fs (k + 2)) [])
      (cfg (.done ()) (fieldOffset fs (k + 2)) (fieldOffset fs (k + 3)) []) 4 run (.done ()) rfl
      (⟨⟨.writeBack ⟨k + 1, by omega⟩, data⟩, .run⟩ : RecordStepControl k Q T S) rfl
      (by intro u hu q hq; cases q with
          | done v => exact (cut u hu v hq).elim
          | fwd v => rfl
          | bwd v => rfl)
      d.workTapePos (L + 1) heads
    simpa only [tapeState, lt_self_iff_false, ↓reduceDIte] using phase
  let final := cfg (recordStepVerdict true : RecordStepControl k Q T S) 0 (fieldOffset fs (k + 3)) []
  have fullcut : fieldOffset fs (k + 3) = L + 1 := by
    have h := length_joinFields_add_one fs (by intro h; simp [h] at flen)
    simpa only [flen, L] using h.symm
  have record : RecordAt final 0 gs := by
    intro z hz hu
    have head : final.workTapePos 0 = d.workTapePos 0 := by simp [final, cfg, recordStepSnapshot]
    rw [head]
    change (if 0 = (0 : Fin 4) ∧ d.workTapePos 0 ≤ d.workTapePos 0 + z ∧
        d.workTapePos 0 + z < d.workTapePos 0 + (fieldOffset fs (k + 3) : ℤ)
      then fieldsTape gs (d.workTapePos 0 + z - d.workTapePos 0)
      else d.workTapes 0 (d.workTapePos 0 + z)) = _
    rw [add_sub_cancel_left, fullcut]
    split_ifs with h
    · rfl
    · have hz' : z = -1 := by rw [sameLength] at hu; omega
      subst z
      have f := oldField 0 (by omega) (-1) le_rfl (by omega)
      have g := newField 0 (by omega) (-1) le_rfl (by omega)
      simpa only [fieldOffset, List.take_zero, List.map_nil, List.sum_nil, Nat.cast_zero, zero_add, add_zero] using f.trans g.symm
  obtain ⟨tw, htw, back⟩ := recordStep_write_back M upd seek start finish final gs glen record data
  have back' : RecordSeg (recordStepMachine M upd seek start finish)
      (recordStepVerdict true) (recordStepVerdict false) d.workTapePos (L + 1)
      (cfg (⟨⟨.writeBack ⟨k + 1, by omega⟩, data⟩, .run⟩ : RecordStepControl k Q T S)
        (fieldOffset fs (k + 2)) (fieldOffset fs (k + 3)) []) final tw := by
    have head : final.workTapePos = d.workTapePos := by
      funext j
      simp [final, cfg, recordStepSnapshot]
    rw [head] at back
    simpa only [final, snap0, snap, Nat.zero_add, ← offsets, sameLength] using back
  obtain ⟨tp, htp, pos⟩ := positionRun
  obtain ⟨tt, htt, tape⟩ := tapes k le_rfl
  have total := Segment.trans
    (Segment.trans (Segment.trans (Segment.trans stateRun pos) tape) tag) back'
  refine ⟨8 + tp + tt + 5 + tw, ?_, ?_⟩
  · rw [sameLength] at htw
    change _ ≤ 40 * (k + 3) * (L + 1)
    nlinarith
  · have initial : cfg (⟨⟨.writeState, data⟩, .fwd ()⟩ : RecordStepControl k Q T S) 0 0 w =
        recordStepSnapshot d (⟨⟨.writeState, data⟩, .fwd ()⟩ : RecordStepControl k Q T S) 0 w [] := by
      apply Cfg.ext <;> try rfl
      funext j z
      have no : ¬(j = 0 ∧ d.workTapePos j ≤ z ∧ z < d.workTapePos j) := by omega
      simp [cfg, recordStepSnapshot, no]
    have endpoint : final = {d with
        state := some (recordStepVerdict true)
        workTapes := fun j z =>
          if j = 0 ∧ d.workTapePos j ≤ z ∧ z < d.workTapePos j + (L : ℤ)
            then fieldsTape gs (z - d.workTapePos j) else d.workTapes j z} := by
      apply Cfg.ext <;> try rfl
      · funext j z
        by_cases hj : j = 0
        · subst j
          simp only [final, cfg, recordStepSnapshot, fullcut, show (0 : Fin 4) ≠ 1 by decide,
            show (0 : Fin 4) ≠ 3 by decide, ↓reduceIte, true_and]
          split_ifs with h h' h'
          · rfl
          · have hz : z = d.workTapePos 0 + (L : ℤ) := by omega
            subst z
            rw [add_sub_cancel_left]
            have old := hrec (L : ℤ) (by omega) (by rfl)
            change d.workTapes 0 (d.workTapePos 0 + (L : ℤ)) = fieldsTape fs (L : ℤ) at old
            calc
              fieldsTape gs (L : ℤ) = none := by rw [← sameLength]; simp [fieldsTape]
              _ = d.workTapes 0 (d.workTapePos 0 + (L : ℤ)) := by simpa [L, fieldsTape] using old.symm
          · omega
          · rfl
        · simp [final, cfg, recordStepSnapshot, hj, blank j hj]
      · funext j
        simp [final, cfg, recordStepSnapshot]
    rw [initial, endpoint] at total
    exact total



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
segments, including the seek/restore, scratch cleanup and final time/radius ledger.

**Fill-C continuation 2 sketch appendix (partial).** The full R1--R6 read now has a
`RecordRun` ending at the source observations and both canonical digit copies. The target's
halted branch is complete, including both clears, the unchanged record, first verdict and
common bounds. Shared snapshot specializations support clear and map rows; rich R1 seek
and Save transports preserve every frame cell and output prefix. Fuel/probe/Save (I1--I3)
and seek/Read (I4--I5) are each composed in the existing host with their full cuts and
head bounds. Empty-input cleanup and rejection cleanup are also proved segments.
The remaining live-source admission still needs their concatenation with complement,
normal-branch decrement, restore and cleanup (I6--I9), the A0--A5 rewrite, and its final
endpoint and time/radius ledger. No private helper is admitted.

**Fill-C continuation 3 sketch appendix (complete).** The native cycle now composes
I0--I9, including complement, normal-branch borrow, restoration and D cleanup, with
exact native position and output restoration. The observed action and edge test identify
both source-step branches. Rejection clears B before any record write. Success maintains
the processed prefix of the final record while the untouched suffix retains the source
record, using the public field layout and framed rows. The clamped position uses the same
R1 arithmetic transport as restoration; two scans per work field write and shift its mark.
The tag map and inverse skips complete the update with all scratch globally blank and all
heads restored. `RecordRun` composes the full cuts and radii; the unchanged coefficient
`200 * (k + 3) * (Cseek + 1)` covers the time and head-radius ledgers. -/
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
    let w := (binDigits (posWidth x.length) c.inputPos.val).map (RecSym.digit (Q := Q) (T := T))
    let data := {recordStepReadData (T := T) s c k with tag := some τ}
    let L := (joinFields (cfgRecord s c τ)).length
    obtain ⟨tr, htr, hread⟩ := recordStep_read_all M upd seek start finish s c τ hc d hd hrec hblank
    have span := fieldOffset_add_length_le (cfgRecord s c τ) 1 (by simp [cfgRecord_length])
    have hwidth : w.length ≤ L := by
      change 2 + w.length ≤ L at span
      omega
    by_cases halted : c.state = none
    · have hhalt := recordStep_halt_run M upd seek start finish d w data halted
      have cleanup : RecordSeg R yes no d.workTapePos (L + 1)
          (recordStepSnapshot d (recordStepReadExit data) 0 w w)
          (recordStepSnapshot d yes 0 [] []) (4 * w.length + 6) :=
        Segment.mono hhalt (fun _ hx => hx) (record_headBox_mono (by omega))
      have total := Segment.trans hread cleanup
      have total := (recordSeg_iff (R := R) (yes := yes) (no := no)
        (base := d.workTapePos) (radius := L + 1)).mp total
      have hcoef : 10 * (k + 3) + 23 ≤ 200 * (k + 3) * (Cseek + 1) :=
        le_trans (by omega : 10 * (k + 3) + 23 ≤ 200 * (k + 3))
          (Nat.le_mul_of_pos_right _ (by omega))
      refine ⟨tr + (4 * w.length + 6), ?_, total.2.1, ?_, ?_, ?_⟩
      · change tr + (4 * w.length + 6) ≤ 200 * (k + 3) * (Cseek + 1) * (L + x.length + 1)
        have htime : tr + (4 * w.length + 6) ≤ (10 * (k + 3) + 23) * (L + 1) := by
          dsimp only [L] at hwidth ⊢
          nlinarith
        exact le_trans htime (Nat.mul_le_mul hcoef (by omega))
      · intro u hu j
        have h := total.2.2 u hu j
        have hbig : L + 1 ≤ 200 * (k + 3) * (Cseek + 1) * (L + 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        exact le_trans h (by exact_mod_cast hbig)
      · intro _
        rw [total.1, recordStepSnapshot_empty d yes hblank]
        rw [MultiTapeTM.step_of_halt halted, MultiTapeTM.outputSymbol_of_halt halted, hupd]
        apply Cfg.ext <;> try rfl
        funext j z
        dsimp only
        split
        next h =>
          obtain ⟨rfl, hlo, hhi⟩ := h
          simpa using hrec (z - d.workTapePos 0) (by omega) (by omega)
        next => rfl
      · intro hout
        exact (hout (by simpa only [MultiTapeTM.step_of_halt halted] using hc)).elim
    · obtain ⟨b, tn, htn, hn⟩ := recordStep_live_native M upd seek start finish Cseek hseek c d data
        halted rfl (hblank 2 (by decide))
      let observed := {data with nativeRight := b, input := c.inputSymbol}
      have native : RecordSeg R yes no d.workTapePos ((Cseek + 1) * (L + 1))
          (recordStepSnapshot d (recordStepReadExit data) 0 w w)
          (recordStepSnapshot d (recordStepApply M observed) 0 w []) tn := by
        apply Segment.mono hn (fun _ hx => hx) (record_headBox_mono ?_)
        apply Nat.mul_le_mul_left
        have hw : w.length = posWidth x.length := by simp [w, binDigits]
        omega
      have read' := Segment.mono hread (fun _ hx => hx)
        (record_headBox_mono (Nat.le_mul_of_pos_left (L + 1) (by omega : 0 < Cseek + 1)))
      have ready := Segment.trans read' native
      have facts := recordStep_observed_action M s c τ b hc halted
      by_cases hin : (M.step c).InWindow s
      · have inside : recordStepOutside M observed = false := facts.2.2.mpr hin
        obtain ⟨ta, hta, applied⟩ := recordStep_apply_run M upd seek start finish s c τ hc observed
          rfl rfl rfl d hrec hblank
        have ready' : RecordSeg R yes no d.workTapePos ((Cseek + 1) * (L + 1)) d
            (recordStepSnapshot d (⟨⟨.writeState, observed⟩, .fwd ()⟩ : P) 0 w []) (tr + tn) := by
          simpa [recordStepApply, inside] using ready
        have applied' := Segment.mono applied (fun _ hx => hx)
          (record_headBox_mono (Nat.le_mul_of_pos_left (L + 1) (by omega : 0 < Cseek + 1)))
        have total := Segment.trans ready' applied'
        have total := (recordSeg_iff (R := R) (yes := yes) (no := no)
          (base := d.workTapePos) (radius := (Cseek + 1) * (L + 1))).mp total
        refine ⟨tr + tn + ta, ?_, total.2.1, ?_, ?_, ?_⟩
        · have hw : posWidth x.length ≤ L := by simpa [w, binDigits] using hwidth
          have ht1 : tr ≤ (10 * (k + 3) + 17) * (L + x.length + 1) :=
            le_trans htr (Nat.mul_le_mul_left _ (by omega))
          have ht2 : tn ≤ 20 * (Cseek + 1) * (L + x.length + 1) :=
            le_trans htn (Nat.mul_le_mul_left _ (by omega))
          have ht3 : ta ≤ 40 * (k + 3) * (L + x.length + 1) :=
            le_trans hta (Nat.mul_le_mul_left _ (by omega))
          have coeff : (10 * (k + 3) + 17) + 20 * (Cseek + 1) + 40 * (k + 3) ≤
              200 * (k + 3) * (Cseek + 1) := by nlinarith
          change tr + tn + ta ≤ 200 * (k + 3) * (Cseek + 1) * (L + x.length + 1)
          exact le_trans (by nlinarith : tr + tn + ta ≤
            ((10 * (k + 3) + 17) + 20 * (Cseek + 1) + 40 * (k + 3)) * (L + x.length + 1))
            (Nat.mul_le_mul_right _ coeff)
        · intro u hu j
          apply le_trans (total.2.2 u hu j)
          have coeff : Cseek + 1 ≤ 200 * (k + 3) * (Cseek + 1) :=
            Nat.le_mul_of_pos_left _ (by omega)
          exact_mod_cast Nat.mul_le_mul_right (L + 1) coeff
        · intro _
          have step : (recordStepAction M observed).apply c = M.step c := facts.1
          have output : (recordStepAction M observed).output = M.outputSymbol c := facts.2.1
          simpa only [step, output] using total.1
        · exact fun hout => (hout hin).elim
      · have outside : recordStepOutside M observed = true := by
          cases h : recordStepOutside M observed with
          | false => exact (hin (facts.2.2.mp h)).elim
          | true => rfl
        have reject := recordStep_reject_run M upd seek start finish d w observed outside
        have reject' := Segment.mono reject (fun _ hx => hx) (record_headBox_mono (by
          exact le_trans (by omega : w.length + 1 ≤ L + 1)
            (Nat.le_mul_of_pos_left _ (by omega : 0 < Cseek + 1))))
        have total := Segment.trans ready reject'
        have total := (recordSeg_iff (R := R) (yes := yes) (no := no)
          (base := d.workTapePos) (radius := (Cseek + 1) * (L + 1))).mp total
        refine ⟨(tr + tn) + (2 * w.length + 3), ?_, total.2.1, ?_, ?_, ?_⟩
        · have hw : posWidth x.length ≤ L := by simpa [w, binDigits] using hwidth
          have ht1 : tr ≤ (10 * (k + 3) + 17) * (L + x.length + 1) :=
            le_trans htr (Nat.mul_le_mul_left _ (by omega))
          have ht2 : tn ≤ 20 * (Cseek + 1) * (L + x.length + 1) :=
            le_trans htn (Nat.mul_le_mul_left _ (by omega))
          have ht3 : 2 * w.length + 3 ≤ 3 * (L + x.length + 1) := by omega
          have coeff : (10 * (k + 3) + 17) + 20 * (Cseek + 1) + 3 ≤
              200 * (k + 3) * (Cseek + 1) := by nlinarith
          change tr + tn + (2 * w.length + 3) ≤ 200 * (k + 3) * (Cseek + 1) * (L + x.length + 1)
          exact le_trans (by nlinarith : tr + tn + (2 * w.length + 3) ≤
            ((10 * (k + 3) + 17) + 20 * (Cseek + 1) + 3) * (L + x.length + 1))
            (Nat.mul_le_mul_right _ coeff)
        · intro u hu j
          apply le_trans (total.2.2 u hu j)
          have coeff : Cseek + 1 ≤ 200 * (k + 3) * (Cseek + 1) :=
            Nat.le_mul_of_pos_left _ (by omega)
          exact_mod_cast Nat.mul_le_mul_right (L + 1) coeff
        · exact fun h => (hin h).elim
        · intro _
          rw [total.1, recordStepSnapshot_empty d no hblank]


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
      RecordSeg R yes no d.workTapePos (L + 1)
        (cfg (⟨.forward j i, .run⟩ : S) p)
        (cfg (if i = 0 then (⟨.forward j 1, .run⟩ : S)
          else ⟨.compare ⟨j.val + 1, by omega⟩, .run⟩)
          (Function.update p i (j.val + 1))) (fs[j.val].length + 2) := by
    obtain ⟨hr, hc, hh⟩ := recordStep_contract_clauses (skipTM_contract i _) fs[j.val]
      (cfg SeekPhase.run p) rfl
      (by
        rw [skipTM_contract_pre]
        intro z hl hu
        simpa only [cfg, hpi] using hword i j.val (by omega) he z (by omega) hu)
    rw [skipTM_contract_time, skipTM_contract_post, recordStep_seekPost_eq] at hr
    simp only [skipTM_contract_time, skipTM_contract_lo, skipTM_contract_hi] at hc hh
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
    apply recordStep_tagged_segment hphase.1 hphase.2 (by intro h; cases h) (by intro h; cases h) ?_
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
    · rw [if_neg hi, Finset.mem_Icc] at hs
      rw [le_antisymm hs.2 hs.1]
      exact hhead _ p hp r
  have hback (b : Bool) (j : Fin (k + 2))
      (he : fs.take (j.val + 1) = gs.take (j.val + 1))
      (i : Fin 2) (p : Fin 2 → ℕ) (hpi : p i = j.val + 1) (hp : ∀ r, p r < fs.length) :
      RecordSeg R yes no d.workTapePos (L + 1)
        (cfg (⟨.backward b j i, .run⟩ : S) p)
        (cfg (if i = 0 then (⟨.backward b j 1, .run⟩ : S)
          else recordEqBack b ⟨j.val, by omega⟩) (Function.update p i j.val))
        (fs[j.val].length + 4) := by
    have hoff := fieldOffset_succ fs j.val (by omega)
    obtain ⟨hr, hc, hh⟩ := recordStep_contract_clauses (skipBackTM_contract i _) fs[j.val]
      (cfg SeekPhase.run p) rfl
      (by
        rw [skipBackTM_contract_pre]
        intro z hl hu
        convert hword i j.val (by omega) he z hl hu using 1
        dsimp [cfg]
        congr 1
        rw [hpi, hoff]
        push_cast
        ring)
    rw [skipBackTM_contract_time, skipBackTM_contract_post, recordStep_seekPost_eq] at hr
    simp only [skipBackTM_contract_time, skipBackTM_contract_lo, skipBackTM_contract_hi] at hc hh
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
    apply recordStep_tagged_segment hphase.1 hphase.2 (by intro h; cases h) (by intro h; cases h) ?_
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
    · rw [if_neg hi, Finset.mem_Icc] at hs
      rw [le_antisymm hs.2 hs.1]
      exact hhead _ p hp r
  have hforward (j : Fin (k + 2)) (he : fs.take (j.val + 1) = gs.take (j.val + 1)) :
      RecordSeg R yes no d.workTapePos (L + 1)
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
    have h := Segment.trans h0 h1
    rw [hp] at h
    exact h
  have hrestore (b : Bool) : ∀ j (hj : j ≤ k + 2), fs.take j = gs.take j →
      ∃ t ≤ j * B, RecordSeg R yes no d.workTapePos (L + 1)
        (cfg (recordEqBack b ⟨j, by omega⟩) (fun _ => j))
        (cfg (⟨.verdict b, .run⟩ : S) (fun _ => 0)) t := by
    intro j
    induction j with
    | zero =>
      intro hj he
      exact ⟨0, by omega,
        Segment.zero ((record_headBox_iff _ _ _).mpr (hhead _ _ (by intro r; omega)))⟩
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
      have hb := Segment.trans h0 h1
      rw [hp] at hb
      have hb' : RecordSeg R yes no d.workTapePos (L + 1)
          (cfg (recordEqBack b ⟨j + 1, by omega⟩) (fun _ => j + 1))
          (cfg (recordEqBack b ⟨j, by omega⟩) (fun _ => j))
          ((fs[j].length + 4) + (fs[j].length + 4)) := by
        simpa only [recordEqBack, Nat.zero_lt_succ, dif_pos] using hb
      have hlen := fieldOffset_add_length_le fs j (by omega)
      refine ⟨((fs[j].length + 4) + (fs[j].length + 4)) + t, ?_, Segment.trans hb' hr⟩
      rw [Nat.succ_mul]
      dsimp [B, L] at *
      omega
  have hcompare (j : Fin (k + 3)) (he : fs.take j.val = gs.take j.val) :
      ∃ δ ≤ fs[j.val].length, RecordSeg R yes no d.workTapePos (L + 1)
        (cfg (⟨.compare j, .run⟩ : S) (fun _ => j.val))
        (cfg (if fs[j.val] = gs[j.val] then
          if h : j.val < k + 2 then (⟨.forward ⟨j.val, h⟩ 0, .run⟩ : S)
          else recordEqBack true j else recordEqBack false j) (fun _ => j.val))
        (2 * δ + 3) := by
    obtain ⟨hr, hc, hh⟩ := recordStep_contract_clauses_range
      (compareTM_contract 0 1 (by decide) _) (fs[j.val], gs[j.val])
      (cfg FlagPhase.run (fun _ => j.val)) rfl
      (by
        rw [compareTM_contract_pre]
        exact ⟨hword0 j.val (by omega), hword1 j.val (by omega) he⟩)
    rw [compareTM_contract_time, compareTM_contract_post] at hr
    simp only [compareTM_contract_time, compareTM_contract_lo, compareTM_contract_hi] at hc hh
    set δ := compareStop fs[j.val] gs[j.val] with hδdef
    have hδ : δ ≤ min fs[j.val].length gs[j.val].length := compareStop_le _ _
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
    apply recordStep_tagged_segment hphase.1 hphase.2 (by intro h; cases h) (by intro h; cases h) ?_
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
      ∃ t ≤ r * B + (k + 2) * B, RecordSeg R yes no d.workTapePos (L + 1)
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
            ?_, Segment.trans (Segment.trans hc hcross) hr⟩
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
          simpa only [if_pos heq, yes] using Segment.trans hc hr
      · simp only [if_neg hf] at hc
        have hne : fs ≠ gs := by intro h; subst gs; exact hf rfl
        obtain ⟨t, ht, hr⟩ := hrestore false j.val (by have := j.isLt; omega) he
        have ht' : t ≤ (k + 2) * B := le_trans ht (Nat.mul_le_mul_right B (by have := j.isLt; omega))
        have hb : B ≤ (r + 1) * B := Nat.le_mul_of_pos_left _ (by omega)
        refine ⟨(2 * δ + 3) + t, by omega, ?_⟩
        simpa only [if_neg hne, no] using Segment.trans hc hr
  obtain ⟨t, ht, hall⟩ := hsolve (k + 3) ⟨0, by omega⟩ (by simp) rfl
  have hstart : cfg entry (fun _ => 0) = d := by
    apply Cfg.ext
    · exact hd.symm
    · rfl
    · rfl
    · funext i; simp [cfg, fieldOffset]
    · rfl
  change RecordSeg R yes no d.workTapePos (L + 1) (cfg entry (fun _ => 0)) _ t at hall
  rw [hstart, recordSeg_iff] at hall
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
    obtain ⟨hr, hc, hh⟩ := recordStep_contract_clauses_range
      (scanTM_contract (0 : Fin 1) (scanFold δ) scanKeep a _) fs[j]
      (cfg (ScanPhase.fwd a) j) rfl (by rw [scanTM_contract_pre]; exact hword j hj)
    rw [scanTM_contract_time, scanTM_contract_post] at hr
    simp only [scanTM_contract_time, scanTM_contract_lo, scanTM_contract_hi] at hc hh
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
      RecordSeg R yes no d.workTapePos (L + 1)
        (cfg (fstate q j (by omega)) j) (cfg (fstate q (j + 1) (by omega)) (j + 1))
        (fs[j].length + 2) := by
    have hjf : j < fs.length := by omega
    have hnext : j + 1 < fs.length := by omega
    obtain ⟨hr, hc, hh⟩ := recordStep_contract_clauses (skipTM_contract (0 : Fin 1) _) fs[j]
      (cfg SeekPhase.run j) rfl
      (by rw [skipTM_contract_pre]; exact fun p hl hu => hword j hjf p (by omega) hu)
    rw [skipTM_contract_time, skipTM_contract_post, recordStep_seekPost_eq] at hr
    simp only [skipTM_contract_time, skipTM_contract_lo, skipTM_contract_hi] at hc hh
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
    apply recordStep_tagged_segment hp.1 hp.2 (by intro h; cases h) (by intro h; cases h) ?_
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
      RecordSeg R yes no d.workTapePos (L + 1)
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
    obtain ⟨hr, hc, hh⟩ := recordStep_contract_clauses (skipBackTM_contract (0 : Fin 1) _)
      fs[j] (cfg SeekPhase.run (j + 1)) rfl (by rw [skipBackTM_contract_pre]; exact hw)
    rw [skipBackTM_contract_time, skipBackTM_contract_post, recordStep_seekPost_eq] at hr
    simp only [skipBackTM_contract_time, skipBackTM_contract_lo, skipBackTM_contract_hi] at hc hh
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
    apply recordStep_tagged_segment hp.1 hp.2 (by intro h; cases h) (by intro h; cases h) ?_
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
      ∃ t ≤ j * B, RecordSeg R yes no d.workTapePos (L + 1)
        (cfg (fstate q 0 (by omega)) 0) (cfg (fstate q j hj) j) t := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨0, by omega, Segment.zero ((record_headBox_iff _ _ _).mpr (hhead _ 0 (by omega)))⟩
    | succ j ih =>
      intro hj
      obtain ⟨t, ht, hr⟩ := ih (by omega)
      have hb := fieldOffset_add_length_le fs j (by omega)
      refine ⟨t + (fs[j].length + 2), ?_, Segment.trans hr (hskip q j (by omega))⟩
      dsimp [B, L] at *
      rw [Nat.succ_mul]
      omega
  have hbackward (b : Bool) : ∀ j (hj : j ≤ k + 2),
      ∃ t ≤ j * B, RecordSeg R yes no d.workTapePos (L + 1)
        (cfg (bstate b j hj) j) (cfg (⟨.verdict b, .run⟩ : S) 0) t := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨0, by omega, Segment.zero ((record_headBox_iff _ _ _).mpr (hhead _ 0 (by omega)))⟩
    | succ j ih =>
      intro hj
      obtain ⟨t, ht, hr⟩ := ih (by omega)
      have hb := fieldOffset_add_length_le fs j (by omega)
      refine ⟨(fs[j].length + 4) + t, ?_, Segment.trans (hbackstep b j (by omega)) hr⟩
      dsimp [B, L] at *
      rw [Nat.succ_mul]
      omega
  have hsword : fs[0] = [RecSym.st c.state] := rfl
  have htword : fs[k + 2] = [RecSym.tag τ] := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem (by omega)]
    simp [fs, cfgRecord]
  have hstate : RecordSeg R yes no d.workTapePos (L + 1)
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
    exact recordStep_tagged_segment hp.1 hp.2 (by intro h; cases h) (by intro h; cases h)
      hh (hhead _ 0 (by omega))
  have htag : RecordSeg R yes no d.workTapePos (L + 1)
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
      (recordStep_tagged_segment hp.1 hp.2 (by intro h; cases h) (by intro h; cases h)
        hh (hhead _ (k + 2) (by omega)))
  obtain ⟨tf, htf, hf⟩ := hforward c.state (k + 2) le_rfl
  obtain ⟨tb, htb, hb⟩ := hbackward (P c.state τ) (k + 2) le_rfl
  have hall := Segment.trans (Segment.trans (Segment.trans hstate hf) htag) hb
  have hstart : cfg entry 0 = d := by
    apply Cfg.ext
    · exact hd.symm
    · rfl
    · rfl
    · funext i; simp [cfg, fieldOffset]
    · rfl
  rw [hstart] at hall
  have hall := (recordSeg_iff (R := R) (yes := yes) (no := no)
    (base := d.workTapePos) (radius := L + 1)).mp hall
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

namespace Turing

/-! ### The initial configuration is windowed -/

/-- **The initial configuration is in every window**: its heads are at `0` and its work
tapes are blank. It is the windowed runner's precondition at the start of a simulation from
an initial configuration (H3; `Complexity.space_hierarchy`'s diagonalizer). [AB09, §4.1.1]

**Proof sketch.** Unfold `Turing.Cfg.init`. -/
theorem Cfg.inWindow_init {k : ℕ} {Symbol State : Type} (q₀ : State)
    (x : List Symbol) (s : ℕ) : (Cfg.init q₀ x : Cfg k Symbol State x).InWindow s :=
  ⟨fun _ => by simp, fun _ _ _ => rfl⟩

end Turing
