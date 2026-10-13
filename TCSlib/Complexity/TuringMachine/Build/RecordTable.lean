/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.CfgRecord
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.InputLength
import Mathlib.Data.Nat.Bitwise

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: record tables and the deferred record rows (§12.8b)

The table layer of the §12.8 rich-alphabet design and the record rows its
statement gate deferred (`machine-library-design.md` §12.8a §8 item 10, §9
decisions 2 and 5, §12.8b). A **table** is a header field followed by entries,
each entry a fixed number of fields, all in the blank-separated field layout of
`Turing.joinFields`, with two blank cells on each side. The breadth-first
simulation of `NSPACE` in exponential time keeps its visited set in one; the
rows here append to a table, find the first entry a finite-state fold accepts,
copy field lists between tapes, and return from a table's end to its start.
The record rows write the record template and the initial record from binary
radius digits, decide record validity against the template, and enumerate the
valid records, which Savitch's midpoint recursion consumes.

**Status (fill continuation 4): partial fill (15 of 20 targets proved).** The
layout facts, end-to-start adapter, field-list copy and record-template writer
are proved. Five existential rows remain sorried with their proof sketches.
Append also has a proved reverse copier and seek-and-copy prefix. The
already-landed `Turing.RecordValid.joinFields_length` is admission-free as well.

## Design

* **The table layout** (decision 2 of §12.8a §9). `Turing.tableFields h es`
  is the header `h` followed by the fields of the entries `es`, and
  `Turing.TableAt` places its layout at an origin with two blank cells before
  the header and two after the last field. The header is nonempty, so the
  field list is never empty, every seek precondition is uniform, and the
  empty table is a header alone. Entries are addressed by
  `Turing.tableOffset`, the cell their first field starts at.
* **The end-to-start adapter** (decision 2, round-1 notes 14 and 42) is a real
  machine, `Turing.tableRewindTM`: skip back over the last field, then seek
  the start. Its exact framed contract is the composition of the two Catalog
  rows by one seam.
* **Find takes fuel.** The number of entries is not on any tape, and the one
  rich loop host, `Turing.counterLoopTMVia`, runs a counter, so
  `Turing.exists_tableFindTM` takes a digit word whose value exceeds the
  number of entries and restores it. The breadth-first host keeps one such word.
* **Field-list copy** `Turing.exists_fieldsCopyTM` moves a fixed number of
  fields between tapes; append and the enumeration are built on it, and the
  hosts use it for workspaces, table entries and Savitch's frames.
* **Record rows are existential modules** in the house style: a machine,
  entry and verdict anchors with `yes ≠ no`, a first-return time bound, an
  exact finish configuration that restores every head, the input position and
  the scratch, and a work-space clause bounding every work head through the
  verdict to `C·(size + 1)` cells of its entry position (round-1 major 1).
  Tape layouts are fixed and local, hosted by R1 (decision 4).
* **The template** `Turing.recordTemplate n s` carries what a record row cannot
  read off a candidate: the bound `n + 1` at the position width, and the
  `2s + 1`-cell window of a blank tape with its head at `0`.
* **The enumeration order is existential.** `Turing.exists_recordNextTM`
  exports a duplicate-free list of exactly the valid records and a module that
  walks it; the order the fill realizes is the odometer order, but no consumer
  reads it.

## Main definitions

* `Turing.recordLength` — the layout length of every record at `(k, n, s)`.
* `Turing.recordTemplate` — the widths template of the validity and
  enumeration rows.
* `Turing.tableFields`, `Turing.tableOffset`, `Turing.TableWF`,
  `Turing.TableAt` — the table layout, entry offsets, well-formedness, and
  placement on a tape.
* `Turing.tableRewindTM` — the end-to-start adapter.

## Main results

* `Turing.joinFields_length`, `Turing.fieldOffset_length`,
  `Turing.joinFields_cfgRecord_length`, `Turing.cfgRecord_field_ne_nil`,
  `Turing.cfgRecord_init`, `Turing.RecordValid.joinFields_length`,
  `Turing.recordValid_iff_exists_cfg`,
  `Turing.joinFields_recordTemplate_length`, `Turing.binDigits_posWidth_succ`
  — layout and record facts (proved).
* `Turing.TableWF.field_ne_nil`, `Turing.tableOffset_eq`,
  `Turing.tableOffset_length`, `Turing.TableAt.recordAt_take` — table facts
  (proved).
* `Turing.tableRewindTM_run_ofCfg` — the adapter's framed contract
  (proved).
* `Turing.exists_fieldsCopyTM` — field-list copy (proved).
* `Turing.exists_tableFindTM`, `Turing.exists_tableAppendTM` — the remaining
  table rows (statements).
* `Turing.exists_recordTemplateTM` — the record-template writer
  (proved; fill continuation 4).
* `Turing.exists_recordInitTM`, `Turing.exists_recordValidTM`,
  `Turing.exists_recordNextTM` — the remaining record rows of R8.7 (statements).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1 and Claim 4.4: configurations
  described in `O(S(n))` bits; Theorem 4.2(iii), whose simulation searches the
  configuration graph keeping a table of visited configurations; Theorem 4.14
  (Savitch), whose recursion enumerates candidate midpoint configurations.)
-/

namespace Turing

/-! ### Layout lengths -/

/-- **The length of a field layout** (design §12.8b). A nonempty field list
lays out as its cells plus one separator between consecutive fields.

**Proof sketch.** Induct on the list: `List.intercalate` of a singleton is its
field, and each further field adds its length and one separator.

**Fill appendix.** Reuse the public layout induction in
`Turing.length_joinFields_add_one`; the remaining induction distributes the
sum of field lengths plus one. No second layout induction is introduced. -/
theorem joinFields_length {Γ : Type*} (fs : List (List Γ)) (hfs : fs ≠ []) :
    (joinFields fs).length = (fs.map List.length).sum + fs.length - 1 := by
  have h := length_joinFields_add_one fs hfs
  have hs : (fs.map (fun u => u.length + 1)).sum =
      (fs.map List.length).sum + fs.length := by
    clear h hfs
    induction fs with
    | nil => simp
    | cons u fs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
  simp only [fieldOffset, List.take_length] at h
  omega

/-- **The end offset of a field layout** (design §12.8b; the formula of
`Turing.fieldOffset`'s docstring, made a lemma). For a nonempty field list,
`fieldOffset fs |fs|` is the layout length plus one: the cell after the blank
that ends the layout, where `Turing.seekEndTM` stops and a further field would
start.

**Proof sketch.** `fieldOffset fs |fs|` sums `|f| + 1` over all fields, which is
`Turing.joinFields_length` plus one. -/
theorem fieldOffset_length {Γ : Type*} (fs : List (List Γ)) (hfs : fs ≠ []) :
    fieldOffset fs fs.length = (joinFields fs).length + 1 := by
  exact (length_joinFields_add_one fs hfs).symm

/-- **The record length** (design §12.8b): the layout length of every record
with `k` tapes, input length `n` and radius `s` — `k` tape fields of `2s + 1`
cells, `posWidth n` position digits, the state and tag cells, and `k + 2`
separators. -/
def recordLength (k n s : ℕ) : ℕ := k * (2 * s + 1) + posWidth n + k + 4

/-- **Every record has the record length** (design §12.8b). The layout of
`Turing.cfgRecord s c τ` has length `Turing.recordLength k |x| s`, whatever the
configuration and the tag. So the valid records at `(k, n, s)` all occupy the
same interval, and a row may rewrite one record into another in place.

**Proof sketch.** `Turing.joinFields_length` with the field lengths read off
`Turing.cfgRecord`: `1`, `posWidth |x|` (`binDigits` has its width), `2s + 1`
for each of the `k` tape fields, and `1`, over `k + 3` fields. -/
theorem joinFields_cfgRecord_length {k : ℕ} {Q T : Type} {x : List Bool} (s : ℕ)
    (c : Cfg k Bool Q x) (τ : T) :
    (joinFields (cfgRecord s c τ)).length = recordLength k x.length s := by
  rw [joinFields_length _ (by simp [cfgRecord]), cfgRecord_length]
  simp only [cfgRecord, Bind.bind, Pure.pure, ← List.map_eq_flatMap,
    binDigits, List.map_cons, List.map_append, List.map_map,
    Function.comp_def, List.length_map, List.length_range, List.map_const',
    List.length_finRange, List.sum_cons, List.sum_append, List.sum_replicate_nat,
    List.length_cons, List.length_nil, List.map_nil, List.sum_nil, recordLength]
  omega

/-- **Record fields are nonempty** (design §12.8b). No field of a record is
empty, so a table of records has no double blank inside it and the seek rows
apply.

**Proof sketch.** The state and tag fields have one cell, the tape fields
`2s + 1`, and the position field `posWidth |x| ≥ 1` cells, since
`Nat.bits (|x| + 1)` is nonempty. -/
theorem cfgRecord_field_ne_nil {k : ℕ} {Q T : Type} {x : List Bool} (s : ℕ)
    (c : Cfg k Bool Q x) (τ : T) : ∀ u ∈ cfgRecord s c τ, u ≠ [] := by
  have hwidth : 0 < posWidth x.length := by
    simpa only [posWidth, Nat.size_eq_bits_len] using
      (Nat.size_pos.mpr (Nat.succ_pos x.length))
  intro u hu
  simp only [cfgRecord, List.mem_cons, List.mem_append, List.mem_map,
    List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | ⟨i, hi, rfl⟩ | rfl
  · simp
  · intro h
    have := congrArg List.length h
    simp only [List.length_map, binDigits, List.length_range, List.length_nil] at this
    omega
  · intro h
    have := congrArg List.length h
    simp only [Bind.bind, Pure.pure, ← List.map_eq_flatMap,
      List.length_map, List.length_range, List.length_nil] at this
    omega
  · simp

/-- **The initial record** (design §12.8b). The record of the start
configuration `Cfg.init q₀ x` with tag `τ₀`: the state `some q₀`, the input
position `1` in `posWidth |x|` digits, `k` copies of the blank window with the
mark at its center (the head at cell `0`), and the tag. This is what
`Turing.exists_recordInitTM` writes.

**Proof sketch.** Unfold `Turing.cfgRecord` at `Cfg.init`: its work tapes are
blank, its heads at `0`, which is window index `s`, and its input position
is `1`. -/
theorem cfgRecord_init {k : ℕ} {Q T : Type} (x : List Bool) (s : ℕ) (q₀ : Q) (τ₀ : T) :
    cfgRecord s (Cfg.init q₀ x : Cfg k Bool Q x) τ₀ =
      [RecSym.st (some q₀)] :: ((binDigits (posWidth x.length) 1).map RecSym.digit) ::
        (List.replicate k ((List.range (2 * s + 1)).map fun j =>
            RecSym.cell none (decide (j = s))) ++
          [[RecSym.tag τ₀]]) := by
  have hmark (j : ℕ) : (0 : ℤ) = (j : ℤ) - s ↔ j = s := by omega
  simp only [cfgRecord, Cfg.init, Bind.bind, Pure.pure,
    ← List.map_eq_flatMap, List.map_map, Function.comp_def, hmark, List.map_const',
    List.length_finRange, Fin.val_one]

/-- **Valid records have the record length** (design §12.8b).

**Proof sketch.** A valid record is `Turing.cfgRecord s c τ` for a
configuration on an input of length `n`; apply
`Turing.joinFields_cfgRecord_length`. -/
theorem RecordValid.joinFields_length {k n s : ℕ} {Q T : Type}
    {fs : List (List (RecSym Q T))} (h : RecordValid k n s Q T fs) :
    (joinFields fs).length = recordLength k n s := by
  obtain ⟨x, c, τ, hx, -, rfl⟩ := h
  rw [joinFields_cfgRecord_length, hx]

/-- **Validity over a given input** (design §12.8b). A field list is a valid
record at input length `|x|` exactly when it is the record of a windowed
configuration on `x` itself. A record depends on its input only through the
input's length, so the windowed configurations of the actual input enumerate
every valid record; Savitch's midpoint enumeration rests on this.

**Proof sketch.** Backward: take the input `x`. Forward: a configuration on an
input `x'` with `|x'| = |x|` transports to `x` with the same state, work tapes,
heads and output and the input position cast along `|x'| = |x|`; its record and
window predicate are unchanged, since neither reads the input's symbols. -/
theorem recordValid_iff_exists_cfg {k : ℕ} {Q T : Type} (s : ℕ) (x : List Bool)
    (fs : List (List (RecSym Q T))) :
    RecordValid k x.length s Q T fs ↔
      ∃ (c : Cfg k Bool Q x) (τ : T), c.InWindow s ∧ cfgRecord s c τ = fs := by
  constructor
  · rintro ⟨y, c, τ, hy, hc, rfl⟩
    let d : Cfg k Bool Q x :=
      { state := c.state
        inputPos := ⟨c.inputPos.val, by simpa only [hy] using c.inputPos.isLt⟩
        workTapes := c.workTapes
        workTapePos := c.workTapePos
        output := c.output }
    refine ⟨d, τ, hc, ?_⟩
    simp only [cfgRecord, d, hy]
  · rintro ⟨c, τ, hc, hrec⟩
    exact ⟨x, c, τ, rfl, hc, hrec⟩

/-! ### The record template -/

/-- **The record template** (design §12.8b). Two fields over the record
alphabet: the bound `n + 1` in `posWidth n` digits, which also gives the
position width, and the window of a blank tape with its head at cell `0`:
`2s + 1` blank cells with the mark at the center. The validity and enumeration
rows read the widths and the position bound off it; its window field is the
tape field of the initial record (`Turing.cfgRecord_init`). -/
def recordTemplate (Q T : Type) (n s : ℕ) : List (List (RecSym Q T)) :=
  [(binDigits (posWidth n) (n + 1)).map RecSym.digit,
    (List.range (2 * s + 1)).map fun j => RecSym.cell none (decide (j = s))]

/-- **The template's length** (design §12.8b).

**Proof sketch.** Two fields of lengths `posWidth n` and `2s + 1`, and one
separator. -/
theorem joinFields_recordTemplate_length (Q T : Type) (n s : ℕ) :
    (joinFields (recordTemplate Q T n s)).length = posWidth n + 2 * s + 2 := by
  rw [joinFields_length _ (by simp [recordTemplate])]
  simp [recordTemplate, binDigits]
  omega

/-- **The template's bound field is `Nat.bits (n + 1)`** (design §12.8b). The
position width is the bit length of `n + 1`, so the fixed-width digits of
`n + 1` are its canonical binary word. A machine obtains the bound field from
`Turing.exists_inputLengthTM`'s `Nat.bits n` by one more increment.

**Proof sketch.** `binDigits w v` lists `v.testBit j` for `j < w`, and
`Nat.bits v` lists the same bits up to the bit length of `v`, which is
`posWidth n` at `v = n + 1`. -/
theorem binDigits_posWidth_succ (n : ℕ) :
    binDigits (posWidth n) (n + 1) = Nat.bits (n + 1) := by
  apply List.ext_getElem
  · simp [binDigits, posWidth]
  · intro j hj₁ hj₂
    simp only [binDigits, List.getElem_map, List.getElem_range]
    exact (Nat.testBit_eq_inth (n + 1) j).trans (List.getI_eq_getElem _ hj₂)

/-! ### Tables -/

/-- **The fields of a table** (design §12.8b, decision 2): the header `h`
followed by the fields of the entries `es` in order. -/
def tableFields {Γ : Type*} (h : List Γ) (es : List (List (List Γ))) : List (List Γ) :=
  h :: es.flatten

/-- **Entry offsets** (design §12.8b): the cell, relative to the table's origin,
at which entry `j` of the table starts. At `j = |es|` it is where a further
entry would start, two cells after the last field
(`Turing.tableOffset_length`). -/
def tableOffset {Γ : Type*} (h : List Γ) (es : List (List (List Γ))) (j : ℕ) : ℕ :=
  fieldOffset (tableFields h es) (1 + ((es.take j).map List.length).sum)

/-- **Well-formed tables** (design §12.8b): a nonempty header, and entries of
`m` fields each, every field nonempty. Under it two consecutive blanks occur
only at the table's ends, so the seek rows apply, and entries are found by
counting fields. -/
def TableWF {Γ : Type*} (m : ℕ) (h : List Γ) (es : List (List (List Γ))) : Prop :=
  h ≠ [] ∧ ∀ e ∈ es, e.length = m ∧ ∀ u ∈ e, u ≠ []

/-- **A table on a tape** (design §12.8b, decision 2): tape `r` holds the field
layout of the table with header `h` and entries `es` from the origin `o`, with
two blank cells before the header and two after the last field. The cells
beyond the sentinels are arbitrary; the head may be anywhere. -/
def TableAt {K : ℕ} {Γ S : Type*} {x : List Γ} (d : Cfg K Γ S x) (r : Fin K) (o : ℤ)
    (h : List Γ) (es : List (List (List Γ))) : Prop :=
  ∀ p : ℤ, -2 ≤ p → p ≤ ((joinFields (tableFields h es)).length : ℤ) + 1 →
    d.workTapes r (o + p) = fieldsTape (tableFields h es) p

/-- **Table fields are nonempty** (design §12.8b): the precondition of the seek
rows, from well-formedness.

**Proof sketch.** A field of the table is the header or a field of an entry. -/
theorem TableWF.field_ne_nil {Γ : Type*} {m : ℕ} {h : List Γ} {es : List (List (List Γ))}
    (hwf : TableWF m h es) : ∀ u ∈ tableFields h es, u ≠ [] := by
  intro u hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact hwf.1
  · obtain ⟨en, hen, hu⟩ := List.mem_flatten.mp hu
    exact (hwf.2 en hen).2 u hu

/-- **Entry offsets in closed form** (design §12.8b). When no entry is empty,
entry `j` starts after the header and its separator and, for each earlier
entry, its layout and one separator.

**Proof sketch.** Split `Turing.fieldOffset` over the header and the flattened
entries, and use `Turing.fieldOffset_length` on each earlier entry. -/
theorem tableOffset_eq {Γ : Type*} (h : List Γ) (es : List (List (List Γ)))
    (hes : ∀ e ∈ es, e ≠ []) (j : ℕ) :
    tableOffset h es j =
      h.length + 1 + ((es.take j).map fun e => (joinFields e).length + 1).sum := by
  unfold tableOffset tableFields
  rw [Nat.add_comm 1, fieldOffset_cons_succ]
  congr 1
  unfold fieldOffset
  rw [show (es.take j).map List.length = (es.map List.length).take j from List.map_take,
    List.take_sum_flatten, List.map_flatten, List.sum_flatten, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro en hen
  exact (by
    simpa only [fieldOffset, List.take_length] using
      fieldOffset_length en (hes en (List.mem_of_mem_take hen)))

/-- **The end of a table** (design §12.8b). The offset past the last entry is
the table's layout length plus one: the second trailing blank, where
`Turing.seekEndTM` stops from the origin.

**Proof sketch.** At `j = |es|` the field index is `|tableFields h es|`; apply
`Turing.fieldOffset_length`, the field list being nonempty. -/
theorem tableOffset_length {Γ : Type*} (h : List Γ) (es : List (List (List Γ))) :
    tableOffset h es es.length = (joinFields (tableFields h es)).length + 1 := by
  unfold tableOffset
  rw [List.take_length, ← List.length_flatten]
  simpa only [tableFields, List.length_cons, Nat.add_comm] using
    fieldOffset_length (tableFields h es) (List.cons_ne_nil _ _)

/-- Every cell of a nonempty layout, including its two delimiters, lies in a
field's framed interval.

**Proof sketch.** Choose the first field whose end is at or beyond the cell. The last
field supplies existence by the public end-offset formula. Minimality and the public
successor-offset formula give the lower bound. This uses no second layout induction. -/
private theorem rt_field_cover {Γ : Type*} (fs : List (List Γ)) (hne : fs ≠ [])
    (p : ℤ) (hp : -1 ≤ p) (hp' : p ≤ ((joinFields fs).length : ℤ)) :
    ∃ (j : ℕ) (hj : j < fs.length),
      -1 ≤ p - fieldOffset fs j ∧ p - fieldOffset fs j ≤ (fs[j].length : ℤ) := by
  have hlen : 0 < fs.length := List.length_pos_iff.mpr hne
  have hlast : fs.length - 1 < fs.length := by omega
  have hend := fieldOffset_succ fs (fs.length - 1) hlast
  rw [Nat.sub_add_cancel hlen, fieldOffset_length fs hne] at hend
  have hex : ∃ (j : ℕ) (hj : j < fs.length),
      p ≤ (fieldOffset fs j : ℤ) + (fs[j].length : ℤ) := by
    exact ⟨fs.length - 1, hlast, by omega⟩
  obtain ⟨hj, hu⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, hj, ?_, by omega⟩
  by_cases hz : Nat.find hex = 0
  · simpa only [hz, fieldOffset, List.take_zero, List.map_nil, List.sum_nil,
      Nat.cast_zero, sub_zero] using hp
  · have hprev : Nat.find hex - 1 < fs.length := by omega
    have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    have hnot : ¬p ≤ (fieldOffset fs (Nat.find hex - 1) : ℤ) +
        (fs[Nat.find hex - 1].length : ℤ) := fun h => hmin ⟨hprev, h⟩
    have hstep := fieldOffset_succ fs (Nat.find hex - 1) hprev
    rw [Nat.sub_add_cancel (show 1 ≤ Nat.find hex by omega)] at hstep
    omega

/-- A nonempty contiguous block of fields has the same framed cells inside a
larger layout, and its interval is contained in that layout.

**Proof sketch.** Splitting a list prefix adds field offsets. Locate each requested
cell in one field using `rt_field_cover`, and apply `fieldsTape_field` twice.
The last field and `fieldOffset_add_length_le` give containment. -/
private theorem rt_fields_slice {Γ : Type*} (pre gs post : List (List Γ))
    (hne : gs ≠ []) :
    fieldOffset (pre ++ (gs ++ post)) pre.length + (joinFields gs).length ≤
        (joinFields (pre ++ (gs ++ post))).length ∧
    ∀ p : ℤ, -1 ≤ p → p ≤ ((joinFields gs).length : ℤ) →
      fieldsTape (pre ++ (gs ++ post))
        ((fieldOffset (pre ++ (gs ++ post)) pre.length : ℤ) + p) = fieldsTape gs p := by
  let fs := pre ++ (gs ++ post)
  have hidx (j : ℕ) (hj : j < gs.length) : pre.length + j < fs.length := by
    simp only [fs, List.length_append]
    omega
  have hfield (j : ℕ) (hj : j < gs.length) :
      fs[pre.length + j]'(hidx j hj) = gs[j] := by
    simp [fs, List.getElem_append_right, List.getElem_append_left, hj]
  have hoff (j : ℕ) (hj : j ≤ gs.length) :
      fieldOffset fs (pre.length + j) = fieldOffset fs pre.length + fieldOffset gs j := by
    simp only [fs, fieldOffset, List.take_length_add_append,
      List.take_append_of_le_length hj, List.map_append, List.sum_append, List.take_left]
  have hlen : 0 < gs.length := List.length_pos_iff.mpr hne
  have hlast : gs.length - 1 < gs.length := by omega
  have hspan := fieldOffset_add_length_le fs (pre.length + (gs.length - 1))
    (hidx _ hlast)
  rw [hfield _ hlast, hoff _ (by omega)] at hspan
  have hend := fieldOffset_succ gs (gs.length - 1) hlast
  rw [Nat.sub_add_cancel hlen, fieldOffset_length gs hne] at hend
  refine ⟨show fieldOffset fs pre.length + (joinFields gs).length ≤
    (joinFields fs).length from by omega, ?_⟩
  intro p hp hp'
  obtain ⟨j, hj, hlo, hhi⟩ := rt_field_cover gs hne p hp hp'
  have hbig := fieldsTape_field fs (pre.length + j) (hidx j hj)
    (p - fieldOffset gs j) hlo (by simpa only [hfield j hj] using hhi)
  have hsmall := fieldsTape_field gs j hj (p - fieldOffset gs j) hlo hhi
  have ho := hoff j (by omega)
  have heq : (fieldOffset fs (pre.length + j) : ℤ) + (p - fieldOffset gs j) =
      (fieldOffset fs pre.length : ℤ) + p := by omega
  rw [heq, hfield j hj] at hbig
  rw [show (fieldOffset gs j : ℤ) + (p - fieldOffset gs j) = p by omega] at hsmall
  exact hbig.trans hsmall.symm

/-- **An entry of a table is a record at its offset** (design §12.8b). If a
well-formed table sits at `o` on tape `r` and the head is at entry `j`'s offset,
then the first `m₀ > 0` fields of entry `j` form a record at the head in the
sense of `Turing.RecordAt`. At `m₀ = m` this is the whole entry; at `m₀ = k + 3`
inside an entry of a record and a flag field, it is the record.

**Proof sketch.** `Turing.fieldsTape_field` on the table's field list, at the
field indices of entry `j`. The cell before the entry is the separator after
the header or after the previous entry, and the cell after the `m₀` fields is
the separator after field `m₀ - 1`, or the first trailing blank. -/
theorem TableAt.recordAt_take {K : ℕ} {Γ S : Type*} {x : List Γ} {d : Cfg K Γ S x}
    {r : Fin K} {o : ℤ} {m : ℕ} {h : List Γ} {es : List (List (List Γ))}
    (ht : TableAt d r o h es) (hwf : TableWF m h es) (j : ℕ) (hj : j < es.length)
    (hpos : d.workTapePos r = o + tableOffset h es j) (m₀ : ℕ) (hm₀ : 0 < m₀)
    (hm₀m : m₀ ≤ m) : RecordAt d r (es[j].take m₀) := by
  let pre := h :: (es.take j).flatten
  let gs := es[j].take m₀
  let post := es[j].drop m₀ ++ (es.drop (j + 1)).flatten
  have hem : es[j].length = m := (hwf.2 es[j] (List.getElem_mem hj)).1
  have hgs : gs ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp only [gs, List.length_take, hem, Nat.min_eq_left hm₀m]
    exact hm₀
  have hes := (List.take_append_drop j es).symm
  rw [List.drop_eq_getElem_cons hj] at hes
  have hlayout : tableFields h es = pre ++ (gs ++ post) := by
    calc
      tableFields h es = h :: ((es.take j).flatten ++
          (es[j] ++ (es.drop (j + 1)).flatten)) := by
        unfold tableFields
        conv_lhs => rw [hes]
        simp only [List.flatten_append, List.flatten_cons]
      _ = pre ++ (gs ++ post) := by
        simp only [pre, gs, post, List.cons_append, ← List.append_assoc,
          List.take_append_drop]
  have hoff : fieldOffset (tableFields h es) pre.length = tableOffset h es j := by
    simp only [tableOffset, pre, List.length_cons, List.length_flatten, Nat.add_comm]
  have hslice := rt_fields_slice pre gs post hgs
  rw [← hlayout, hoff] at hslice
  intro p hp hp'
  rw [hpos, add_assoc, ht ((tableOffset h es j : ℤ) + p) (by omega) (by
    have := hslice.1
    change p ≤ ((joinFields gs).length : ℤ) at hp'
    omega)]
  exact hslice.2 p hp hp'

/-! ### The end-to-start adapter -/

/-- **The end-to-start adapter** (design §12.8b, decision 2 of §12.8a §9):
from the cell where `Turing.seekEndTM` stops, the second blank after a field
layout, skip back over the last field (`Turing.skipBackTM`), then seek the
start (`Turing.seekStartTM`). The two are joined by one seam. Nothing is
written. -/
def tableRewindTM {Γ : Type*} (k : ℕ) (i : Fin k) : MultiTapeTM k Γ (SeekPhase ⊕ SeekPhase) :=
  seamCompTM (skipBackTM k i) .done (seekStartTM k i) .run

/-- **The end-to-start adapter, framed** (design §12.8b). Let tape `i` hold a
nonempty list `ws` of nonempty fields in the field layout, preceded by two
blank cells and followed by one, with the head on the cell after that blank,
at `D = fieldOffset ws |ws|` from the layout's start. Then the adapter reaches
`Sum.inr done` at exactly `D + 7`, with the head of tape `i` at the layout's
start and nothing else changed, and not earlier. The current cell and the cells
beyond the sentinels are arbitrary. Up to the exit the head stays within
`[pos - D - 2, pos]`, and every other head is fixed. For a table at `o`, `ws`
is its field list, the start is `o`, and `D + 7` is the layout length plus
eight.

**Proof sketch.** `Turing.seamCompTM_run_ofCfg` with `Turing.skipBackTM_run_ofCfg`
over the last field `u`, which starts at `pos - |u| - 1`, in `|u| + 3` steps,
then the dispatch step, then `Turing.seekStartTM_run_ofCfg` from the first cell
of `u`, which is nonblank, over the remaining fields, in `D' + 4` steps with
`D = D' + |u| + 1`. The framing of `u` and of the remaining fields is
`Turing.fieldsTape_field` and the split of `Turing.fieldOffset` at the last
field. The first-return cut is `Turing.seamCompTM_firstReturn_ofCfg`.

**Fill appendix.** The two phase contracts supply the exact run and cut.
`Turing.seamCompTM_visitedByTapeHead_ofCfg` transports their head bounds;
`rt_fields_slice` restricts the original frame to the prefix before the last field. -/
theorem tableRewindTM_run_ofCfg {Γ : Type*} {k : ℕ} {x : List Γ} (i : Fin k)
    (ws : List (List Γ)) (hne : ws ≠ []) (hws : ∀ u ∈ ws, u ≠ [])
    (d : Cfg k Γ (SeekPhase ⊕ SeekPhase) x) (hstate : d.state = some (Sum.inl .run))
    (hw : ∀ p : ℤ, -2 ≤ p → p < (fieldOffset ws ws.length : ℤ) →
      d.workTapes i (d.workTapePos i - fieldOffset ws ws.length + p) = fieldsTape ws p) :
    (tableRewindTM k i).runFrom d (fieldOffset ws ws.length + 7) =
        { d with
          state := some (Sum.inr .done)
          workTapePos := Function.update d.workTapePos i
            (d.workTapePos i - fieldOffset ws ws.length) } ∧
      (∀ t < fieldOffset ws ws.length + 7,
        ((tableRewindTM k i).runFrom d t).state ≠ some (Sum.inr .done)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ fieldOffset ws ws.length + 7 →
        if j = i then
          ((tableRewindTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - fieldOffset ws ws.length - 2) (d.workTapePos j)
        else ((tableRewindTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  classical
  have hlen : 0 < ws.length := List.length_pos_iff.mpr hne
  let a := ws.length - 1
  have ha : a < ws.length := by omega
  let pre := ws.take a
  let u := ws[a]
  have hprelen : pre.length = a := by simp [pre, Nat.min_eq_left (Nat.le_of_lt ha)]
  have hsplit : ws = pre ++ [u] := by
    simpa only [pre, u, show a + 1 = ws.length by omega, List.take_length] using
      (List.take_append_getElem ha).symm
  have ho : fieldOffset ws a = fieldOffset pre pre.length := by
    rw [hprelen]
    simp only [fieldOffset, pre, List.take_take, Nat.min_self]
  have hD : fieldOffset ws ws.length = fieldOffset pre pre.length + u.length + 1 := by
    have hh := fieldOffset_succ ws a ha
    rw [show a + 1 = ws.length by omega, ho] at hh
    simpa only [u, Nat.add_assoc] using hh
  let c₀ : Cfg k Γ SeekPhase x := d.mapState (fun _ => .run)
  let c₁ : Cfg k Γ SeekPhase x :=
    { c₀ with
      state := some .done
      workTapePos := Function.update c₀.workTapePos i (c₀.workTapePos i - u.length - 1) }
  have hc₀ : c₀.state = some .run := by simp [c₀, Cfg.mapState, hstate]
  have hentry : c₀.mapState Sum.inl = d := by
    apply Cfg.ext <;> simp [c₀, Cfg.mapState, hstate]
  have hu (p : ℤ) (hp : -1 ≤ p) (hp' : p ≤ (u.length : ℤ)) :
      c₀.workTapes i (c₀.workTapePos i - u.length - 1 + p) = FinTM.bufferTape u p := by
    change d.workTapes i (d.workTapePos i - u.length - 1 + p) = _
    have heq : d.workTapePos i - u.length - 1 + p =
        d.workTapePos i - fieldOffset ws ws.length + ((fieldOffset ws a : ℤ) + p) := by
      rw [ho]
      omega
    rw [heq, hw _ (by omega) (by rw [ho]; omega)]
    exact fieldsTape_field ws a ha p hp hp'
  obtain ⟨h₁, hcut₁, hrad₁⟩ := skipBackTM_run_ofCfg i u c₀ hc₀ hu
  change (skipBackTM k i).runFrom c₀ (u.length + 3) = c₁ at h₁
  let c₂ := c₁.mapState (fun _ => SeekPhase.run)
  have hnonempty : u ≠ [] := hws u (List.getElem_mem ha)
  have hcur : c₂.workTapes i (c₂.workTapePos i) ≠ none := by
    have hh := hu 0 (by omega) (by omega)
    simp only [add_zero, c₀, Cfg.mapState] at hh
    change d.workTapes i (Function.update d.workTapePos i
      (d.workTapePos i - u.length - 1) i) ≠ none
    rw [Function.update_self, hh]
    cases he : u with
    | nil => exact False.elim (hnonempty he)
    | cons b bs => simp [FinTM.bufferTape]
  have hframe (p : ℤ) (hp : -2 ≤ p)
      (hp' : p < (fieldOffset pre pre.length : ℤ)) :
      c₂.workTapes i (c₂.workTapePos i - fieldOffset pre pre.length + p) =
        fieldsTape pre p := by
    change d.workTapes i (Function.update d.workTapePos i
      (d.workTapePos i - u.length - 1) i - fieldOffset pre pre.length + p) = _
    rw [Function.update_self]
    have heq : d.workTapePos i - u.length - 1 - fieldOffset pre pre.length + p =
        d.workTapePos i - fieldOffset ws ws.length + p := by omega
    rw [heq, hw p hp (by omega)]
    by_cases hp0 : 0 ≤ p
    · have hprene : pre ≠ [] := by
        intro he
        simp [he, fieldOffset] at hp'
        omega
      have hs := (rt_fields_slice [] pre [u] hprene).2 p (by omega) (by
        have := fieldOffset_length pre hprene
        omega)
      simpa only [List.nil_append, fieldOffset, List.length_nil, List.take_zero, List.map_nil,
        List.sum_nil, Nat.cast_zero, zero_add, ← hsplit] using hs
    · simp [fieldsTape, hp0]
  have hpre : ∀ v ∈ pre, v ≠ [] := fun v hv => hws v (List.mem_of_mem_take hv)
  obtain ⟨h₂, hcut₂, hrad₂⟩ := seekStartTM_run_ofCfg i pre hpre c₂ rfl hcur hframe
  let c₃ : Cfg k Γ SeekPhase x :=
    { c₂ with
      state := some .done
      workTapePos := Function.update c₂.workTapePos i
        (c₂.workTapePos i - fieldOffset pre pre.length) }
  change (seekStartTM k i).runFrom (c₁.mapState fun _ => SeekPhase.run)
    (fieldOffset pre pre.length + 4) = c₃ at h₂
  have htime : u.length + 3 + 1 + (fieldOffset pre pre.length + 4) =
      fieldOffset ws ws.length + 7 := by omega
  have hrun := seamCompTM_run_ofCfg (skipBackTM k i) .done (seekStartTM k i) .run
    h₁ rfl hcut₁ h₂
  have hcut := seamCompTM_firstReturn_ofCfg (skipBackTM k i) .done
    (seekStartTM k i) .run .done h₁ rfl hcut₁ h₂ rfl hcut₂
  rw [hentry, htime] at hrun hcut
  refine ⟨?_, hcut, ?_⟩
  · change (tableRewindTM k i).runFrom d (fieldOffset ws ws.length + 7) =
      c₃.mapState Sum.inr at hrun
    rw [hrun]
    apply Cfg.ext <;> simp [c₃, c₂, c₁, c₀, Cfg.mapState, Function.update_idem,
      show d.workTapePos i - (u.length : ℤ) - 1 - fieldOffset pre pre.length =
        d.workTapePos i - fieldOffset ws ws.length by omega]
  · intro j t ht
    let region := Finset.Icc
      (if j = i then d.workTapePos j - fieldOffset ws ws.length - 2 else d.workTapePos j)
      (d.workTapePos j)
    have cover :
        (skipBackTM k i).visitedByTapeHead c₀ (u.length + 3) j ∪
          (seekStartTM k i).visitedByTapeHead c₂ (fieldOffset pre pre.length + 4) j ⊆
        region := by
      apply Finset.union_subset
      · apply Finset.image_subset_iff.mpr
        intro v hv
        have bounds := hrad₁ j v (Nat.le_of_lt_succ (Finset.mem_range.mp hv))
        by_cases hji : j = i
        · subst j
          simp only [if_true, Finset.mem_Icc] at bounds
          change d.workTapePos i - (u.length : ℤ) - 2 ≤ _ ∧ _ ≤ d.workTapePos i at bounds
          simp only [region, if_true, Finset.mem_Icc]
          omega
        · simp only [if_neg hji] at bounds
          simp only [region, if_neg hji, Finset.mem_Icc]
          rw [bounds]
          simp only [c₀, Cfg.mapState, le_refl, and_self]
      · apply Finset.image_subset_iff.mpr
        intro v hv
        have bounds := hrad₂ j v (Nat.le_of_lt_succ (Finset.mem_range.mp hv))
        by_cases hji : j = i
        · subst j
          simp only [if_true, Finset.mem_Icc] at bounds
          change Function.update d.workTapePos i (d.workTapePos i - u.length - 1) i -
              fieldOffset pre pre.length - 2 ≤ _ ∧
            _ ≤ Function.update d.workTapePos i (d.workTapePos i - u.length - 1) i at bounds
          rw [Function.update_self] at bounds
          simp only [region, if_true, Finset.mem_Icc]
          omega
        · simp only [if_neg hji] at bounds
          simp only [region, if_neg hji, Finset.mem_Icc]
          rw [bounds]
          simp only [c₂, c₁, c₀, Cfg.mapState, Function.update_of_ne hji, le_refl, and_self]
    have transfer := seamCompTM_visitedByTapeHead_ofCfg (skipBackTM k i) .done
      (seekStartTM k i) .run (T₂ := fieldOffset pre pre.length + 4) h₁ rfl hcut₁ j
    rw [hentry, htime] at transfer
    have membership : ((tableRewindTM k i).runFrom d t).workTapePos j ∈ region := by
      apply cover
      apply transfer
      exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
    by_cases hji : j = i
    · simpa only [region, if_pos hji] using membership
    · simp only [region, if_neg hji, Finset.mem_Icc] at membership
      simpa only [if_neg hji] using le_antisymm membership.2 membership.1

/-! ### Copying a field list -/

/-- The fixed field count determines a finite sum of the catalog phase types. -/
private def rt_copyState : ℕ → Type
  | 0 => Unit
  | 1 => SweepPhase
  | m + 2 => SweepPhase ⊕ (SeekPhase ⊕ (SeekPhase ⊕
      (rt_copyState (m + 1) ⊕ (SeekPhase ⊕ SeekPhase))))

/-- The recursive field-copy controller has finitely many states. -/
private instance rt_copyState_fintype : (m : ℕ) → Fintype (rt_copyState m)
  | 0 => inferInstanceAs (Fintype Unit)
  | 1 => inferInstanceAs (Fintype SweepPhase)
  | m + 2 => by
    letI := rt_copyState_fintype (m + 1)
    change Fintype (SweepPhase ⊕ (SeekPhase ⊕ (SeekPhase ⊕
      (rt_copyState (m + 1) ⊕ (SeekPhase ⊕ SeekPhase)))))
    infer_instance

/-- Equality of the finite field-copy control states is decidable. -/
private instance rt_copyState_decidableEq : (m : ℕ) → DecidableEq (rt_copyState m)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | 1 => inferInstanceAs (DecidableEq SweepPhase)
  | m + 2 => by
    letI := rt_copyState_decidableEq (m + 1)
    change DecidableEq (SweepPhase ⊕ (SeekPhase ⊕ (SeekPhase ⊕
      (rt_copyState (m + 1) ⊕ (SeekPhase ⊕ SeekPhase)))))
    infer_instance

/-- The field-copy entry is the first copy's sweep state; the empty case is a no-op. -/
private def rt_copyEntry : (m : ℕ) → rt_copyState m
  | 0 => ()
  | 1 => .sweep
  | _ + 2 => .inl .sweep

/-- The field-copy exit is the last backward skip's anchor. -/
private def rt_copyExit : (m : ℕ) → rt_copyState m
  | 0 => ()
  | 1 => .done
  | _ + 2 => .inr (.inr (.inr (.inr (.inr .done))))

/-- A fixed field-list copier built exclusively by catalog rows and R2 seams.

**Proof sketch.** Zero fields return immediately; one field uses `copyTM`. For two or
more, copy the first field, skip it on the source and destination, run the copier for
the nonempty tail, and skip back once on each tape. Every seam intercepts its catalog
exit, including the recursive copier's exit. No transition-level host is introduced. -/
private def rt_copyMachine {Γ : Type*} : (m : ℕ) → MultiTapeTM 2 Γ (rt_copyState m)
  | 0 => { q₀ := (), tr := fun _ _ _ => ⟨0, fun _ => (none, 0), none, some ()⟩ }
  | 1 => copyTM 2 0 1
  | m + 2 =>
    seamCompTM (copyTM 2 0 1) .done
      (seamCompTM (skipTM 2 0) .done
        (seamCompTM (skipTM 2 1) .done
          (seamCompTM (rt_copyMachine (m + 1)) (rt_copyExit (m + 1))
            (seamCompTM (skipBackTM 2 0) .done (skipBackTM 2 1) .run) (.inl .run))
          (.inl (rt_copyEntry (m + 1)))) (.inl .run)) (.inl .run)

/-- The field-copy contract for its zero-field and one-field base cases.

**Proof sketch.** The empty layout changes no cell and returns at time zero. For a
singleton, apply the public copy contract and `fieldsTape_field`; its two head intervals
lie within twice the layout length plus one. -/
private theorem rt_copy_run_base {Γ : Type*} (m : ℕ) (hm : m ≤ 1) :
    ∃ C : ℕ,
      ∀ {x : List Γ} (fs : List (List Γ)), fs.length = m →
      ∀ d : Cfg 2 Γ (rt_copyState m) x, d.state = some (rt_copyEntry m) → RecordAt d 0 fs →
        (∀ p : ℤ, -1 ≤ p → p ≤ ((joinFields fs).length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = none) →
        ∃ t ≤ C * ((joinFields fs).length + 1),
          (∀ u < t, ((rt_copyMachine m).runFrom d u).state ≠ some (rt_copyExit m)) ∧
          (∀ u ≤ t, ∀ j : Fin 2,
            |((rt_copyMachine m).runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((joinFields fs).length + 1) : ℕ) : ℤ)) ∧
          (rt_copyMachine m).runFrom d t =
            { d with
              state := some (rt_copyExit m)
              workTapes := fun j q =>
                if j = 1 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + ((joinFields fs).length : ℤ)
                  then fieldsTape fs (q - d.workTapePos j)
                else d.workTapes j q } := by
  rcases m with _ | m
  · refine ⟨0, ?_⟩
    intro x fs hfs d hd _ _
    have hnil : fs = [] := List.eq_nil_of_length_eq_zero hfs
    subst fs
    refine ⟨0, by simp, by simp, ?_, ?_⟩
    · intro v hv j
      have hv0 : v = 0 := by omega
      subst v
      simp
    · apply Cfg.ext <;> simp [joinFields, List.intercalate, hd, rt_copyEntry, rt_copyExit]
      funext j q
      split_ifs with h
      · omega
      · rfl
  · have hm0 : m = 0 := by omega
    subst m
    refine ⟨2, ?_⟩
    intro x fs hfs d hd hsrc _
    obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hfs
    have hlen : (joinFields [u]).length = u.length := by simp [joinFields, List.intercalate]
    have hword (p : ℤ) (hp : -1 ≤ p) (hp' : p ≤ (u.length : ℤ)) :
        d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape u p := by
      rw [hsrc p hp (by simpa only [hlen] using hp')]
      simpa only [fieldOffset, List.take_zero, List.map_nil, List.sum_nil,
        Nat.cast_zero, zero_add, List.getElem_cons_zero] using
        fieldsTape_field [u] 0 (by simp) p hp hp'
    obtain ⟨hcopy, hcut, hrad⟩ := copyTM_run_ofCfg (0 : Fin 2) 1 (by decide) u d hd hword
    refine ⟨2 * u.length + 2, by omega, hcut, ?_, ?_⟩
    · intro v hv j
      have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      have hr := hrad j v hv
      simp only [hj, if_true, Finset.mem_Icc] at hr
      change |((copyTM 2 0 1).runFrom d v).workTapePos j - d.workTapePos j| ≤ _
      rw [abs_le]
      constructor <;> omega
    · change (copyTM 2 0 1).runFrom d (2 * u.length + 2) = _
      rw [hcopy, hlen]
      congr 1
      funext j q
      split_ifs with h
      · have hh := fieldsTape_field [u] 0 (by simp) (q - d.workTapePos j)
          (by omega) (by change q - d.workTapePos j ≤ (u.length : ℤ); omega)
        simpa only [fieldOffset, List.take_zero, List.map_nil, List.sum_nil,
          Nat.cast_zero, zero_add, List.getElem_cons_zero] using hh.symm
      · rfl

/-- Combine the copier's phase certificates without re-proving the seam trace.

**Proof sketch.** The public seam contracts give the endpoint and cut. Their
visited-set inclusion places each composite head in one of the two phase runs,
so a common interval about the original heads remains an interval for the seam. -/
private theorem rt_copy_seam {Γ S₁ S₂ : Type*} {k : ℕ} {x : List Γ}
    [DecidableEq S₁] (M₁ : MultiTapeTM k Γ S₁) (q₁ : S₁)
    (M₂ : MultiTapeTM k Γ S₂) (entry q₂ : S₂)
    {a b : Cfg k Γ S₁ x} {c : Cfg k Γ S₂ x} {t₁ t₂ : ℕ}
    (origin : Fin k → ℤ) (B : ℤ)
    (h₁ : M₁.runFrom a t₁ = b) (hb : b.state = some q₁)
    (hc₁ : ∀ v < t₁, (M₁.runFrom a v).state ≠ some q₁)
    (hr₁ : ∀ v ≤ t₁, ∀ j, |(M₁.runFrom a v).workTapePos j - origin j| ≤ B)
    (h₂ : M₂.runFrom (b.mapState fun _ => entry) t₂ = c) (hc : c.state = some q₂)
    (hc₂ : ∀ v < t₂, (M₂.runFrom (b.mapState fun _ => entry) v).state ≠ some q₂)
    (hr₂ : ∀ v ≤ t₂, ∀ j,
      |(M₂.runFrom (b.mapState fun _ => entry) v).workTapePos j - origin j| ≤ B) :
    (seamCompTM M₁ q₁ M₂ entry).runFrom (a.mapState Sum.inl) (t₁ + 1 + t₂) =
        c.mapState Sum.inr ∧
      (∀ v < t₁ + 1 + t₂,
        ((seamCompTM M₁ q₁ M₂ entry).runFrom (a.mapState Sum.inl) v).state ≠
          some (Sum.inr q₂)) ∧
      (∀ v ≤ t₁ + 1 + t₂, ∀ j,
        |((seamCompTM M₁ q₁ M₂ entry).runFrom (a.mapState Sum.inl) v).workTapePos j -
          origin j| ≤ B) := by
  refine ⟨seamCompTM_run_ofCfg M₁ q₁ M₂ entry h₁ hb hc₁ h₂,
    seamCompTM_firstReturn_ofCfg M₁ q₁ M₂ entry q₂ h₁ hb hc₁ h₂ hc hc₂, ?_⟩
  intro v hv j
  have hmem := seamCompTM_visitedByTapeHead_ofCfg M₁ q₁ M₂ entry
    (T₂ := t₂) h₁ hb hc₁ j
    (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hv)))
  rcases Finset.mem_union.mp hmem with hmem | hmem
  · obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hmem
    rw [← he]
    exact hr₁ r (Nat.le_of_lt_succ (Finset.mem_range.mp hr)) j
  · obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hmem
    rw [← he]
    exact hr₂ r (Nat.le_of_lt_succ (Finset.mem_range.mp hr)) j

/-- The frozen recursive copier satisfies its contract for every field count.

**Proof sketch.** Induct on the field count, citing the frozen two base cases.
Copy the first field, skip it on both tapes, invoke the nonempty-tail contract,
and skip back on both tapes. The two write regions meet at a blank separator.
Compose all six phases by the public seam contracts and enlarge the tail constant
by 20 to cover the first field, five dispatches, and the shift of the tail frame. -/
private theorem rt_copy_run {Γ : Type*} (m : ℕ) :
    ∃ C : ℕ,
      ∀ {x : List Γ} (fs : List (List Γ)), fs.length = m →
      ∀ d : Cfg 2 Γ (rt_copyState m) x, d.state = some (rt_copyEntry m) → RecordAt d 0 fs →
        (∀ p : ℤ, -1 ≤ p → p ≤ ((joinFields fs).length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = none) →
        ∃ t ≤ C * ((joinFields fs).length + 1),
          (∀ u < t, ((rt_copyMachine m).runFrom d u).state ≠ some (rt_copyExit m)) ∧
          (∀ u ≤ t, ∀ j : Fin 2,
            |((rt_copyMachine m).runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((joinFields fs).length + 1) : ℕ) : ℤ)) ∧
          (rt_copyMachine m).runFrom d t =
            { d with
              state := some (rt_copyExit m)
              workTapes := fun j q =>
                if j = 1 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + ((joinFields fs).length : ℤ)
                  then fieldsTape fs (q - d.workTapePos j)
                else d.workTapes j q } := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m ≤ 1
    · exact rt_copy_run_base m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    obtain ⟨C, hC⟩ := ih (n + 1) (by omega)
    refine ⟨C + 20, ?_⟩
    intro x fs hfs d hd hsrc hblank
    cases fs with
    | nil => simp at hfs
    | cons u tail =>
      have htail : tail.length = n + 1 := by simpa using hfs
      have hne : tail ≠ [] := by intro he; simp [he] at htail
      have hlen : (joinFields (u :: tail)).length =
          u.length + 1 + (joinFields tail).length := by
        cases tail with
        | nil => exact False.elim (hne rfl)
        | cons v vs => simp only [joinFields_cons_cons, List.length_append, List.length_map, List.length_cons]; omega
      have hfirst (p : ℤ) (hp : -1 ≤ p) (hp' : p ≤ (u.length : ℤ)) :
          d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape u p := by
        rw [hsrc p hp (by omega)]
        simpa only [fieldOffset, List.take_zero, List.map_nil, List.sum_nil,
          Nat.cast_zero, zero_add, List.getElem_cons_zero] using
          fieldsTape_field (u :: tail) 0 (by simp) p hp hp'
      let a₀ : Cfg 2 Γ SweepPhase x := d.mapState (fun _ => .sweep)
      let a₁ : Cfg 2 Γ SweepPhase x :=
        { a₀ with state := some .done
                  workTapes := fun j q =>
                    if j = 1 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (u.length : ℤ)
                    then FinTM.bufferTape u (q - d.workTapePos j)
                    else d.workTapes j q }
      have ha₀ : a₀.state = some .sweep := by simp [a₀, Cfg.mapState, hd]
      obtain ⟨hr₀, hc₀, hb₀⟩ := copyTM_run_ofCfg (0 : Fin 2) 1 (by decide) u a₀ ha₀ hfirst
      change (copyTM 2 0 1).runFrom a₀ (2 * u.length + 2) = a₁ at hr₀
      have hword (j : Fin 2) (p : ℤ) (hp : -1 ≤ p) (hp' : p ≤ (u.length : ℤ)) :
          a₁.workTapes j (d.workTapePos j + p) = FinTM.bufferTape u p := by
        fin_cases j
        · simpa [a₁, a₀, Cfg.mapState] using hfirst p hp hp'
        · change (if (1 : Fin 2) = 1 ∧ d.workTapePos 1 ≤ d.workTapePos 1 + p ∧
              d.workTapePos 1 + p < d.workTapePos 1 + (u.length : ℤ)
            then FinTM.bufferTape u (d.workTapePos 1 + p - d.workTapePos 1)
            else d.workTapes 1 (d.workTapePos 1 + p)) = _
          split_ifs with hh
          · congr 1; omega
          · rw [hblank p hp (by omega)]
            have he : p = -1 ∨ p = (u.length : ℤ) := by omega
            rcases he with rfl | rfl <;> simp [FinTM.bufferTape]
      let a₂ := a₁.mapState (fun _ => SeekPhase.run)
      let a₃ : Cfg 2 Γ SeekPhase x :=
        { a₂ with state := some .done
                  workTapePos := Function.update a₂.workTapePos 0
                    (a₂.workTapePos 0 + u.length + 1) }
      obtain ⟨hr₁, hc₁, hb₁⟩ := skipTM_run_ofCfg (0 : Fin 2) u a₂ rfl
        (fun p hp hp' => hword 0 p (by omega) hp')
      change (skipTM 2 0).runFrom a₂ (u.length + 1) = a₃ at hr₁
      let a₄ := a₃.mapState (fun _ => SeekPhase.run)
      let a₅ : Cfg 2 Γ SeekPhase x :=
        { a₄ with state := some .done
                  workTapePos := Function.update a₄.workTapePos 1
                    (a₄.workTapePos 1 + u.length + 1) }
      have ha₄ : a₄.workTapePos 1 = d.workTapePos 1 := by
        simp [a₄, a₃, a₂, a₁, a₀, Cfg.mapState]
      obtain ⟨hr₂, hc₂, hb₂⟩ := skipTM_run_ofCfg (1 : Fin 2) u a₄ rfl
        (fun p hp hp' => by
          change a₁.workTapes 1 (a₄.workTapePos 1 + p) = _
          rw [ha₄]
          exact hword 1 p (by omega) hp')
      change (skipTM 2 1).runFrom a₄ (u.length + 1) = a₅ at hr₂
      let a₆ := a₅.mapState (fun _ => rt_copyEntry (n + 1))
      have hpos (j : Fin 2) : a₆.workTapePos j = d.workTapePos j + u.length + 1 := by
        fin_cases j <;> simp [a₆, a₅, a₄, a₃, a₂, a₁, a₀, Cfg.mapState]
      have hsrctail : RecordAt a₆ 0 tail := by
        intro p hp hp'
        change a₁.workTapes 0 (a₆.workTapePos 0 + p) = _
        rw [hpos]
        simp only [a₁, show (0 : Fin 2) ≠ 1 by decide,
          false_and, if_false]
        rw [show d.workTapePos 0 + (u.length : ℤ) + 1 + p =
          d.workTapePos 0 + ((u.length : ℤ) + 1 + p) by omega,
          hsrc _ (by omega) (by omega)]
        have hs := (rt_fields_slice [u] tail [] hne).2 p hp hp'
        simpa [fieldOffset] using hs
      have hblanktail (p : ℤ) (hp : -1 ≤ p)
          (hp' : p ≤ ((joinFields tail).length : ℤ)) :
          a₆.workTapes 1 (a₆.workTapePos 1 + p) = none := by
        change a₁.workTapes 1 (a₆.workTapePos 1 + p) = _
        rw [hpos]
        simp only [a₁]
        rw [if_neg (by omega)]
        rw [show d.workTapePos 1 + (u.length : ℤ) + 1 + p =
          d.workTapePos 1 + ((u.length : ℤ) + 1 + p) by omega]
        exact hblank _ (by omega) (by omega)
      obtain ⟨t, ht, hc₃, hb₃, hr₃⟩ := hC tail htail a₆ rfl hsrctail hblanktail
      let a₇ : Cfg 2 Γ (rt_copyState (n + 1)) x :=
        { a₆ with state := some (rt_copyExit (n + 1))
                  workTapes := fun j q =>
                    if j = 1 ∧ a₆.workTapePos j ≤ q ∧
                        q < a₆.workTapePos j + ((joinFields tail).length : ℤ)
                    then fieldsTape tail (q - a₆.workTapePos j)
                    else a₆.workTapes j q }
      change (rt_copyMachine (n + 1)).runFrom a₆ t = a₇ at hr₃
      have hfirst₇ (j : Fin 2) (p : ℤ) (hp : -1 ≤ p) (hp' : p ≤ (u.length : ℤ)) :
          a₇.workTapes j (d.workTapePos j + p) = FinTM.bufferTape u p := by
        change (if j = 1 ∧ a₆.workTapePos j ≤ d.workTapePos j + p ∧
            d.workTapePos j + p < a₆.workTapePos j + ((joinFields tail).length : ℤ)
          then _ else a₁.workTapes j (d.workTapePos j + p)) = _
        rw [hpos, if_neg (by omega)]
        exact hword j p hp hp'
      let a₈ := a₇.mapState (fun _ => SeekPhase.run)
      let a₉ : Cfg 2 Γ SeekPhase x :=
        { a₈ with state := some .done
                  workTapePos := Function.update a₈.workTapePos 0
                    (a₈.workTapePos 0 - u.length - 1) }
      obtain ⟨hr₄, hc₄, hb₄⟩ := skipBackTM_run_ofCfg (0 : Fin 2) u a₈ rfl
        (fun p hp hp' => by
          change a₇.workTapes 0 (a₆.workTapePos 0 - u.length - 1 + p) = _
          rw [hpos]
          convert hfirst₇ 0 p hp hp' using 1; congr 1; omega)
      change (skipBackTM 2 0).runFrom a₈ (u.length + 3) = a₉ at hr₄
      let a₁₀ := a₉.mapState (fun _ => SeekPhase.run)
      let a₁₁ : Cfg 2 Γ SeekPhase x :=
        { a₁₀ with state := some .done
                   workTapePos := Function.update a₁₀.workTapePos 1
                     (a₁₀.workTapePos 1 - u.length - 1) }
      have ha₁₀ : a₁₀.workTapePos 1 = a₆.workTapePos 1 := by
        simp [a₁₀, a₉, a₈, a₇, Cfg.mapState]
      obtain ⟨hr₅, hc₅, hb₅⟩ := skipBackTM_run_ofCfg (1 : Fin 2) u a₁₀ rfl
        (fun p hp hp' => by
          change a₇.workTapes 1 (a₁₀.workTapePos 1 - u.length - 1 + p) = _
          rw [ha₁₀, hpos]
          convert hfirst₇ 1 p hp hp' using 1; congr 1; omega)
      change (skipBackTM 2 1).runFrom a₁₀ (u.length + 3) = a₁₁ at hr₅
      have hmerged : a₇.workTapes = fun j q =>
          if j = 1 ∧ d.workTapePos j ≤ q ∧
              q < d.workTapePos j + ((joinFields (u :: tail)).length : ℤ)
          then fieldsTape (u :: tail) (q - d.workTapePos j)
          else d.workTapes j q := by
        funext j q
        change (if j = 1 ∧ a₆.workTapePos j ≤ q ∧
            q < a₆.workTapePos j + ((joinFields tail).length : ℤ)
          then fieldsTape tail (q - a₆.workTapePos j)
          else a₁.workTapes j q) = _
        rw [hpos]
        by_cases hj : j = 1
        · subst j
          simp only [a₁, true_and]
          by_cases htq : d.workTapePos 1 + u.length + 1 ≤ q ∧
              q < d.workTapePos 1 + u.length + 1 + ((joinFields tail).length : ℤ)
          · rw [if_pos htq, if_pos (by omega)]
            have hs := (rt_fields_slice [u] tail [] hne).2
              (q - (d.workTapePos 1 + u.length + 1)) (by omega) (by omega)
            simp only [List.append_nil, List.singleton_append, fieldOffset,
              List.length_singleton, List.take_succ_cons, List.take_zero,
              List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
              add_zero, Nat.cast_add, Nat.cast_one] at hs
            convert hs.symm using 1; congr 1; omega
          · rw [if_neg htq]
            by_cases hfq : d.workTapePos 1 ≤ q ∧ q < d.workTapePos 1 + (u.length : ℤ)
            · rw [if_pos hfq, if_pos (by omega)]
              have hf := fieldsTape_field (u :: tail) 0 (by simp)
                (q - d.workTapePos 1) (by omega) (by change q - d.workTapePos 1 ≤ (u.length : ℤ); omega)
              simpa only [fieldOffset, List.take_zero, List.map_nil, List.sum_nil,
                Nat.cast_zero, zero_add, List.getElem_cons_zero] using hf.symm
            · rw [if_neg hfq]
              by_cases hq : d.workTapePos 1 ≤ q ∧
                  q < d.workTapePos 1 + ((joinFields (u :: tail)).length : ℤ)
              · rw [if_pos hq]
                have heq : q = d.workTapePos 1 + u.length := by omega
                subst q
                rw [hblank _ (by omega) (by omega)]
                have hf := fieldsTape_field (u :: tail) 0 (by simp)
                  (u.length : ℤ) (by omega) (by rfl)
                simpa [fieldOffset, FinTM.bufferTape] using hf.symm
              · rw [if_neg hq]
        · simp [a₁, hj]
      have hBnat : C * ((joinFields tail).length + 1) + u.length + 2 ≤
          (C + 20) * ((joinFields (u :: tail)).length + 1) := by
        have hh := Nat.mul_le_mul_left C
          (show (joinFields tail).length + 1 ≤ (joinFields (u :: tail)).length + 1 by omega)
        rw [Nat.add_mul]
        omega
      let B : ℤ := ((C + 20) * ((joinFields (u :: tail)).length + 1) : ℕ)
      have hB : (C * ((joinFields tail).length + 1) : ℕ) + (u.length : ℤ) + 2 ≤ B := by
        dsimp only [B]
        exact_mod_cast hBnat
      have pos₀ : a₀.workTapePos = d.workTapePos := rfl
      have pos₂ : a₂.workTapePos = d.workTapePos := rfl
      have pos₄ (j : Fin 2) : a₄.workTapePos j =
          if j = 0 then d.workTapePos j + u.length + 1 else d.workTapePos j := by
        simp [a₄, a₃, a₂, a₁, a₀, Cfg.mapState, Function.update_apply]
        split_ifs with hj
        · subst j; rfl
        · rfl
      have pos₈ (j : Fin 2) : a₈.workTapePos j = d.workTapePos j + u.length + 1 := hpos j
      have pos₁₀ (j : Fin 2) : a₁₀.workTapePos j =
          if j = 0 then d.workTapePos j else d.workTapePos j + u.length + 1 := by
        change Function.update a₆.workTapePos 0 (a₆.workTapePos 0 - u.length - 1) j = _
        simp only [Function.update_apply, hpos]
        split_ifs with hj
        · subst j; omega
        · rfl
      have bound₀ : ∀ v ≤ 2 * u.length + 2, ∀ j : Fin 2,
          |((copyTM 2 0 1).runFrom a₀ v).workTapePos j - d.workTapePos j| ≤ B := by
        intro v hv j
        have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
        have hh := hb₀ j v hv
        simp only [hj, if_true, Finset.mem_Icc, pos₀] at hh
        rw [abs_le]; constructor <;> omega
      have bound₁ : ∀ v ≤ u.length + 1, ∀ j : Fin 2,
          |((skipTM 2 0).runFrom a₂ v).workTapePos j - d.workTapePos j| ≤ B := by
        intro v hv j
        have hh := hb₁ j v hv
        rw [pos₂] at hh
        split_ifs at hh
        · simp only [Finset.mem_Icc] at hh
          rw [abs_le]; constructor <;> omega
        · rw [hh, sub_self, abs_zero]; omega
      have bound₂ : ∀ v ≤ u.length + 1, ∀ j : Fin 2,
          |((skipTM 2 1).runFrom a₄ v).workTapePos j - d.workTapePos j| ≤ B := by
        intro v hv j
        have hh := hb₂ j v hv
        simp only [pos₄] at hh
        fin_cases j <;> simp at hh ⊢
        · rw [hh, abs_le]; constructor <;> omega
        · rw [abs_le]; constructor <;> omega
      have bound₃ : ∀ v ≤ t, ∀ j : Fin 2,
          |((rt_copyMachine (n + 1)).runFrom a₆ v).workTapePos j - d.workTapePos j| ≤ B := by
        intro v hv j
        have hh := abs_le.mp (hb₃ v hv j)
        rw [hpos] at hh
        rw [abs_le]; constructor <;> omega
      have bound₄ : ∀ v ≤ u.length + 3, ∀ j : Fin 2,
          |((skipBackTM 2 0).runFrom a₈ v).workTapePos j - d.workTapePos j| ≤ B := by
        intro v hv j
        have hh := hb₄ j v hv
        simp only [pos₈] at hh
        split_ifs at hh
        · simp only [Finset.mem_Icc] at hh
          rw [abs_le]; constructor <;> omega
        · rw [hh, abs_le]; constructor <;> omega
      have bound₅ : ∀ v ≤ u.length + 3, ∀ j : Fin 2,
          |((skipBackTM 2 1).runFrom a₁₀ v).workTapePos j - d.workTapePos j| ≤ B := by
        intro v hv j
        have hh := hb₅ j v hv
        simp only [pos₁₀] at hh
        fin_cases j <;> simp at hh ⊢
        · rw [hh, abs_le]; constructor <;> omega
        · rw [abs_le]; constructor <;> omega
      let M₄₅ : MultiTapeTM 2 Γ (SeekPhase ⊕ SeekPhase) := seamCompTM (skipBackTM 2 0) SeekPhase.done (skipBackTM 2 1) SeekPhase.run
      obtain ⟨hr₄₅, hc₄₅, hb₄₅⟩ := rt_copy_seam (skipBackTM 2 0) .done
        (skipBackTM 2 1) .run .done d.workTapePos B
        hr₄ rfl hc₄ bound₄ hr₅ rfl hc₅ bound₅
      let M₃₄₅ := seamCompTM (rt_copyMachine (n + 1)) (rt_copyExit (n + 1)) M₄₅ (.inl .run)
      obtain ⟨hr₃₄₅, hc₃₄₅, hb₃₄₅⟩ := rt_copy_seam (rt_copyMachine (n + 1))
        (rt_copyExit (n + 1)) M₄₅ (.inl .run) (.inr .done) d.workTapePos B
        hr₃ rfl hc₃ bound₃ hr₄₅ rfl hc₄₅ hb₄₅
      let M₂₃₄₅ := seamCompTM (skipTM 2 1) SeekPhase.done M₃₄₅ (.inl (rt_copyEntry (n + 1)))
      obtain ⟨hr₂₃₄₅, hc₂₃₄₅, hb₂₃₄₅⟩ := rt_copy_seam (skipTM 2 1) .done
        M₃₄₅ (.inl (rt_copyEntry (n + 1))) (.inr (.inr .done)) d.workTapePos B
        hr₂ rfl hc₂ bound₂ hr₃₄₅ rfl hc₃₄₅ hb₃₄₅
      let M₁₂₃₄₅ := seamCompTM (skipTM 2 0) SeekPhase.done M₂₃₄₅ (.inl .run)
      obtain ⟨hr₁₂₃₄₅, hc₁₂₃₄₅, hb₁₂₃₄₅⟩ := rt_copy_seam (skipTM 2 0) .done
        M₂₃₄₅ (.inl .run) (.inr (.inr (.inr .done))) d.workTapePos B
        hr₁ rfl hc₁ bound₁ hr₂₃₄₅ rfl hc₂₃₄₅ hb₂₃₄₅
      obtain ⟨hr, hc, hb⟩ := rt_copy_seam (copyTM 2 0 1) .done
        M₁₂₃₄₅ (.inl .run) (.inr (.inr (.inr (.inr .done)))) d.workTapePos B
        hr₀ rfl hc₀ bound₀ hr₁₂₃₄₅ rfl hc₁₂₃₄₅ hb₁₂₃₄₅
      have hentry : a₀.mapState Sum.inl = d := by
        apply Cfg.ext <;> simp [a₀, Cfg.mapState, hd, rt_copyEntry]
      have htime : 2 * u.length + 2 + 1 + (u.length + 1 + 1 +
          (u.length + 1 + 1 + (t + 1 + (u.length + 3 + 1 + (u.length + 3))))) =
          t + 6 * u.length + 15 := by omega
      rw [hentry, htime] at hr hc hb
      refine ⟨t + 6 * u.length + 15, ?_, hc, hb, ?_⟩
      · have hmul := Nat.mul_le_mul_left C
          (show (joinFields tail).length + 1 ≤ (joinFields (u :: tail)).length + 1 by omega)
        rw [Nat.add_mul]
        omega
      · change (rt_copyMachine (n + 2)).runFrom d (t + 6 * u.length + 15) = _ at hr
        rw [hr]
        apply Cfg.ext
        · rfl
        · rfl
        · exact hmerged
        · funext j
          change Function.update a₁₀.workTapePos 1 (a₁₀.workTapePos 1 - u.length - 1) j = _
          simp only [Function.update_apply, pos₁₀]
          (fin_cases j <;> simp); omega
        · rfl

/-- **Field-list copy** (design §12.8b). For a fixed field count `m`, there is a
two-tape module with an entry and an exit state with the following contract.
Start it at its entry with a list `fs` of `m` fields laid out at the head of
tape `0` (`Turing.RecordAt`) and tape `1` blank on the cells from one left of
its head to one right of where the layout will end. It reaches its exit within
`C` times the layout length plus one, and not earlier, with the layout of `fs`
written at the head of tape `1` and nothing else changed: every head, the
source, the input position and the output are as they were. Up to the exit
both heads stay within that many cells of their entry positions. Fields may be
empty. It moves a record into a successor workspace, out of a table entry, or
onto Savitch's frame stack.

**Proof sketch.** For each of the `m` fields, `Turing.copyTM_run_ofCfg` copies
the field, which is a delimited word on tape `0` (`Turing.fieldsTape_field`),
into the blank slot, then `Turing.skipTM_run_ofCfg` advances both heads to the
next field; the copied field is delimited on tape `1` because the slot was
blank. Then `m` applications of `Turing.skipBackTM_run_ofCfg` on each tape
return the heads; the left delimiter of the first field on tape `1` is the
blank cell left of the slot. The phases join by R2 seams. Every phase is linear
in the fields crossed.

**Fill appendix.** The frozen `rt_copyMachine` realizes this route recursively:
copy one field, skip it on both tapes, copy the nonempty tail, then skip back
on both tapes. `rt_copy_run` cites the frozen base cases and proves the general
contract. Its six phase runs and five dispatches cost the tail time plus
`6 * u.length + 15` (the previous frontier overcounted by two). Increasing the
tail constant by 20 covers both time and shifted head bounds. `rt_copy_seam`
bundles the public R2 endpoint, cut and visited-set contracts; the two destination
write regions are combined using the existing field-layout lemmas. -/
theorem exists_fieldsCopyTM {Γ : Type*} (m : ℕ) :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (R : MultiTapeTM 2 Γ P) (entry exit : P)
      (C : ℕ),
      ∀ {x : List Γ} (fs : List (List Γ)), fs.length = m →
      ∀ d : Cfg 2 Γ P x, d.state = some entry → RecordAt d 0 fs →
        (∀ p : ℤ, -1 ≤ p → p ≤ ((joinFields fs).length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = none) →
        ∃ t ≤ C * ((joinFields fs).length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j : Fin 2,
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((joinFields fs).length + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with
              state := some exit
              workTapes := fun j q =>
                if j = 1 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + ((joinFields fs).length : ℤ)
                  then fieldsTape fs (q - d.workTapePos j)
                else d.workTapes j q } := by
  obtain ⟨C, hC⟩ := rt_copy_run (Γ := Γ) m
  exact ⟨rt_copyState m, inferInstance, inferInstance, rt_copyMachine m,
    rt_copyEntry m, rt_copyExit m, C, hC⟩

/-! ### The table rows -/

/-- The phases of one fuelled table-search round. -/
private inductive rt_findPhase (m : ℕ) (A : Type) where
  | read
  | scan (j : Fin m)
  | skip (j : Fin m) (a : A)
  | exit
deriving Fintype, DecidableEq

/-- Each search phase uses the existing row's control type. -/
private def rt_findControl {m : ℕ} {A : Type} : rt_findPhase m A → Type
  | .read => Option Bool
  | .scan _ => ScanPhase A
  | .skip _ _ => SeekPhase
  | .exit => Unit

private instance rt_findControl_fintype {m : ℕ} {A : Type} [Fintype A]
    (p : rt_findPhase m A) : Fintype (rt_findControl p) := by
  cases p <;> dsimp [rt_findControl] <;> infer_instance

private instance rt_findControl_decidableEq {m : ℕ} {A : Type} [DecidableEq A]
    (p : rt_findPhase m A) : DecidableEq (rt_findControl p) := by
  cases p <;> dsimp [rt_findControl] <;> infer_instance

/-- Read-only catalog phases for a table-search round. The one-cell read is
the only non-catalog action: it records whether the entry cell is blank. -/
private def rt_findParts {Γ A : Type} {m : ℕ}
    (δ : A → Option Γ → A) (a₀ : A) :
    (p : rt_findPhase m A) → MultiTapeTM 2 Γ (rt_findControl p)
  | .read =>
      { q₀ := none
        tr := fun q _ w => inputMoveAction 0
          (match q with | none => some (w 0).isSome | some b => some b) }
  | .scan _ => scanTM 2 0 (scanFold (fun a b => δ a (some b))) scanKeep a₀
  | .skip _ _ => skipTM 2 0
  | .exit => { q₀ := (), tr := fun _ _ _ => inputMoveAction 0 () }

/-- The finite redirect table counts fields and carries the fold accumulator.
Acceptance redirects before the final skip, preserving the nonblank witness.
The common escape is distinguished later by reading that same tape cell. -/
private def rt_findRedirect {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool) :
    (p : rt_findPhase m A) → rt_findControl p → Option (Σ p : rt_findPhase m A, rt_findControl p)
  | .read, none => none
  | .read, some false => some ⟨.exit, ()⟩
  | .read, some true => some ⟨.scan ⟨0, hm⟩, .fwd a₀⟩
  | .scan j, .done a =>
      if j.val + 1 < m then some ⟨.skip j (δ a none), .run⟩
      else if acc a then some ⟨.exit, ()⟩ else some ⟨.skip j a, .run⟩
  | .scan _, _ => none
  | .skip j a, .done =>
      if h : j.val + 1 < m then some ⟨.scan ⟨j.val + 1, h⟩, .fwd a⟩
      else some ⟨.read, none⟩
  | .skip _ _, _ => none
  | .exit, _ => none

/-- A round of table find uses the public finite phase host. Its entry is the
blank test, its escape is the single exit phase, and rejection of the final
field returns to the entry for the next counter-loop round. -/
private def rt_findRound {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool) :
    MultiTapeTM 2 Γ (Σ p : rt_findPhase m A, rt_findControl p) :=
  phaseHostTM (rt_findParts (m := m) δ a₀) ⟨.read, none⟩ (rt_findRedirect hm δ a₀ acc)

/-- A fold scan rewrites every cell to itself, so its catalog write mask
collapses to the original tape.

**Proof sketch.** Specialize the public scan contract to the fold instance.
The fold-result identity preserves the word; the supplied frame identifies
each masked cell with the old tape. The cut and head bounds are inherited. -/
private theorem rt_find_scan {Γ A : Type} {x : List Γ}
    (δ : A → Option Γ → A) (a : A) (w : List Γ)
    (d : Cfg 2 Γ (ScanPhase A) x) (hd : d.state = some (.fwd a))
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape w p) :
    (scanTM 2 0 (scanFold (fun b γ => δ b (some γ))) scanKeep a).runFrom d
        (2 * w.length + 2) =
      { d with state := some (.done (w.foldl (fun b γ => δ b (some γ)) a)) } ∧
      (∀ u < 2 * w.length + 2, ∀ b,
        ((scanTM 2 0 (scanFold (fun c γ => δ c (some γ))) scanKeep a).runFrom d u).state ≠
          some (.done b)) ∧
      (∀ j u, u ≤ 2 * w.length + 2 →
        if j = (0 : Fin 2) then
          ((scanTM 2 0 (scanFold (fun c γ => δ c (some γ))) scanKeep a).runFrom d u).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((scanTM 2 0 (scanFold (fun c γ => δ c (some γ))) scanKeep a).runFrom d u).workTapePos j =
          d.workTapePos j) := by
  obtain ⟨hr, hcut, hspace⟩ := scanTM_run_ofCfg (0 : Fin 2)
    (scanFold (fun b γ => δ b (some γ))) scanKeep a w d hd hw
  refine ⟨?_, hcut, hspace⟩
  rw [scanResult_fold] at hr
  rw [hr]
  apply Cfg.ext <;> try rfl
  funext j q
  dsimp only
  split_ifs with h
  · obtain ⟨rfl, hlo, hhi⟩ := h
    have hf := hw (q - d.workTapePos 0) (by omega) (by omega)
    convert hf.symm using 1
    congr 1
    omega
  · rfl

/-- The fold over a nonfinal field includes its separator exactly once. -/
private theorem rt_find_fold_cons {Γ A : Type} (δ : A → Option Γ → A)
    (a : A) (u v : List Γ) (fs : List (List Γ)) :
    (joinFields (u :: v :: fs)).foldl δ a =
      (joinFields (v :: fs)).foldl δ (δ (u.foldl (fun b γ => δ b (some γ)) a) none) := by
  simp only [joinFields_cons_cons, List.foldl_append, List.foldl_cons, List.foldl_map]

/-- An entry-cell test takes one silent stationary step and one host dispatch.
The frame is arbitrary, so the lemma applies both at an entry and at the end.

**Proof sketch.** The one-cell test records `isSome` without moving a head.
The public phase-host contract redirects that observation at its first exit. -/
private theorem rt_find_read {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool)
    {x : List Γ} (d : Cfg 2 Γ (Option Bool) x) (hd : d.state = some none) :
    (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.read : rt_findPhase m A))) 1 =
      d.mapState (fun _ => ⟨.read, some (d.workTapes 0 (d.workTapePos 0)).isSome⟩) ∧
    (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.read : rt_findPhase m A))) 2 =
      d.mapState (fun _ => if (d.workTapes 0 (d.workTapePos 0)).isSome then
        ⟨.scan ⟨0, hm⟩, .fwd a₀⟩ else ⟨.exit, ()⟩) := by
  let b := (d.workTapes 0 (d.workTapePos 0)).isSome
  let z : Cfg 2 Γ (Option Bool) x := { d with state := some (some b) }
  have hz : (rt_findParts (m := m) δ a₀ .read).runFrom d 1 = z := by
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    rw [step_of_inputMoveAction _ d 0 hd (by rfl)]
    simp only [z, moveInputPos_zero]
    rfl
  have hdispatch : rt_findRedirect hm δ a₀ acc .read (some b) =
      some (if b then ⟨.scan ⟨0, hm⟩, .fwd a₀⟩ else ⟨.exit, ()⟩) := by
    cases b <;> rfl
  have hg : ∀ u < 1, ∀ s, ((rt_findParts (m := m) δ a₀ .read).runFrom d u).state = some s →
      rt_findRedirect hm δ a₀ acc .read s = none := by
    intro u hu s hs
    have hu0 : u = 0 := by omega
    subst u
    simp only [MultiTapeTM.runFrom_zero, hd, Option.some.injEq] at hs
    subst s
    rfl
  obtain ⟨hp, h⟩ := phaseHostTM_run (rt_findParts (m := m) δ a₀) ⟨.read, none⟩
    (rt_findRedirect hm δ a₀ acc) .read d z 1 hz (some b) rfl _ hdispatch hg
  refine ⟨?_, ?_⟩
  · rw [show (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.read : rt_findPhase m A))) 1 =
        ((rt_findParts (m := m) δ a₀ .read).runFrom d 1).mapState (Sigma.mk (.read : rt_findPhase m A)) from hp 1 le_rfl, hz]
    apply Cfg.ext <;> simp [z, b, Cfg.mapState, hd]
  ·
    change (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.read : rt_findPhase m A))) 2 = _ at h
    rw [h]
    apply Cfg.ext <;> simp [z, b, Cfg.mapState, hd]

/-- A field fold in the search host follows the catalog scan through its first
exit and then dispatches once, carrying the computed accumulator.

**Proof sketch.** The preceding read-only fold lemma supplies the endpoint and
the no-`done` cut. Instantiate the public phase-host contract at the scan phase;
all possible redirects of that phase are `done` states. -/
private theorem rt_find_scan_phase {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool) (j : Fin m)
    {x : List Γ} (a : A) (w : List Γ) (d : Cfg 2 Γ (ScanPhase A) x)
    (hd : d.state = some (.fwd a))
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape w p)
    (q : Σ p : rt_findPhase m A, rt_findControl p)
    (hq : rt_findRedirect hm δ a₀ acc (.scan j)
      (.done (w.foldl (fun b γ => δ b (some γ)) a)) = some q) :
    (∀ u ≤ 2 * w.length + 2,
      (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A))) u =
        ((scanTM 2 0 (scanFold (fun b γ => δ b (some γ))) scanKeep a).runFrom d u).mapState
          (Sigma.mk (.scan j : rt_findPhase m A))) ∧
    (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A)))
        (2 * w.length + 3) = d.mapState (fun _ => q) := by
  obtain ⟨hr, hc, _⟩ := rt_find_scan δ a w d hd hw
  have hguard : ∀ u < 2 * w.length + 2, ∀ s,
      ((rt_findParts (m := m) δ a₀ (.scan j)).runFrom d u).state = some s →
        rt_findRedirect hm δ a₀ acc (.scan j) s = none := by
    intro u hu s hs
    cases s with
    | fwd b => rfl
    | bwd b => rfl
    | done b => exact (hc u hu b hs).elim
  obtain ⟨hp, he⟩ := phaseHostTM_run (rt_findParts (m := m) δ a₀) ⟨.read, none⟩
    (rt_findRedirect hm δ a₀ acc) (.scan j) d
    { d with state := some (.done (w.foldl (fun b γ => δ b (some γ)) a)) }
    (2 * w.length + 2) hr _ rfl q hq hguard
  refine ⟨hp, ?_⟩
  change (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A)))
    (2 * w.length + 3) = _ at he
  rw [he]
  apply Cfg.ext <;> simp [Cfg.mapState, hd]

/-- A rejected or nonfinal field's skip in the search host reaches the next
field start and then dispatches once, without changing any tape.

**Proof sketch.** Apply the public skip contract and its first-return cut to
the public phase-host contract. The only redirect is its `done` anchor. -/
private theorem rt_find_skip_phase {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool) (j : Fin m) (a : A)
    {x : List Γ} (w : List Γ) (d : Cfg 2 Γ SeekPhase x)
    (hd : d.state = some .run)
    (hw : ∀ p : ℤ, 0 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape w p)
    (q : Σ p : rt_findPhase m A, rt_findControl p)
    (hq : rt_findRedirect hm δ a₀ acc (.skip j a) .done = some q) :
    (∀ u ≤ w.length + 1,
      (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.skip j a : rt_findPhase m A))) u =
        ((skipTM 2 0).runFrom d u).mapState (Sigma.mk (.skip j a : rt_findPhase m A))) ∧
    (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.skip j a : rt_findPhase m A)))
        (w.length + 2) =
      ({ d with
          workTapePos := Function.update d.workTapePos 0
            (d.workTapePos 0 + w.length + 1) } : Cfg 2 Γ SeekPhase x).mapState (fun _ => q) := by
  obtain ⟨hr, hc, _⟩ := skipTM_run_ofCfg (0 : Fin 2) w d hd hw
  have hguard : ∀ u < w.length + 1, ∀ s,
      ((rt_findParts (m := m) δ a₀ (.skip j a)).runFrom d u).state = some s →
        rt_findRedirect hm δ a₀ acc (.skip j a) s = none := by
    intro u hu s hs
    cases s <;> try rfl
    exact (hc u hu hs).elim
  obtain ⟨hp, he⟩ := phaseHostTM_run (rt_findParts (m := m) δ a₀) ⟨.read, none⟩
    (rt_findRedirect hm δ a₀ acc) (.skip j a) d _ (w.length + 1)
    hr .done rfl q hq hguard
  refine ⟨hp, ?_⟩
  change (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.skip j a : rt_findPhase m A)))
    (w.length + 2) = _ at he
  rw [he]
  apply Cfg.ext <;> simp [Cfg.mapState, hd]

/-- An accepted last field exits before its skip, at the field's original
head. This is the executable correction required by the statement audit.

**Proof sketch.** The field scan computes the fold and restores its head; its
single dispatch goes directly to the escape phase. Until that dispatch every
state remains tagged as a scan, and the public scan radius bounds every head. -/
private theorem rt_find_last_accept {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool) (j : Fin m)
    (hj : j.val + 1 = m) {x : List Γ} (a : A) (w : List Γ)
    (ha : acc (w.foldl (fun b γ => δ b (some γ)) a) = true)
    (d : Cfg 2 Γ (ScanPhase A) x) (hd : d.state = some (.fwd a))
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape w p) :
    (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A)))
        (2 * w.length + 3) = d.mapState (fun _ => ⟨.exit, ()⟩) ∧
    (∀ u < 2 * w.length + 3, ∃ s,
      ((rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A))) u).state = some s ∧
        s ≠ ⟨.read, none⟩ ∧ s ≠ ⟨.exit, ()⟩) ∧
    (∀ u ≤ 2 * w.length + 3, ∀ i : Fin 2,
      if i = 0 then
        ((rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A))) u).workTapePos i ∈
          Finset.Icc (d.workTapePos i - 1) (d.workTapePos i + (w.length : ℤ))
      else ((rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A))) u).workTapePos i =
        d.workTapePos i) := by
  obtain ⟨hp, he⟩ := rt_find_scan_phase hm δ a₀ acc j a w d hd hw ⟨.exit, ()⟩
    (by simp [rt_findRedirect, hj, ha])
  obtain ⟨hs, _, hb⟩ := rt_find_scan δ a w d hd hw
  refine ⟨he, ?_, ?_⟩
  · intro u hu
    rw [hp u (by omega)]
    have hl := MultiTapeTM.runFrom_state_ne_none_of_le
      (scanTM 2 0 (scanFold (fun b γ => δ b (some γ))) scanKeep a) d
      (2 * w.length + 2) (by rw [hs]; simp) u (by omega)
    cases hst : ((scanTM 2 0 (scanFold (fun b γ => δ b (some γ))) scanKeep a).runFrom d u).state with
    | none => exact (hl hst).elim
    | some s =>
      refine ⟨⟨.scan j, s⟩, ?_, ?_, ?_⟩
      · simp [Cfg.mapState, hst]
      · intro h
        have hidx := congrArg Sigma.fst h
        cases hidx
      · intro h
        have hidx := congrArg Sigma.fst h
        cases hidx
  · intro u hu i
    by_cases hle : u ≤ 2 * w.length + 2
    · rw [hp u hle]
      exact hb i u hle
    · have hu' : u = 2 * w.length + 3 := by omega
      subst u
      rw [he]
      simp only [Cfg.mapState]
      split_ifs
      simp

/-- A fold followed by its skip crosses exactly one field and one separator.
Both a nonfinal field and a rejected final field use this same segment.

**Proof sketch.** Compose the scan's first-exit dispatch with the skip's
first-exit dispatch using addition of run times. Before the final dispatch
the host's phase tag is either `scan` or `skip`, excluding both round anchors. -/
private theorem rt_find_advance {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool) (j : Fin m)
    {x : List Γ} (a b : A) (w : List Γ) (d : Cfg 2 Γ (ScanPhase A) x)
    (hd : d.state = some (.fwd a))
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape w p)
    (hscan : rt_findRedirect hm δ a₀ acc (.scan j)
      (.done (w.foldl (fun c γ => δ c (some γ)) a)) = some ⟨.skip j b, .run⟩)
    (q : Σ p : rt_findPhase m A, rt_findControl p)
    (hskip : rt_findRedirect hm δ a₀ acc (.skip j b) .done = some q) :
    (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A)))
        (3 * w.length + 5) =
      ({ d with
          workTapePos := Function.update d.workTapePos 0
            (d.workTapePos 0 + w.length + 1) } : Cfg 2 Γ (ScanPhase A) x).mapState (fun _ => q) ∧
    (∀ u < 3 * w.length + 5,
      ((rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A))) u).state ≠
          some ⟨.read, none⟩ ∧
      ((rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A))) u).state ≠
          some ⟨.exit, ()⟩) := by
  obtain ⟨hpre, hr⟩ := rt_find_scan_phase hm δ a₀ acc j a w d hd hw
    ⟨.skip j b, .run⟩ hscan
  let c : Cfg 2 Γ SeekPhase x := d.mapState (fun _ => .run)
  have hc : c.state = some .run := by simp [c, Cfg.mapState, hd]
  have hcword : ∀ p : ℤ, 0 ≤ p → p ≤ (w.length : ℤ) →
      c.workTapes 0 (c.workTapePos 0 + p) = FinTM.bufferTape w p :=
    fun p hp hp' => hw p (by omega) hp'
  have hstart : d.mapState (fun _ => (⟨.skip j b, SeekPhase.run⟩ : Σ p : rt_findPhase m A, rt_findControl p)) =
      c.mapState (Sigma.mk (.skip j b : rt_findPhase m A)) := by
    apply Cfg.ext <;> simp [c, Cfg.mapState, hd]
  obtain ⟨hpre', hr'⟩ := rt_find_skip_phase hm δ a₀ acc j b w c hc hcword q hskip
  refine ⟨?_, ?_⟩
  · rw [show 3 * w.length + 5 = (2 * w.length + 3) + (w.length + 2) by omega,
      MultiTapeTM.runFrom_add, hr, hstart, hr']
    apply Cfg.ext <;> simp [c, Cfg.mapState, hd]
  · intro u hu
    by_cases hfront : u < 2 * w.length + 3
    · rw [hpre u (by omega)]
      cases hs : ((scanTM 2 0 (scanFold (fun c γ => δ c (some γ))) scanKeep a).runFrom d u).state <;>
        simp [Cfg.mapState, hs]
    · have hsplit : u = (2 * w.length + 3) + (u - (2 * w.length + 3)) := by omega
      rw [hsplit, MultiTapeTM.runFrom_add, hr, hstart, hpre' _ (by omega)]
      cases hs : ((skipTM 2 0).runFrom c (u - (2 * w.length + 3))).state <;>
        simp [Cfg.mapState, hs]

/-- Starting in field `j`, the search round folds every remaining field, then
escapes on acceptance at the start of the final field or returns to its entry
at the next entry offset on rejection. The run costs at most five times the
remaining layout length plus one.

**Proof sketch.** Induct on the remaining field list. A nonfinal field uses
the common scan-and-skip segment, adding its separator to the accumulator;
the public shifted-layout lemma supplies the tail frame. The final field
uses the accepted exit or the same scan-and-skip segment. Every segment
intercepts the public row's first exit. -/
private theorem rt_find_fields_run {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool)
    (fs : List (List Γ)) (j : Fin m) (hn : j.val + fs.length = m)
    {x : List Γ} (a : A) (d : Cfg 2 Γ (ScanPhase A) x)
    (hd : d.state = some (.fwd a))
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ ((joinFields fs).length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = fieldsTape fs p) :
    ∃ t ≤ 5 * ((joinFields fs).length + 1),
      (∀ u < t,
        ((rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A))) u).state ≠
            some ⟨.read, none⟩ ∧
        ((rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A))) u).state ≠
            some ⟨.exit, ()⟩) ∧
      (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A))) t =
        ({ d with
            workTapePos := Function.update d.workTapePos 0
              (d.workTapePos 0 + fieldOffset fs
                (if acc ((joinFields fs).foldl δ a) then fs.length - 1 else fs.length)) } :
          Cfg 2 Γ (ScanPhase A) x).mapState (fun _ =>
            if acc ((joinFields fs).foldl δ a) then ⟨.exit, ()⟩ else ⟨.read, none⟩) := by
  induction fs generalizing j a d with
  | nil => simp only [List.length_nil, Nat.add_zero] at hn; omega
  | cons w ws ih =>
    have hspan : w.length ≤ (joinFields (w :: ws)).length := by
      simpa [fieldOffset] using fieldOffset_add_length_le (w :: ws) 0 (by simp)
    have hword (p : ℤ) (hp : -1 ≤ p) (hp' : p ≤ (w.length : ℤ)) :
        d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape w p := by
      rw [hw p hp (by omega)]
      simpa [fieldOffset] using fieldsTape_field (w :: ws) 0 (by simp) p hp hp'
    cases ws with
    | nil =>
      have hj : j.val + 1 = m := by simpa using hn
      have hlen : (joinFields [w]).length = w.length := by simp [joinFields, List.intercalate]
      have hfold : (joinFields [w]).foldl δ a = w.foldl (fun b γ => δ b (some γ)) a := by
        simp [joinFields, List.intercalate, List.foldl_map]
      cases ha : acc (w.foldl (fun b γ => δ b (some γ)) a) with
      | true =>
        obtain ⟨hr, hc, _⟩ := rt_find_last_accept hm δ a₀ acc j hj a w ha d hd hword
        refine ⟨2 * w.length + 3, by omega, ?_, ?_⟩
        · intro u hu
          obtain ⟨s, hs, hsr, hse⟩ := hc u hu
          exact ⟨fun h => hsr (Option.some.inj (hs.symm.trans h)),
            fun h => hse (Option.some.inj (hs.symm.trans h))⟩
        · simpa [hfold, ha, fieldOffset, Cfg.mapState, hd] using hr
      | false =>
        obtain ⟨hr, hc⟩ := rt_find_advance hm δ a₀ acc j a
          (w.foldl (fun b γ => δ b (some γ)) a) w d hd hword
          (by simp [rt_findRedirect, hj, ha]) ⟨.read, none⟩
          (by simp [rt_findRedirect, hj])
        refine ⟨3 * w.length + 5, by omega, hc, ?_⟩
        simpa [hfold, ha, fieldOffset, Nat.cast_add, add_assoc] using hr
    | cons v vs =>
      have hj : j.val + 1 < m := by simp only [List.length_cons] at hn; omega
      let j' : Fin m := ⟨j.val + 1, hj⟩
      let b := δ (w.foldl (fun c γ => δ c (some γ)) a) none
      let c : Cfg 2 Γ (ScanPhase A) x :=
        { d with
          state := some (.fwd b)
          workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + w.length + 1) }
      have hlen : (joinFields (w :: v :: vs)).length =
          w.length + 1 + (joinFields (v :: vs)).length := by
        simp only [joinFields_cons_cons, List.length_append, List.length_map, List.length_cons]
        omega
      have htail (p : ℤ) (hp : -1 ≤ p) (hp' : p ≤ ((joinFields (v :: vs)).length : ℤ)) :
          c.workTapes 0 (c.workTapePos 0 + p) = fieldsTape (v :: vs) p := by
        change d.workTapes 0 (Function.update d.workTapePos 0
          (d.workTapePos 0 + w.length + 1) 0 + p) = _
        rw [Function.update_self]
        have h := (hw ((w.length : ℤ) + 1 + p) (by omega) (by omega)).trans
          (fieldsTape_cons_shift w v vs p hp)
        convert h using 1
        congr 1
        omega
      obtain ⟨hr, hc⟩ := rt_find_advance hm δ a₀ acc j a b w d hd hword
        (by simp [rt_findRedirect, hj, b]) ⟨.scan j', .fwd b⟩
        (by simp [rt_findRedirect, hj, j'])
      have hstart : (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.scan j : rt_findPhase m A)))
          (3 * w.length + 5) = c.mapState (Sigma.mk (.scan j' : rt_findPhase m A)) := by
        rw [hr]
        apply Cfg.ext <;> simp [c, Cfg.mapState, hd]
      obtain ⟨t, ht, hct, hrt⟩ := ih j' (by simp only [j', List.length_cons]; simp only [List.length_cons] at hn; omega)
        b c rfl htail
      refine ⟨(3 * w.length + 5) + t, by omega, ?_, ?_⟩
      · intro u hu
        by_cases hfront : u < 3 * w.length + 5
        · exact hc u hfront
        · rw [show u = (3 * w.length + 5) + (u - (3 * w.length + 5)) by omega,
            MultiTapeTM.runFrom_add, hstart]
          exact hct _ (by omega)
      · rw [MultiTapeTM.runFrom_add, hstart, hrt]
        have hf : (joinFields (w :: v :: vs)).foldl δ a =
            (joinFields (v :: vs)).foldl δ b := rt_find_fold_cons δ a w v vs
        rw [hf]
        apply Cfg.ext
        · simp [c, Cfg.mapState, hd]
        · rfl
        · rfl
        · funext i
          by_cases hi : i = 0
          · subst i
            simp only [Cfg.mapState, Function.update_self, c, List.length_cons]
            split_ifs <;> simp [fieldOffset_cons_succ, Nat.cast_add] <;> omega
          · simp [c, Cfg.mapState, Function.update_of_ne hi]
        · rfl

/-- At the trailing blank, a round takes two stationary steps to escape.
Its only intermediate state is the recorded blank observation. -/
private theorem rt_find_blank {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool)
    {x : List Γ} (d : Cfg 2 Γ (Option Bool) x) (hd : d.state = some none)
    (hb : d.workTapes 0 (d.workTapePos 0) = none) :
    (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.read : rt_findPhase m A))) 2 =
        d.mapState (fun _ => ⟨.exit, ()⟩) ∧
    (∀ u, 0 < u → u < 2 → ∃ s,
      ((rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.read : rt_findPhase m A))) u).state = some s ∧
        s ≠ ⟨.read, none⟩ ∧ s ≠ ⟨.exit, ()⟩) := by
  obtain ⟨hp, hr⟩ := rt_find_read hm δ a₀ acc d hd
  simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hp hr
  refine ⟨hr, ?_⟩
  intro u hu hu'
  have hu1 : u = 1 := by omega
  subst u
  rw [hp]
  refine ⟨⟨.read, some false⟩, ?_, ?_, ?_⟩
  · simp [Cfg.mapState, hd]
  · intro h
    cases h
  · intro h
    have hi := congrArg Sigma.fst h
    cases hi

/-- One nonempty table entry is folded in a positive number of steps, returning
to the round anchor on rejection or taking the common escape on acceptance.
Only the table head and the control can change.

**Proof sketch.** Nonempty fields make the initial cell nonblank. Compose the
two-step observation with the proved field-list segment. Its no-anchor cut,
and the observation's distinct intermediate state, give the round cut;
liveness follows from the public fact that a live endpoint has a live prefix. -/
private theorem rt_find_entry {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool)
    (fs : List (List Γ)) (hfs : fs.length = m) (hne : ∀ w ∈ fs, w ≠ [])
    {x : List Γ} (d : Cfg 2 Γ (Option Bool) x) (hd : d.state = some none)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ ((joinFields fs).length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = fieldsTape fs p) :
    ∃ t, 0 < t ∧ t ≤ 7 * ((joinFields fs).length + 1) ∧
      (∀ u, 0 < u → u < t → ∃ s,
        ((rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.read : rt_findPhase m A))) u).state = some s ∧
          s ≠ ⟨.read, none⟩ ∧ s ≠ ⟨.exit, ()⟩) ∧
      (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.read : rt_findPhase m A))) t =
        ({ d with
            workTapePos := Function.update d.workTapePos 0
              (d.workTapePos 0 + fieldOffset fs
                (if acc ((joinFields fs).foldl δ a₀) then m - 1 else m)) } :
          Cfg 2 Γ (Option Bool) x).mapState (fun _ =>
            if acc ((joinFields fs).foldl δ a₀) then ⟨.exit, ()⟩ else ⟨.read, none⟩) := by
  have hcur : (d.workTapes 0 (d.workTapePos 0)).isSome = true := by
    cases fs with
    | nil => simp at hfs; omega
    | cons w ws =>
      have hn := hne w (by simp)
      cases w with
      | nil => exact (hn rfl).elim
      | cons γ w =>
        have hs := hw 0 (by omega) (by omega)
        rw [add_zero] at hs
        rw [hs]
        have hf := fieldsTape_field ((γ :: w) :: ws) 0 (by simp) 0 (by omega) (by omega)
        simpa [fieldOffset, FinTM.bufferTape] using congrArg Option.isSome hf
  obtain ⟨hp, hr⟩ := rt_find_read hm δ a₀ acc d hd
  simp only [hcur, ↓reduceIte] at hp hr
  let c : Cfg 2 Γ (ScanPhase A) x := d.mapState (fun _ => .fwd a₀)
  have hc : c.state = some (.fwd a₀) := by simp [c, Cfg.mapState, hd]
  let j : Fin m := ⟨0, hm⟩
  have hstart : d.mapState (fun _ => (⟨.scan j, ScanPhase.fwd a₀⟩ : Σ p : rt_findPhase m A, rt_findControl p)) =
      c.mapState (Sigma.mk (.scan j : rt_findPhase m A)) := by
    apply Cfg.ext <;> simp [c, Cfg.mapState, hd]
  obtain ⟨t, ht, hcut, hrun⟩ := rt_find_fields_run hm δ a₀ acc fs j
    (by simpa [j] using hfs) a₀ c hc hw
  have hend : (rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.read : rt_findPhase m A))) (2 + t) =
      ({ d with
          workTapePos := Function.update d.workTapePos 0
            (d.workTapePos 0 + fieldOffset fs
              (if acc ((joinFields fs).foldl δ a₀) then m - 1 else m)) } :
        Cfg 2 Γ (Option Bool) x).mapState (fun _ =>
          if acc ((joinFields fs).foldl δ a₀) then ⟨.exit, ()⟩ else ⟨.read, none⟩) := by
    rw [MultiTapeTM.runFrom_add, hr, hstart, hrun]
    apply Cfg.ext <;> simp [c, Cfg.mapState, hd, hfs]
  refine ⟨2 + t, by omega, by omega, ?_, hend⟩
  intro u hu hut
  have hl := MultiTapeTM.runFrom_state_ne_none_of_le (rt_findRound hm δ a₀ acc)
    (d.mapState (Sigma.mk (.read : rt_findPhase m A))) (2 + t) (by rw [hend]; simp [Cfg.mapState, hd]) u (by omega)
  have havoid : ((rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.read : rt_findPhase m A))) u).state ≠
        some ⟨.read, none⟩ ∧
      ((rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.read : rt_findPhase m A))) u).state ≠
        some ⟨.exit, ()⟩ := by
    by_cases hu1 : u = 1
    · rw [hu1, hp]
      simp [Cfg.mapState, hd]
    · rw [show u = 2 + (u - 2) by omega, MultiTapeTM.runFrom_add, hr, hstart]
      exact hcut _ (by omega)
  cases hs : ((rt_findRound hm δ a₀ acc).runFrom (d.mapState (Sigma.mk (.read : rt_findPhase m A))) u).state with
  | none => exact (hl hs).elim
  | some s =>
    refine ⟨s, rfl, ?_, ?_⟩
    · intro h; exact havoid.1 (hs.trans (congrArg some h))
    · intro h; exact havoid.2 (hs.trans (congrArg some h))

/-- A proof-only clock for the public counter-loop orbit: the first positive
return to the round entry or escape. It is not used by the transition table. -/
private noncomputable def rt_findClock {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool)
    {x : List Γ} (d : Cfg 2 Γ (Σ p : rt_findPhase m A, rt_findControl p) x) : ℕ := by
  classical
  exact if h : ∃ t, 0 < t ∧
      (((rt_findRound hm δ a₀ acc).runFrom d t).state = some ⟨.read, none⟩ ∨
        ((rt_findRound hm δ a₀ acc).runFrom d t).state = some ⟨.exit, ()⟩)
  then Nat.find h else 1

/-- A positive round with no earlier anchor has exactly the proof clock's
duration. The equation follows from the least-witness characterization. -/
private theorem rt_findClock_eq {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool)
    {x : List Γ} (d : Cfg 2 Γ (Σ p : rt_findPhase m A, rt_findControl p) x)
    (t : ℕ) (ht : 0 < t)
    (he : ((rt_findRound hm δ a₀ acc).runFrom d t).state = some ⟨.read, none⟩ ∨
      ((rt_findRound hm δ a₀ acc).runFrom d t).state = some ⟨.exit, ()⟩)
    (hc : ∀ u, 0 < u → u < t →
      ((rt_findRound hm δ a₀ acc).runFrom d u).state ≠ some ⟨.read, none⟩ ∧
        ((rt_findRound hm δ a₀ acc).runFrom d u).state ≠ some ⟨.exit, ()⟩) :
    rt_findClock hm δ a₀ acc d = t := by
  classical
  unfold rt_findClock
  rw [dif_pos ⟨t, ht, he⟩]
  apply (Nat.find_eq_iff _).mpr
  refine ⟨⟨ht, he⟩, ?_⟩
  intro u hu h
  exact h.2.elim (hc u h.1 hu).1 (hc u h.1 hu).2

/-- The entry-round contract at its proof clock, on the actual hosted state
type. This is the form consumed by the public counter-loop orbit.

**Proof sketch.** Forget only the entry's control tag, apply the proved raw
entry contract, and restore the tag. The no-anchor cut identifies that finite
time with the first-positive-anchor clock. No transition depends on the clock. -/
private theorem rt_find_round_entry {Γ A : Type} {m : ℕ} (hm : 0 < m)
    (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool)
    (fs : List (List Γ)) (hfs : fs.length = m) (hne : ∀ w ∈ fs, w ≠ [])
    {x : List Γ} (c : Cfg 2 Γ (Σ p : rt_findPhase m A, rt_findControl p) x)
    (hc : c.state = some ⟨.read, none⟩)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ ((joinFields fs).length : ℤ) →
      c.workTapes 0 (c.workTapePos 0 + p) = fieldsTape fs p) :
    let t := rt_findClock hm δ a₀ acc c
    0 < t ∧ t ≤ 7 * ((joinFields fs).length + 1) ∧
      (∀ u, 0 < u → u < t → ∃ s,
        ((rt_findRound hm δ a₀ acc).runFrom c u).state = some s ∧
          s ≠ ⟨.read, none⟩ ∧ s ≠ ⟨.exit, ()⟩) ∧
      (rt_findRound hm δ a₀ acc).runFrom c t =
        { c with
          state := some (if acc ((joinFields fs).foldl δ a₀) then ⟨.exit, ()⟩ else ⟨.read, none⟩)
          workTapePos := Function.update c.workTapePos 0
            (c.workTapePos 0 + fieldOffset fs
              (if acc ((joinFields fs).foldl δ a₀) then m - 1 else m)) } := by
  let d : Cfg 2 Γ (Option Bool) x := c.mapState (fun _ => none)
  have hd : d.state = some none := by simp [d, Cfg.mapState, hc]
  have hstart : d.mapState (Sigma.mk (.read : rt_findPhase m A)) = c := by
    apply Cfg.ext <;> simp [d, Cfg.mapState, hc]
  obtain ⟨t, ht, hb, hg, hr⟩ := rt_find_entry hm δ a₀ acc fs hfs hne d hd hw
  rw [hstart] at hg hr
  have he : (rt_findRound hm δ a₀ acc).runFrom c t =
      { c with
        state := some (if acc ((joinFields fs).foldl δ a₀) then ⟨.exit, ()⟩ else ⟨.read, none⟩)
        workTapePos := Function.update c.workTapePos 0
          (c.workTapePos 0 + fieldOffset fs
            (if acc ((joinFields fs).foldl δ a₀) then m - 1 else m)) } := by
    rw [hr]
    apply Cfg.ext <;> simp [d, Cfg.mapState, hc]
  have hend : ((rt_findRound hm δ a₀ acc).runFrom c t).state = some ⟨.read, none⟩ ∨
      ((rt_findRound hm δ a₀ acc).runFrom c t).state = some ⟨.exit, ()⟩ := by
    rw [he]
    cases acc ((joinFields fs).foldl δ a₀) <;> simp
  have hclock := rt_findClock_eq hm δ a₀ acc c t ht hend (by
    intro u hu hut
    obtain ⟨s, hst, hsa, hse⟩ := hg u hu hut
    exact ⟨fun h => hsa (Option.some.inj (hst.symm.trans h)),
      fun h => hse (Option.some.inj (hst.symm.trans h))⟩)
  dsimp only
  rw [hclock]
  exact ⟨ht, hb, hg, he⟩

/-- **Table find** (design §12.8a §3, §12.8b). For a digit embedding `e`, a
field count `m > 0` and a finite-state fold `δ` from `a₀` with acceptance
`acc`, there is a module with an entry, two distinct verdict anchors and
`K + 2` tapes with the following contract. An entry `en` of a table is
*accepted* when `acc` holds of the fold of `δ` over its layout
`Turing.joinFields en`, blanks included. Start the module at its entry with a
well-formed table of `m`-field entries at `o` on tape `0` and its head at `o`;
on tape `1` a delimited fuel word `w` of digits `e b` whose value exceeds the
number of entries; and the other tapes blank. It reaches a verdict within `C`
times the table's layout length plus `|w| + 1`, and no verdict earlier. If some
entry is accepted, the verdict is `yes` with the head of tape `0` at the first
accepted entry's offset; otherwise it is `no` with the head back at `o`.
Nothing is written: the table, the fuel, the scratch, every other head, the
input position and the output are as they were. Up to the verdict every work
head stays within that many cells of its entry position. The empty table
answers `no`. With `δ` reading the flag field, it finds the first unprocessed
record of the breadth-first table; with `δ` reading the state and tag fields,
an accepting record. The fuel bounds the loop; a host keeps one fuel word,
since the module restores it.

**Proof sketch.** Copy the fuel to a scratch counter (`Turing.copyTM_run_ofCfg`)
and cross the header (`Turing.skipTM_run_ofCfg`). Then loop over the entries
under `Turing.counterLoopTMVia e` (R8.0b), one entry per round, escaping at the
end of the table or at an accepted entry; the fuel's value exceeds the number
of rounds run, so the counter never runs out. A round tests the cell at the
current entry's offset: a blank is the second trailing blank, the end of the
table (no field is empty, by `Turing.TableWF.field_ne_nil`). Otherwise it runs
the fold over the entry's `m` fields, one `Turing.scanTM` fold per field from
the state the previous field left (`Turing.scanTM_run_ofCfg` with
`Turing.scanResult_fold` at `δ · (some ·)`), the separator step `δ a none`
between consecutive fields, and `Turing.skipTM` after each of the first `m - 1`
fields, all by R2 seams with the fold state and a field counter in finite
control. After the last field's fold, test `acc`: on acceptance escape **before**
skipping that field, so the head is still on its nonblank cells; otherwise skip
it and continue. A stationary read after the escape then tells the two exits
apart, a nonblank cell meaning acceptance and the trailing blank the end of the
table. On acceptance, return over the `m - 1` crossed fields and to the start
of the current one by `Turing.skipBackTM_run_ofCfg`, and answer `yes`; at the
end, return by `Turing.tableRewindTM_run_ofCfg` and answer `no`. (Round 1 of
the wave-1 statement gate, finding 3: skipping the accepted final field would
leave the head on the end-of-table blank. Take `m = 1`, `h = [true]`,
`es = [[[true]]]` and an accepting fold: the entry starts at offset 2, and the
skip would leave the head at offset 4, a blank, although `findIdx?` gives
`some 0`. An explicit verdict bit carried across the escape is an equivalent
alternative.) Clear
the scratch counter. The rounds cost a constant times the entries' layouts, and
the decrements at most `4r + 2|w|` for `r` rounds
(`Turing.counterOverhead_le_of_le`). The value `m > 0` is necessary: with empty
entries, the tables `[]` and `[[]]` lay out identically and the verdict would
have to differ.

**Universe (maintainer fix, 2026-10-12; flagged).** The alphabet is `Γ : Type`, not `Type*`.
The mandated loop `Turing.counterLoopTMVia` and the phase host `Turing.phaseHostTM` take their
alphabet in `Type`, so the route could not be instantiated at an arbitrary universe (the record
tables continuation's escalation). Every consumer's alphabet, `RecSym Q T`, lies in `Type`.
Generalizing the two hosts instead is the optional backlog item UNIV-1.

**Fill appendix (continuation 2, partial; flagged).** The finite round is now
`rt_findRound`, using the public phase host to compose catalog fold scans and
skips. Its proved entry contract folds exactly `joinFields fs`, costs at most
`7 * ((joinFields fs).length + 1)`, preserves every tape, and supplies the
positive first-return/escape cut. Acceptance exits at the start of the final
field, before its skip; rejection advances to the next entry. A blank entry
cell escapes in two stationary steps. `rt_findClock` and
`rt_find_round_entry` put this contract in the proof-clock form required by
`counterLoopOrbit`; the clock is absent from the executable transition table.
The full row remains admitted: its table-index orbit proof, application of
`counterLoopTMVia`, fuel copy/clearing, verdict test, and return phases still
need to be composed. The six public admissions have not moved into helpers. -/
theorem exists_tableFindTM {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) (m : ℕ) (hm : 0 < m)
    {A : Type} [Fintype A] [DecidableEq A] (δ : A → Option Γ → A) (a₀ : A) (acc : A → Bool) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P) (R : MultiTapeTM (K + 2) Γ P)
      (entry yes no : P) (C : ℕ), yes ≠ no ∧
      ∀ {y : List Γ} (o : ℤ) (h : List Γ) (es : List (List (List Γ))) (w : List Bool),
        TableWF m h es → es.length < Nat.ofDigits 2 (w.map Bool.toNat) →
      ∀ d : Cfg (K + 2) Γ P y, d.state = some entry → d.workTapePos 0 = o →
        TableAt d 0 o h es →
        (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = FinTM.bufferTape (w.map e) p) →
        (∀ j : Fin (K + 2), 2 ≤ j.val → ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * ((joinFields (tableFields h es)).length + w.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no) ∧
          (∀ u ≤ t, ∀ j : Fin (K + 2),
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((joinFields (tableFields h es)).length + w.length + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            match es.findIdx? (fun en => acc ((joinFields en).foldl δ a₀)) with
            | some j =>
              { d with
                state := some yes
                workTapePos := Function.update d.workTapePos 0 (o + tableOffset h es j) }
            | none => { d with state := some no } := by
  sorry

/-- Transport field-list copy to the reverse pair of tapes for table append.

**Proof sketch.** Select the source bank by the transposition of tapes zero
and one. R1 transports the already-proved copier's run at every time; its
selected-tape laws transfer the frame and head bound. No second copier or
copy trace is defined. -/
private theorem rt_fieldsCopy_reverse {Γ : Type*} (m : ℕ) :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (R : MultiTapeTM 2 Γ P) (entry exit : P)
      (C : ℕ),
      ∀ {x : List Γ} (fs : List (List Γ)), fs.length = m →
      ∀ d : Cfg 2 Γ P x, d.state = some entry → RecordAt d 1 fs →
        (∀ p : ℤ, -1 ≤ p → p ≤ ((joinFields fs).length : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + p) = none) →
        ∃ t ≤ C * ((joinFields fs).length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j : Fin 2,
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((joinFields fs).length + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with state := some exit
                     workTapes := fun j q =>
                       if j = 0 ∧ d.workTapePos j ≤ q ∧
                           q < d.workTapePos j + ((joinFields fs).length : ℤ)
                       then fieldsTape fs (q - d.workTapePos j)
                       else d.workTapes j q } := by
  classical
  obtain ⟨P, hfin, heq, R, entry, exit, C, hR⟩ := exists_fieldsCopyTM (Γ := Γ) m
  letI := hfin
  letI := heq
  let ι := (Equiv.swap (0 : Fin 2) 1).toEmbedding
  have hswap (j : Fin 2) : ι (ι j) = j := Equiv.swap_apply_self 0 1 j
  have hz : ι 0 = 1 := Equiv.swap_apply_left 0 1
  have ho : ι 1 = 0 := Equiv.swap_apply_right 0 1
  refine ⟨P, hfin, heq, embedEmitTM ι R, entry, exit, C, ?_⟩
  intro x fs hfs d hd hsrc hblank
  let c : Cfg 2 Γ P x :=
    { d with workTapes := fun j => d.workTapes (ι j)
             workTapePos := fun j => d.workTapePos (ι j) }
  have hstart : embedEmitCfg ι d.workTapes d.workTapePos [] c = d := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      rw [← hswap j, embedEmitCfg_selected_tape]
    · funext j
      rw [← hswap j, embedEmitCfg_selected_pos]
    · exact List.nil_append _
  have hcsrc : RecordAt c 0 fs := by simpa only [RecordAt, c, hz] using hsrc
  have hcblank (p : ℤ) (hp : -1 ≤ p) (hp' : p ≤ ((joinFields fs).length : ℤ)) :
      c.workTapes 1 (c.workTapePos 1 + p) = none := by
    simpa only [c, ho] using hblank p hp hp'
  obtain ⟨t, ht, hcut, hrad, hrun⟩ := hR fs hfs c hd hcsrc hcblank
  have htransfer (v : ℕ) : (embedEmitTM ι R).runFrom d v =
      embedEmitCfg ι d.workTapes d.workTapePos [] (R.runFrom c v) := by
    simpa only [hstart] using embedEmitTM_runFrom ι R d.workTapes d.workTapePos [] c v
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · intro v hv
    rw [htransfer]
    exact hcut v hv
  · intro v hv j
    rw [htransfer, ← hswap j, embedEmitCfg_selected_pos]
    have hh := hrad v hv (ι j)
    simpa only [c, hswap] using hh
  · rw [htransfer, hrun]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j q
      rw [← hswap j, embedEmitCfg_selected_tape]
      change (if ι j = 1 ∧ d.workTapePos (ι (ι j)) ≤ q ∧
          q < d.workTapePos (ι (ι j)) + ((joinFields fs).length : ℤ)
        then fieldsTape fs (q - d.workTapePos (ι (ι j)))
        else d.workTapes (ι (ι j)) q) = _
      simp only [hswap]
      have hj : ι j = 1 ↔ j = 0 := by
        rw [← hz]
        exact ι.injective.eq_iff
      simp only [hj]
    · funext j
      rw [← hswap j, embedEmitCfg_selected_pos]
    · exact List.nil_append _

/-- The seek-and-copy prefix of append. It leaves the destination head at the old
second trailing blank, with the source layout written there and all other data
restored. The suffix writer and the old-table rewind are subsequent phases.

**Proof sketch.** Seek over the old nonempty fields, then invoke the reverse
copier at the second trailing blank. The old table's blank tail supplies the
copier's whole frame, including its left delimiter. R2 combines the contracts;
the new head bound includes the shift by the old table's span. -/
private theorem rt_append_copy {Γ : Type*} (m : ℕ) :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (R : MultiTapeTM 2 Γ P) (entry exit : P)
      (C : ℕ),
      ∀ {x : List Γ} (o : ℤ) (h : List Γ) (es : List (List (List Γ))) (e : List (List Γ)),
        (∀ u ∈ tableFields h es, u ≠ []) → e.length = m →
      ∀ d : Cfg 2 Γ P x, d.state = some entry → d.workTapePos 0 = o → TableAt d 0 o h es →
        (∀ q : ℤ, o + ((joinFields (tableFields h es)).length : ℤ) ≤ q → d.workTapes 0 q = none) →
        RecordAt d 1 e →
        ∃ t ≤ C * ((joinFields (tableFields h es)).length + (joinFields e).length + 1),
          (∀ v < t, (R.runFrom d v).state ≠ some exit) ∧
          (∀ v ≤ t, ∀ j : Fin 2,
            |(R.runFrom d v).workTapePos j - d.workTapePos j| ≤
              ((C * ((joinFields (tableFields h es)).length + (joinFields e).length + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with state := some exit
                     workTapePos := Function.update d.workTapePos 0 (o + tableOffset h es es.length)
                     workTapes := fun j q =>
                       if j = 0 ∧ o + tableOffset h es es.length ≤ q ∧
                           q < o + tableOffset h es es.length + ((joinFields e).length : ℤ)
                       then fieldsTape e (q - (o + tableOffset h es es.length))
                       else d.workTapes j q } := by
  classical
  obtain ⟨P, hfin, heq, R, entry, exit, C, hR⟩ := rt_fieldsCopy_reverse (Γ := Γ) m
  letI := hfin
  letI := heq
  refine ⟨SeekPhase ⊕ P, inferInstance, inferInstance,
    seamCompTM (seekEndTM 2 0) .done R entry, .inl .run, .inr exit, C + 4, ?_⟩
  intro x o h es e hnonempty hlen d hd hpos htable hblank hsource
  let D := fieldOffset (tableFields h es) (tableFields h es).length
  have hD : D = (joinFields (tableFields h es)).length + 1 :=
    fieldOffset_length _ (by simp [tableFields])
  have hoffset : tableOffset h es es.length = D := by
    rw [tableOffset_length, hD]
  let a : Cfg 2 Γ SeekPhase x := d.mapState (fun _ => .run)
  let b : Cfg 2 Γ SeekPhase x :=
    { a with state := some .done
             workTapePos := Function.update a.workTapePos 0 (a.workTapePos 0 + D) }
  have ha : a.state = some .run := by simp [a, Cfg.mapState, hd]
  have hf (p : ℤ) (hp : 0 ≤ p) (hp' : p ≤ (D : ℤ)) :
      a.workTapes 0 (a.workTapePos 0 + p) = fieldsTape (tableFields h es) p := by
    change d.workTapes 0 (d.workTapePos 0 + p) = _
    rw [hpos]
    exact htable p (by omega) (by omega)
  obtain ⟨hs, hsc, hsb⟩ := seekEndTM_run_ofCfg (0 : Fin 2) (tableFields h es)
    (by simp [tableFields]) hnonempty a ha hf
  change (seekEndTM 2 0).runFrom a (D + 1) = b at hs
  let c := b.mapState (fun _ => entry)
  have cp₀ : c.workTapePos 0 = o + D := by
    simp [c, b, a, Cfg.mapState, hpos]
  have cp₁ : c.workTapePos 1 = d.workTapePos 1 := by
    simp [c, b, a, Cfg.mapState]
  have hcsource : RecordAt c 1 e := by
    intro p hp hp'
    change d.workTapes 1 (c.workTapePos 1 + p) = _
    rw [cp₁]
    exact hsource p hp hp'
  have hcblank (p : ℤ) (hp : -1 ≤ p) (_ : p ≤ ((joinFields e).length : ℤ)) :
      c.workTapes 0 (c.workTapePos 0 + p) = none := by
    change d.workTapes 0 (c.workTapePos 0 + p) = _
    rw [cp₀]
    exact hblank _ (by omega)
  obtain ⟨t, ht, hcc, hcb, hcr⟩ := hR e hlen c rfl hcsource hcblank
  let z : Cfg 2 Γ P x :=
    { c with state := some exit
             workTapes := fun j q =>
               if j = 0 ∧ c.workTapePos j ≤ q ∧ q < c.workTapePos j + ((joinFields e).length : ℤ)
               then fieldsTape e (q - c.workTapePos j) else c.workTapes j q }
  change R.runFrom c t = z at hcr
  let B := (C + 4) * ((joinFields (tableFields h es)).length + (joinFields e).length + 1)
  have hbudget : C * ((joinFields e).length + 1) + D + 2 ≤ B := by
    have hh := Nat.mul_le_mul_left C
      (show (joinFields e).length + 1 ≤
        (joinFields (tableFields h es)).length + (joinFields e).length + 1 by omega)
    dsimp only [B]
    rw [Nat.add_mul]
    omega
  have hbudget' : (C * ((joinFields e).length + 1) : ℕ) + (D : ℤ) + 2 ≤ (B : ℤ) := by
    exact_mod_cast hbudget
  have hsb' : ∀ v ≤ D + 1, ∀ j : Fin 2,
      |((seekEndTM 2 0).runFrom a v).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
    intro v hv j
    have hh := hsb j v hv
    change (if j = 0 then
      ((seekEndTM 2 0).runFrom a v).workTapePos j ∈ Finset.Icc (d.workTapePos j)
        (d.workTapePos j + D) else
      ((seekEndTM 2 0).runFrom a v).workTapePos j = d.workTapePos j) at hh
    split_ifs at hh
    · simp only [Finset.mem_Icc] at hh
      rw [abs_le]; constructor <;> omega
    · rw [hh, sub_self, abs_zero]; omega
  have hcb' : ∀ v ≤ t, ∀ j : Fin 2,
      |(R.runFrom c v).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
    intro v hv j
    have hh := abs_le.mp (hcb v hv j)
    fin_cases j
    · change -((C * ((joinFields e).length + 1) : ℕ) : ℤ) ≤
          (R.runFrom c v).workTapePos 0 - c.workTapePos 0 ∧
        (R.runFrom c v).workTapePos 0 - c.workTapePos 0 ≤ _ at hh
      rw [cp₀] at hh
      change |(R.runFrom c v).workTapePos 0 - d.workTapePos 0| ≤ _
      rw [hpos, abs_le]; constructor <;> omega
    · change -((C * ((joinFields e).length + 1) : ℕ) : ℤ) ≤
          (R.runFrom c v).workTapePos 1 - c.workTapePos 1 ∧
        (R.runFrom c v).workTapePos 1 - c.workTapePos 1 ≤ _ at hh
      rw [cp₁] at hh
      change |(R.runFrom c v).workTapePos 1 - d.workTapePos 1| ≤ _
      rw [abs_le]; constructor <;> omega
  obtain ⟨hr, hcut, hrad⟩ := rt_copy_seam (seekEndTM 2 0) .done R entry exit
    d.workTapePos (B : ℤ) hs rfl hsc hsb' hcr rfl hcc hcb'
  have hentry : a.mapState Sum.inl = d := by
    apply Cfg.ext <;> simp [a, Cfg.mapState, hd]
  rw [hentry] at hr hcut hrad
  refine ⟨D + 1 + 1 + t, by omega, hcut, hrad, ?_⟩
  rw [hr]
  apply Cfg.ext
  · rfl
  · rfl
  · funext j q
    change (if j = 0 ∧ c.workTapePos j ≤ q ∧ q < c.workTapePos j + ((joinFields e).length : ℤ)
      then fieldsTape e (q - c.workTapePos j) else d.workTapes j q) = _
    by_cases hj : j = 0
    · subst j; simp only [cp₀, hoffset]
    · simp [hj]
  · simp [z, c, b, a, Cfg.mapState, hpos, hoffset]
  · rfl

/-- **Table append** (design §12.8a §3, §12.8b). For a field count `m` and a
fixed list `suf` of suffix fields, there is a two-tape module with an entry and
an exit state with the following contract. Start it at its entry with a table
at `o` on tape `0` whose fields are all nonempty, its head at `o`, tape `0`
blank from the table's end on, and an `m`-field list `e` laid out at the head
of tape `1`. It reaches its exit within `C` times the two layout lengths plus
one, and not earlier. At that point tape `0` holds the table with the new entry
`e ++ suf` appended, with its head back at `o`, and every other cell, every
other head, the input position and the output are as they were. Up to the exit
every work head stays within that many cells of its entry position. With
`suf := [[digit false]]` it appends a successor record with its
"unprocessed" flag.

**Proof sketch.** `Turing.seekEndTM_run_ofCfg` over the table's field list
moves the head to the second trailing blank, which is the new entry's offset
(`Turing.tableOffset_length`); its left neighbour, the first trailing blank,
becomes the separator. `Turing.exists_fieldsCopyTM` copies `e` there from
tape `1` into the blank region, `Turing.skipTM` crosses the copied fields, and
`Turing.writeConstTM_run_ofCfg` with skips writes the fields of `suf`. Return by
`Turing.skipBackTM_run_ofCfg` over the `m + |suf|` new fields, which reaches the
old second trailing blank whether or not those fields are empty, and then
`Turing.tableRewindTM_run_ofCfg` over the old field list, whose fields are
nonempty; the adapter ignores the cell under its head. The phases join by R2
seams. The new layout extends the old (`Turing.fieldsTape` of the longer list
agrees with the old one on the old layout), so the finish is the old tape with
the new layout written over `[o, o + L')`.

**Fill appendix.** Empty appended fields need not preserve `Turing.TableWF`.
A consumer that subsequently seeks must append nonempty fields. This partial
has not yet filled the append contract. `rt_fieldsCopy_reverse` transports the
proved copier through R1; `rt_append_copy` proves the seek-and-copy prefix, with
its exact tape update and shifted head bound. Writing the fixed suffix and
restoring the table head remain the continuation frontier. -/
theorem exists_tableAppendTM {Γ : Type*} (m : ℕ) (suf : List (List Γ)) :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (R : MultiTapeTM 2 Γ P) (entry exit : P)
      (C : ℕ),
      ∀ {y : List Γ} (o : ℤ) (h : List Γ) (es : List (List (List Γ))) (e : List (List Γ)),
        (∀ u ∈ tableFields h es, u ≠ []) → e.length = m →
      ∀ d : Cfg 2 Γ P y, d.state = some entry → d.workTapePos 0 = o → TableAt d 0 o h es →
        (∀ q : ℤ, o + ((joinFields (tableFields h es)).length : ℤ) ≤ q → d.workTapes 0 q = none) →
        RecordAt d 1 e →
        ∃ t ≤ C * ((joinFields (tableFields h es)).length + (joinFields e).length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j : Fin 2,
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((joinFields (tableFields h es)).length + (joinFields e).length + 1) : ℕ) :
                ℤ)) ∧
          R.runFrom d t =
            { d with
              state := some exit
              workTapes := fun j q =>
                if j = 0 ∧ o ≤ q ∧
                    q < o + ((joinFields (tableFields h (es ++ [e ++ suf]))).length : ℤ)
                  then fieldsTape (tableFields h (es ++ [e ++ suf])) (q - o)
                else d.workTapes j q } := by
  sorry

/-! ### The deferred record rows -/

/-- Fixed-width successor, extending the word by one digit exactly on overflow. -/
private def rt_succWord (w : List Bool) : List Bool :=
  (incFixed w).getD (List.replicate w.length false ++ [true])

/-- A carry through a low one exposes the same operation on the remaining word. -/
private theorem rt_succWord_cons (w : List Bool) :
    rt_succWord (true :: w) = false :: rt_succWord w := by
  unfold rt_succWord
  cases h : incFixed w <;> simp [incFixed, h, List.replicate_succ]

/-- The extension convention gives the canonical binary word of the successor.

**Proof sketch.** Treat zero and one separately, including the one-digit
 overflow. For a positive high part, use the public even and odd bit-word
 equations; only the odd case carries into the smaller high part. -/
private theorem rt_succWord_bits (n : ℕ) : rt_succWord n.bits = (n + 1).bits := by
  induction n using Nat.binaryRecFromOne with
  | zero => simp [rt_succWord, incFixed]
  | one => simp [rt_succWord, incFixed, Nat.bits, Nat.binaryRec]
  | bit b m hm ih =>
    cases b
    · change rt_succWord (2 * m).bits = (2 * m + 1).bits
      rw [Nat.bit0_bits m hm, Nat.bit1_bits]
      rfl
    · change rt_succWord (2 * m + 1).bits = (2 * m + 2).bits
      rw [Nat.bit1_bits, rt_succWord_cons, ih]
      convert (Nat.bit0_bits (m + 1) (by omega)).symm using 1

/-- A successful fixed-width increment preserves the word length. -/
private theorem rt_incFixed_length (w v : List Bool) (h : incFixed w = some v) :
    v.length = w.length := by
  induction w generalizing v with
  | nil => simp [incFixed] at h
  | cons b w ih =>
    cases b
    · simp only [incFixed, Option.some.injEq] at h
      subst v; rfl
    · cases he : incFixed w with
      | none => simp [incFixed, he] at h
      | some z =>
        simp only [incFixed, he, Option.map_some, Option.some.injEq] at h
        subst v
        simp [ih z he]


/-- A three-step boundary extension: from one cell past a delimiter, move left,
write one symbol, and move twice right. No catalog row has this exact local
interface; the unbounded scans around it use the public skip rows. -/
private def rt_boundaryTM {Γ : Type*} (k : ℕ) (i : Fin k) (b : Γ) :
    MultiTapeTM k Γ (Fin 4) where
  q₀ := 0
  tr := fun q _ _ =>
    if q = 0 then tapeAction i 0 none .neg 1
    else if q = 1 then tapeAction i 0 (some (some b)) .pos 2
    else if q = 2 then tapeAction i 0 none .pos 3
    else inputMoveAction 0 3

/-- The boundary extension writes only the cell immediately left of its entry
head, ends one cell to the right, and has a first exit after three steps.

**Proof sketch.** Apply the public one-step move and write equations three
 times. The intermediate configurations give the cut and head interval. -/
private theorem rt_boundary_run {Γ : Type*} {k : ℕ} {x : List Γ}
    (i : Fin k) (b : Γ) (d : Cfg k Γ (Fin 4) x) (hs : d.state = some 0) :
    (rt_boundaryTM k i b).runFrom d 3 =
      {d with
        state := some 3
        workTapes := Function.update d.workTapes i
          (Function.update (d.workTapes i) (d.workTapePos i - 1) (some b))
        workTapePos := Function.update d.workTapePos i (d.workTapePos i + 1)} ∧
    (∀ u < 3, ((rt_boundaryTM k i b).runFrom d u).state ≠ some 3) ∧
    (∀ u ≤ 3, ∀ j : Fin k,
      if j = i then
        ((rt_boundaryTM k i b).runFrom d u).workTapePos j ∈
          Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + 1)
      else ((rt_boundaryTM k i b).runFrom d u).workTapePos j = d.workTapePos j) := by
  let a : Cfg k Γ (Fin 4) x := {d with
    state := some 1
    workTapePos := Function.update d.workTapePos i (d.workTapePos i - 1)}
  let c : Cfg k Γ (Fin 4) x := {d with
    state := some 2
    workTapes := Function.update d.workTapes i
      (Function.update (d.workTapes i) (d.workTapePos i - 1) (some b))}
  have one : (rt_boundaryTM k i b).runFrom d 1 = a := by
    change (rt_boundaryTM k i b).step d = a
    rw [step_of_tapeAction_move (rt_boundaryTM k i b) d (q' := 1) i 0 .neg hs
      (by simp [rt_boundaryTM])]
    simp [a, SignType.cast, sub_eq_add_neg]
  have two : (rt_boundaryTM k i b).runFrom d 2 = c := by
    change (rt_boundaryTM k i b).step ((rt_boundaryTM k i b).runFrom d 1) = c
    rw [one]
    rw [step_of_tapeAction_write (rt_boundaryTM k i b) a (q := 1) (q' := 2) i 0
      (some b) .pos rfl (by simp [rt_boundaryTM])]
    apply Cfg.ext <;> simp [a, c, SignType.cast, Function.update_idem]
  have three : (rt_boundaryTM k i b).runFrom d 3 =
      {d with
        state := some 3
        workTapes := Function.update d.workTapes i
          (Function.update (d.workTapes i) (d.workTapePos i - 1) (some b))
        workTapePos := Function.update d.workTapePos i (d.workTapePos i + 1)} := by
    change (rt_boundaryTM k i b).step ((rt_boundaryTM k i b).runFrom d 2) = _
    rw [two]
    rw [step_of_tapeAction_move (rt_boundaryTM k i b) c (q := 2) (q' := 3) i 0 .pos rfl
      (by simp [rt_boundaryTM])]
    simp [c, SignType.cast]
  refine ⟨three, ?_, ?_⟩
  · intro u hu
    have casesU : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases casesU with rfl | rfl | rfl <;> simp [one, two, a, c, hs]
  · intro u hu j
    have casesU : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by omega
    rcases casesU with rfl | rfl | rfl | rfl <;> by_cases hj : j = i <;>
      simp [one, two, three, a, c, hj, Finset.mem_Icc] <;> omega

/-- Append one symbol to a delimited word and return to its first cell, using
only two public skips and the fixed three-step boundary extension. -/
private def rt_appendSymbolTM {Γ : Type*} (k : ℕ) (i : Fin k) (b : Γ) :
    MultiTapeTM k Γ (SeekPhase ⊕ (Fin 4 ⊕ SeekPhase)) :=
  seamCompTM (skipTM k i) .done
    (seamCompTM (rt_boundaryTM k i b) 3 (skipBackTM k i) .run) (.inl 0)

/-- The append-symbol leaf has linear time and head displacement, restores all
heads, and changes only the old right delimiter.

**Proof sketch.** Skip the old word, replace its delimiter by the new symbol,
and skip back across the extended word. The extra right blank is the new
word's delimiter. The two R2 seams intercept each exit; their certificates
are combined by the inherited `rt_copy_seam`. -/
private theorem rt_appendSymbol_run {Γ : Type*} {k : ℕ} {x : List Γ}
    (i : Fin k) (b : Γ) (w : List Γ)
    (d : Cfg k Γ (SeekPhase ⊕ (Fin 4 ⊕ SeekPhase)) x)
    (hs : d.state = some (.inl .run))
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) + 1 →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (rt_appendSymbolTM k i b).runFrom d (2 * w.length + 10) =
      {d with
        state := some (.inr (.inr .done))
        workTapes := Function.update d.workTapes i
          (Function.update (d.workTapes i) (d.workTapePos i + w.length) (some b))} ∧
    (∀ u < 2 * w.length + 10,
      ((rt_appendSymbolTM k i b).runFrom d u).state ≠ some (.inr (.inr .done))) ∧
    (∀ u ≤ 2 * w.length + 10, ∀ j : Fin k,
      |((rt_appendSymbolTM k i b).runFrom d u).workTapePos j - d.workTapePos j| ≤
        (w.length : ℤ) + 4) := by
  let a : Cfg k Γ SeekPhase x := d.mapState (fun _ => .run)
  have ha : a.state = some .run := by simp [a, Cfg.mapState, hs]
  let a' : Cfg k Γ SeekPhase x := {a with
    state := some .done
    workTapePos := Function.update a.workTapePos i (a.workTapePos i + w.length + 1)}
  obtain ⟨runA, cutA, headsA⟩ := skipTM_run_ofCfg i w a ha
    (fun p lo hi => hw p (by omega) (by omega))
  change (skipTM k i).runFrom a (w.length + 1) = a' at runA
  let c : Cfg k Γ (Fin 4) x := a'.mapState (fun _ => 0)
  let c' : Cfg k Γ (Fin 4) x := {c with
    state := some 3
    workTapes := Function.update c.workTapes i
      (Function.update (c.workTapes i) (c.workTapePos i - 1) (some b))
    workTapePos := Function.update c.workTapePos i (c.workTapePos i + 1)}
  obtain ⟨runC, cutC, headsC⟩ := rt_boundary_run i b c rfl
  change (rt_boundaryTM k i b).runFrom c 3 = c' at runC
  let e : Cfg k Γ SeekPhase x := c'.mapState (fun _ => .run)
  have epos : e.workTapePos i = d.workTapePos i + w.length + 2 := by
    simp [e, c', c, a', a, Cfg.mapState]; omega
  have tapeE : ∀ p : ℤ, -1 ≤ p → p ≤ ((w ++ [b]).length : ℤ) →
      e.workTapes i (d.workTapePos i + p) = FinTM.bufferTape (w ++ [b]) p := by
    intro p lo hi
    have hi' : p ≤ (w.length : ℤ) + 1 := by simpa using hi
    simp only [e, c', Cfg.mapState, Function.update_self]
    change Function.update (d.workTapes i) (c.workTapePos i - 1) (some b)
      (d.workTapePos i + p) = _
    have cp : c.workTapePos i - 1 = d.workTapePos i + w.length := by
      simp [c, a', a, Cfg.mapState]
    rw [cp, FinTM.bufferTape_append]
    by_cases he : p = (w.length : ℤ)
    · subst p; simp
    · rw [Function.update_of_ne (by omega), Function.update_of_ne he]
      exact hw p lo hi'
  obtain ⟨runE, cutE, headsE⟩ := skipBackTM_run_ofCfg i (w ++ [b]) e rfl
    (fun p lo hi => by
      rw [epos]
      convert tapeE p lo hi using 1
      congr 1
      simp
      omega)
  let f : Cfg k Γ SeekPhase x := {e with
    state := some .done
    workTapePos := Function.update e.workTapePos i (e.workTapePos i - (w ++ [b]).length - 1)}
  change (skipBackTM k i).runFrom e ((w ++ [b]).length + 3) = f at runE
  have radA : ∀ u ≤ w.length + 1, ∀ j,
      |((skipTM k i).runFrom a u).workTapePos j - d.workTapePos j| ≤ (w.length : ℤ) + 4 := by
    intro u hu j
    have bound := headsA j u hu
    change (if j = i then _ ∈ Finset.Icc (d.workTapePos j)
      (d.workTapePos j + w.length + 1) else _ = d.workTapePos j) at bound
    split_ifs at bound
    · obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp bound
      exact abs_le.mpr ⟨by omega, by omega⟩
    · rw [bound]; simp; omega
  have radC : ∀ u ≤ 3, ∀ j,
      |((rt_boundaryTM k i b).runFrom c u).workTapePos j - d.workTapePos j| ≤
        (w.length : ℤ) + 4 := by
    intro u hu j
    have bound := headsC u hu j
    by_cases hj : j = i
    · subst j
      simp only [if_true, Finset.mem_Icc] at bound
      have cp : c.workTapePos i = d.workTapePos i + w.length + 1 := by
        simp [c, a', a, Cfg.mapState]
      rw [cp] at bound
      exact abs_le.mpr ⟨by omega, by omega⟩
    · simp only [if_neg hj] at bound
      rw [bound]
      simp [c, a', a, Cfg.mapState, hj]; omega
  have radE : ∀ u ≤ (w ++ [b]).length + 3, ∀ j,
      |((skipBackTM k i).runFrom e u).workTapePos j - d.workTapePos j| ≤ (w.length : ℤ) + 4 := by
    intro u hu j
    have bound := headsE j u hu
    by_cases hj : j = i
    · subst j
      simp only [if_true, Finset.mem_Icc, epos, List.length_append,
        List.length_singleton, Nat.cast_add, Nat.cast_one] at bound
      exact abs_le.mpr ⟨by omega, by omega⟩
    · simp only [if_neg hj] at bound
      rw [bound]
      simp [e, c', c, a', a, Cfg.mapState, hj]; omega
  obtain ⟨runCE, cutCE, radCE⟩ := rt_copy_seam (rt_boundaryTM k i b) 3
    (skipBackTM k i) .run .done d.workTapePos ((w.length : ℤ) + 4)
    runC rfl cutC radC runE rfl cutE radE
  obtain ⟨runAll, cutAll, radAll⟩ := rt_copy_seam (skipTM k i) .done
    (seamCompTM (rt_boundaryTM k i b) 3 (skipBackTM k i) .run) (.inl 0) (.inr .done)
    d.workTapePos ((w.length : ℤ) + 4) runA rfl cutA radA runCE rfl cutCE radCE
  have start : a.mapState Sum.inl = d := by
    apply Cfg.ext <;> simp [a, Cfg.mapState, hs]
  have time : w.length + 1 + 1 + (3 + 1 + ((w ++ [b]).length + 3)) =
      2 * w.length + 10 := by simp; omega
  rw [start, time] at runAll cutAll radAll
  refine ⟨?_, cutAll, radAll⟩
  change (rt_appendSymbolTM k i b).runFrom d (2 * w.length + 10) = _ at runAll
  rw [runAll]
  apply Cfg.ext <;> try rfl
  · funext j p
    simp [f, e, c', c, a', a, Cfg.mapState]
  · funext j
    by_cases hj : j = i
    · subst j
      simp [Cfg.mapState, f, epos]; omega
    · simp [f, e, c', c, a', a, Cfg.mapState, hj]

/-- The successor leaf's phases are increment, optional extension, and exit. -/
private inductive rt_succPhase where
  | increment | extend | exit
  deriving Fintype, DecidableEq

/-- Each phase retains its cited component's state type. -/
private def rt_succControl : rt_succPhase → Type
  | .increment => FlagPhase
  | .extend => SeekPhase ⊕ (Fin 4 ⊕ SeekPhase)
  | .exit => Unit

private instance rt_succControl_fintype (p : rt_succPhase) : Fintype (rt_succControl p) := by
  cases p <;> dsimp [rt_succControl] <;> infer_instance

private instance rt_succControl_decidableEq (p : rt_succPhase) :
    DecidableEq (rt_succControl p) := by
  cases p <;> dsimp [rt_succControl] <;> infer_instance

/-- Fixed-width increment and the generic one-symbol extension supply the
successor's only computational phases. -/
private def rt_succParts (k : ℕ) (i : Fin k) :
    (p : rt_succPhase) → MultiTapeTM k Bool (rt_succControl p)
  | .increment => incrementTM k i
  | .extend => rt_appendSymbolTM k i true
  | .exit => {q₀ := (), tr := fun _ _ _ => inputMoveAction 0 ()}

/-- Success skips the extension; overflow appends the high one. Both return
through a single final anchor. -/
private def rt_succRedirect :
    (p : rt_succPhase) → rt_succControl p → Option (Σ p, rt_succControl p)
  | .increment, .done true => some ⟨.exit, ()⟩
  | .increment, .done false => some ⟨.extend, .inl .run⟩
  | .extend, .inr (.inr .done) => some ⟨.exit, ()⟩
  | _, _ => none

/-- The variable-width successor is an instance of the public phase host,
with no new carry scan or control-loop trace. -/
private def rt_succTM (k : ℕ) (i : Fin k) :
    MultiTapeTM k Bool (Σ p, rt_succControl p) :=
  phaseHostTM (rt_succParts k i) ⟨.increment, .run⟩ rt_succRedirect

/-- The hosted increment follows the catalog through either first verdict,
then dispatches once to the extension or the common exit.

**Proof sketch.** Both possible redirects are the catalog's verdict states.
The catalog cut discharges the public phase host's guard. -/
private theorem rt_succ_increment {k : ℕ} {x : List Bool} (i : Fin k)
    (a z : Cfg k Bool FlagPhase x) (t : ℕ) (b : Bool)
    (hr : (incrementTM k i).runFrom a t = z) (hz : z.state = some (.done b))
    (hc : ∀ u < t, ∀ flag, ((incrementTM k i).runFrom a u).state ≠ some (.done flag)) :
    (∀ u ≤ t, (rt_succTM k i).runFrom
      (a.mapState (Sigma.mk (β := rt_succControl) rt_succPhase.increment)) u =
      ((incrementTM k i).runFrom a u).mapState
        (Sigma.mk (β := rt_succControl) rt_succPhase.increment)) ∧
    (rt_succTM k i).runFrom
      (a.mapState (Sigma.mk (β := rt_succControl) rt_succPhase.increment)) (t + 1) =
      z.mapState (fun _ => if b then ⟨.exit, ()⟩ else ⟨.extend, .inl .run⟩) := by
  apply phaseHostTM_run (rt_succParts k i) ⟨.increment, .run⟩ rt_succRedirect
    .increment a z t hr (.done b) hz _ (by cases b <;> rfl)
  intro u hu q hq
  cases q with
  | run => rfl
  | rewind flag => rfl
  | done flag => exact (hc u hu flag hq).elim

/-- The successor has linear time and a head envelope independent of the
native input length. Its single added cell is used only on overflow.

**Proof sketch.** Use the catalog's successful or overflow increment contract,
intercepting its first verdict with the public phase host. On overflow, the
proved append-symbol leaf extends the zero word with a high one. The public
phase prefix equalities transfer the two component envelopes and cuts. -/
private theorem rt_succ_run {k : ℕ} {x : List Bool} (i : Fin k) (w : List Bool)
    (d : Cfg k Bool (Σ p, rt_succControl p) x)
    (hs : d.state = some ⟨.increment, .run⟩)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) + 1 →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    ∃ t ≤ 4 * w.length + 14,
      (∀ u < t, ((rt_succTM k i).runFrom d u).state ≠ some ⟨.exit, ()⟩) ∧
      (∀ u ≤ t, ∀ j : Fin k,
        |((rt_succTM k i).runFrom d u).workTapePos j - d.workTapePos j| ≤
          (w.length : ℤ) + 4) ∧
      (rt_succTM k i).runFrom d t =
        {d with
          state := some ⟨.exit, ()⟩
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧
                q < d.workTapePos j + ((rt_succWord w).length : ℤ)
            then FinTM.bufferTape (rt_succWord w) (q - d.workTapePos j)
            else d.workTapes j q} := by
  let a : Cfg k Bool FlagPhase x := d.mapState (fun _ => .run)
  have ha : a.state = some .run := by simp [a, Cfg.mapState, hs]
  have start : a.mapState (Sigma.mk (β := rt_succControl) rt_succPhase.increment) = d := by
    apply Cfg.ext <;> simp [a, Cfg.mapState, hs]
  have framed : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      a.workTapes i (a.workTapePos i + p) = FinTM.bufferTape w p :=
    fun p lo hi => hw p lo (by omega)
  cases hinc : incFixed w with
  | some v =>
    obtain ⟨hr, hc, hb⟩ := incrementTM_run_succ_ofCfg i w v hinc a ha framed
    obtain ⟨pre, finish⟩ := rt_succ_increment i a _ _ true hr rfl hc
    rw [start] at pre finish
    have value : rt_succWord w = v := by simp [rt_succWord, hinc]
    have len := rt_incFixed_length w v hinc
    refine ⟨2 * (w.takeWhile id).length + 3, ?_, ?_, ?_, ?_⟩
    · have := (List.takeWhile_sublist (l := w) id).length_le
      omega
    · intro u hu
      rw [pre u (by omega)]
      cases ((incrementTM k i).runFrom a u).state <;> simp [Cfg.mapState]
    · intro u hu j
      by_cases hp : u ≤ 2 * (w.takeWhile id).length + 2
      · rw [pre u hp]
        simp only [Cfg.mapState]
        have bound := hb j u hp
        change (if j = i then _ ∈ Finset.Icc (d.workTapePos j - 1)
          (d.workTapePos j + ((w.takeWhile id).length : ℤ)) else _ = d.workTapePos j) at bound
        split_ifs at bound
        · have := (List.takeWhile_sublist (l := w) id).length_le
          obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp bound
          exact abs_le.mpr ⟨by omega, by omega⟩
        · rw [bound]; simp; omega
      · have ue : u = (2 * (w.takeWhile id).length + 2) + 1 := by omega
        rw [ue, finish]
        simp [a, Cfg.mapState]; omega
    · convert finish using 1
      apply Cfg.ext <;> simp [a, Cfg.mapState, hs, value, len]
  | none =>
    obtain ⟨hr, hc, hb⟩ := incrementTM_run_overflow_ofCfg i w hinc a ha framed
    obtain ⟨pre, dispatch⟩ := rt_succ_increment i a _ _ false hr rfl hc
    rw [start] at pre dispatch
    let zeros := List.replicate w.length false
    let c : Cfg k Bool (SeekPhase ⊕ (Fin 4 ⊕ SeekPhase)) x :=
      {state := some (.inl .run), inputPos := d.inputPos, workTapePos := d.workTapePos,
       output := d.output,
       workTapes := fun j q => if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
         then FinTM.bufferTape zeros (q - d.workTapePos j) else d.workTapes j q}
    have middle : (rt_succTM k i).runFrom d (2 * w.length + 3) =
        c.mapState (Sigma.mk (β := rt_succControl) rt_succPhase.extend) := by
      exact dispatch
    have frameC : ∀ p : ℤ, -1 ≤ p → p ≤ (zeros.length : ℤ) + 1 →
        c.workTapes i (c.workTapePos i + p) = FinTM.bufferTape zeros p := by
      intro p lo hi
      simp only [c, true_and]
      by_cases inside : 0 ≤ p ∧ p < (w.length : ℤ)
      · rw [if_pos (by omega)]
        congr 1; omega
      · rw [if_neg (by omega), hw p lo (by simpa [zeros] using hi)]
        have hp : p = -1 ∨ p = w.length ∨ p = (w.length : ℤ) + 1 := by
          simp only [zeros, List.length_replicate] at hi; omega
        rcases hp with rfl | rfl | rfl <;> simp [FinTM.bufferTape, zeros]
    obtain ⟨hg, hcut, hrad⟩ := rt_appendSymbol_run i true zeros c rfl frameC
    let z := (rt_appendSymbolTM k i true).runFrom c (2 * zeros.length + 10)
    have hz : z.state = some (.inr (.inr .done)) := by rw [show z = _ from hg]
    obtain ⟨growPre, growEnd⟩ := phaseHostTM_run (rt_succParts k i)
      ⟨.increment, .run⟩ rt_succRedirect .extend c z (2 * zeros.length + 10)
      rfl (.inr (.inr .done)) hz ⟨.exit, ()⟩ rfl (by
        intro u hu q hq
        cases q with
        | inl q => rfl
        | inr q =>
          cases q with
          | inl q => rfl
          | inr q =>
            cases q <;> try rfl
            exact (hcut u hu hq).elim)
    have total : (rt_succTM k i).runFrom d (4 * w.length + 14) =
        z.mapState (fun _ => ⟨.exit, ()⟩) := by
      rw [show 4 * w.length + 14 = (2 * w.length + 3) + (2 * zeros.length + 10 + 1) by
        simp [zeros]; omega, MultiTapeTM.runFrom_add, middle]
      exact growEnd
    refine ⟨4 * w.length + 14, le_rfl, ?_, ?_, ?_⟩
    · intro u hu
      by_cases early : u ≤ 2 * w.length + 2
      · rw [pre u early]
        cases ((incrementTM k i).runFrom a u).state <;> simp [Cfg.mapState]
      · rw [show u = (2 * w.length + 3) + (u - (2 * w.length + 3)) by omega,
          MultiTapeTM.runFrom_add, middle, growPre _ (by simp [zeros]; omega)]
        cases ((rt_appendSymbolTM k i true).runFrom c (u - (2 * w.length + 3))).state <;>
          simp [Cfg.mapState]
    · intro u hu j
      by_cases early : u ≤ 2 * w.length + 2
      · rw [pre u early]
        simp only [Cfg.mapState]
        have bound := hb j u early
        change (if j = i then _ ∈ Finset.Icc (d.workTapePos j - 1)
          (d.workTapePos j + w.length) else _ = d.workTapePos j) at bound
        split_ifs at bound
        · obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp bound
          exact abs_le.mpr ⟨by omega, by omega⟩
        · rw [bound]; simp; omega
      · by_cases last : u = 4 * w.length + 14
        · rw [last, total]
          simp only [z, hg, Cfg.mapState, c, sub_self, abs_zero]
          omega
        · rw [show u = (2 * w.length + 3) + (u - (2 * w.length + 3)) by omega,
            MultiTapeTM.runFrom_add, middle, growPre _ (by simp [zeros]; omega)]
          simpa [c, zeros, Cfg.mapState] using hrad (u - (2 * w.length + 3))
            (by simp [zeros]; omega) j
    · rw [total]
      have value : rt_succWord w = zeros ++ [true] := by simp [rt_succWord, hinc, zeros]
      apply Cfg.ext
      · simp [z, hg, Cfg.mapState]
      · simp [z, hg, Cfg.mapState, c]
      · funext j q
        simp only [z, hg, Cfg.mapState, c, value, List.length_append,
          List.length_singleton, zeros, List.length_replicate, Nat.cast_add, Nat.cast_one]
        by_cases ji : j = i
        · subst j
          simp only [Function.update_self, true_and]
          rw [FinTM.bufferTape_append (List.replicate w.length false) true]
          rw [List.length_replicate]
          by_cases eq : q = d.workTapePos i + w.length
          · subst q
            have shift : d.workTapePos i + (w.length : ℤ) - d.workTapePos i = w.length := by omega
            rw [shift]
            simp
          · rw [Function.update_of_ne eq, Function.update_of_ne (by omega)]
            by_cases inside : d.workTapePos i ≤ q ∧ q < d.workTapePos i + w.length
            · rw [if_pos inside, if_pos (by omega)]
            · rw [if_neg inside, if_neg (by omega)]
        · simp [ji]
      · simp [z, hg, Cfg.mapState, c]
      · simp [z, hg, Cfg.mapState, c]

/-- A clean Boolean bank can write the input-length bound in canonical binary,
restoring every head and all scratch tapes.

**Proof sketch.** Cite `exists_inputLengthTM`, then the variable-width successor
leaf, with one public R2 seam. Monotonicity of bit length gives the space
bound; bit length at most input length plus one gives the time bound. This is
the bound-field phase to be lifted onto the template's dedicated digit bank. -/
private theorem rt_exists_boundTM :
    ∃ (K : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (R : MultiTapeTM (K + 1) Bool S) (entry exit : S) (C : ℕ),
      ∀ {x : List Bool} (d : Cfg (K + 1) Bool S x),
      d.state = some entry → d.inputPos = 1 → (∀ j q, d.workTapes j q = none) →
      ∃ t ≤ C * (x.length + 1),
        (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
        (∀ u ≤ t, ∀ j, |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
          ((C * ((x.length + 1).bits.length + 1) : ℕ) : ℤ)) ∧
        R.runFrom d t = {d with
          state := some exit
          workTapes := fun j q =>
            if j = 0 then FinTM.bufferTape (x.length + 1).bits (q - d.workTapePos j)
            else d.workTapes j q} := by
  obtain ⟨K, S, hfin, heq, M, en, ex, C, contract⟩ := exists_inputLengthTM
  letI := hfin
  letI := heq
  refine ⟨K, S ⊕ (Σ p, rt_succControl p), inferInstance, inferInstance,
    seamCompTM M ex (rt_succTM (K + 1) 0) ⟨.increment, .run⟩,
    .inl en, .inr ⟨.exit, ()⟩, C + 20, ?_⟩
  intro x d hd hip blank
  let a : Cfg (K + 1) Bool S x := d.mapState (fun _ => en)
  have ha : a.state = some en := by simp [a, Cfg.mapState, hd]
  obtain ⟨t, deadline, cut, heads, run⟩ := contract a ha hip
    (fun q _ _ => blank 0 _) (fun j _ q => blank j q)
  let a' : Cfg (K + 1) Bool S x := {a with
    state := some ex
    workTapes := fun j q =>
      if j = 0 ∧ a.workTapePos j ≤ q ∧ q < a.workTapePos j + (x.length.bits.length : ℤ)
      then FinTM.bufferTape x.length.bits (q - a.workTapePos j) else a.workTapes j q}
  change M.runFrom a t = a' at run
  let c := a'.mapState (fun _ => (⟨.increment, .run⟩ : Σ p, rt_succControl p))
  have framed : ∀ p : ℤ, -1 ≤ p → p ≤ (x.length.bits.length : ℤ) + 1 →
      c.workTapes 0 (c.workTapePos 0 + p) = FinTM.bufferTape x.length.bits p := by
    intro p lo hi
    simp only [c, a', a, Cfg.mapState, true_and]
    by_cases inside : 0 ≤ p ∧ p < (x.length.bits.length : ℤ)
    · rw [if_pos (by omega)]
      congr 1; omega
    · rw [if_neg (by omega), blank]
      by_cases neg : p < 0
      · simp [FinTM.bufferTape, show ¬0 ≤ p by omega]
      · simp [FinTM.bufferTape, show 0 ≤ p by omega,
          List.getElem?_eq_none (show x.length.bits.length ≤ p.toNat by omega)]
  obtain ⟨u, ub, ucut, uheads, urun⟩ := rt_succ_run (0 : Fin (K + 1)) x.length.bits c rfl framed
  have monotone : x.length.bits.length ≤ (x.length + 1).bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.le_succ x.length)
  have short : x.length.bits.length ≤ x.length + 1 := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact lt_trans (Nat.lt_succ_self _) Nat.lt_two_pow_self
  let B : ℤ := ((C + 20) * ((x.length + 1).bits.length + 1) : ℕ)
  have firstBound : (C * (x.length.bits.length + 1) : ℕ) ≤
      (C + 20) * ((x.length + 1).bits.length + 1) := by nlinarith
  have nextBound : (x.length.bits.length : ℤ) + 4 ≤ B := by
    dsimp [B]
    exact_mod_cast (show x.length.bits.length + 4 ≤
      (C + 20) * ((x.length + 1).bits.length + 1) by nlinarith)
  have rA : ∀ v ≤ t, ∀ j, |(M.runFrom a v).workTapePos j - d.workTapePos j| ≤ B := by
    intro v hv j
    exact (heads v hv j).trans (by dsimp [B]; exact_mod_cast firstBound)
  have rC : ∀ v ≤ u, ∀ j,
      |((rt_succTM (K + 1) 0).runFrom c v).workTapePos j - d.workTapePos j| ≤ B :=
    fun v hv j => (uheads v hv j).trans nextBound
  obtain ⟨composed, first, radius⟩ := rt_copy_seam M ex (rt_succTM (K + 1) 0)
    ⟨.increment, .run⟩ ⟨.exit, ()⟩ d.workTapePos B
    run rfl cut rA urun rfl ucut rC
  have start : a.mapState Sum.inl = d := by
    apply Cfg.ext <;> simp [a, Cfg.mapState, hd]
  rw [start] at composed first radius
  refine ⟨t + 1 + u, by nlinarith, first, radius, ?_⟩
  rw [composed]
  apply Cfg.ext <;> try rfl
  funext j q
  simp only [Cfg.mapState, c, a', a, rt_succWord_bits]
  by_cases j0 : j = 0
  · subst j
    simp only [true_and, if_true]
    by_cases inside : d.workTapePos 0 ≤ q ∧ q < d.workTapePos 0 + ((x.length + 1).bits.length : ℤ)
    · rw [if_pos inside]
    · rw [if_neg inside, if_neg (by omega), blank]
      rw [FinTM.bufferTape]
      split_ifs with nonnegative
      · rw [List.getElem?_eq_none (show (x.length + 1).bits.length ≤
            (q - d.workTapePos 0).toNat by omega)]
      · rfl
  · simp [j0]

/-- The bound writer transported onto an isolated digit bank of an arbitrary
rich host. Its selected tapes are lifts of a globally blank Boolean bank;
the unselected tapes and the prior output are arbitrary.

**Proof sketch.** Obtain the clean-bank bound writer, lift its whole run along
`RecSym.digitEmb`, then use the public R1 forwarding transport. Selected-head
bounds use `embedEmitCfg_selected_pos`; unselected heads use the public frame.
No restriction or decoding of an arbitrary rich tape is needed. -/
private theorem rt_exists_digitBoundTM (Q T : Type) [DecidableEq Q] [DecidableEq T] :
    ∃ (K : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (R : MultiTapeTM (K + 1) (RecSym Q T) S) (entry exit : S) (C : ℕ),
      ∀ {k : ℕ} (ι : Fin (K + 1) ↪ Fin k) {x : List Bool}
        (a : Cfg (K + 1) Bool S x),
        a.state = some entry → a.inputPos = 1 →
        (∀ j q, a.workTapes j q = none) → a.output = [] →
      ∀ (tapes : Fin k → ℤ → Option (RecSym Q T)) (heads : Fin k → ℤ)
        (pre : List (RecSym Q T)),
      let d := embedEmitCfg ι tapes heads pre (a.liftSymbols (RecSym.digitEmb Q T))
      ∃ t ≤ C * (x.length + 1),
        (∀ u < t, ((embedEmitTM ι R).runFrom d u).state ≠ some exit) ∧
        (∀ u ≤ t, ∀ j,
          |((embedEmitTM ι R).runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * ((x.length + 1).bits.length + 1) : ℕ) : ℤ)) ∧
        (embedEmitTM ι R).runFrom d t =
          embedEmitCfg ι tapes heads pre
            (({a with
              state := some exit
              workTapes := fun j q =>
                if j = 0 then FinTM.bufferTape (x.length + 1).bits (q - a.workTapePos j)
                else a.workTapes j q} : Cfg (K + 1) Bool S x).liftSymbols
                  (RecSym.digitEmb Q T)) := by
  obtain ⟨K, S, hfin, heq, M, entry, exit, C, contract⟩ := rt_exists_boundTM
  letI := hfin
  letI := heq
  let e := RecSym.digitEmb Q T
  refine ⟨K, S, hfin, heq, M.liftSymbols e, entry, exit, C, ?_⟩
  intro k ι x a hs hi blank _ tapes heads pre d
  obtain ⟨t, deadline, cut, radius, finish⟩ := contract a hs hi blank
  have transfer (u : ℕ) :
      (embedEmitTM ι (M.liftSymbols e)).runFrom d u =
        embedEmitCfg ι tapes heads pre ((M.runFrom a u).liftSymbols e) := by
    rw [show d = embedEmitCfg ι tapes heads pre (a.liftSymbols e) from rfl,
      embedEmitTM_runFrom, MultiTapeTM.liftSymbols_runFrom]
  refine ⟨t, deadline, ?_, ?_, ?_⟩
  · intro u hu
    rw [transfer]
    exact cut u hu
  · intro u hu j
    by_cases selected : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := selected
      rw [transfer, embedEmitCfg_selected_pos]
      change |(M.runFrom a u).workTapePos i -
        (embedEmitCfg ι tapes heads pre (a.liftSymbols e)).workTapePos (ι i)| ≤ _
      rw [embedEmitCfg_selected_pos]
      exact radius u hu i
    · have now := ((embedEmitTM_frame ι (M.liftSymbols e) tapes heads pre
          (a.liftSymbols e) u).1 j selected).2
      have initial := ((embedEmitTM_frame ι (M.liftSymbols e) tapes heads pre
          (a.liftSymbols e) 0).1 j selected).2
      change ((embedEmitTM ι (M.liftSymbols e)).runFrom d u).workTapePos j = heads j at now
      change d.workTapePos j = heads j at initial
      rw [now, initial, sub_self, abs_zero]
      exact_mod_cast (Nat.zero_le _)
  · rw [transfer, finish]

/-- The centered mark in a window is exactly two runs of unmarked cells with
one marked cell between them. This identifies the two expansion phases and
the one-cell writer with the record template's window field. -/
private theorem rt_centeredWord {Γ : Type*} (f : Bool → Γ) (s : ℕ) :
    (List.range (2 * s + 1)).map (fun j => f (decide (j = s))) =
      (List.replicate s false ++ true :: List.replicate s false).map f := by
  simp only [List.map_append, List.map_cons, List.map_replicate]
  apply List.ext_getElem
  · simp; omega
  · intro j hj hk
    simp only [List.getElem_map, List.getElem_range]
    by_cases left : j < s
    · rw [List.getElem_append_left (by simpa using left)]
      simp [show j ≠ s by omega]
    · rw [List.getElem_append_right (by simp; omega)]
      by_cases middle : j = s
      · subst j; simp
      · simp only [List.length_replicate]
        rw [List.getElem_cons]
        simp [show j - s ≠ 0 by omega, middle]

/-- The canonical bound word and the two unmarked runs are exactly the
frozen template's two fields. This is the output identity for the unfinished
window pipeline. -/
private theorem rt_template_fields (Q T : Type) (n s : ℕ) :
    recordTemplate Q T n s =
      [((n + 1).bits).map RecSym.digit,
        (List.replicate s false ++ true :: List.replicate s false).map (RecSym.cell none)] := by
  rw [recordTemplate, binDigits_posWidth_succ, rt_centeredWord]

/-! ### Record-template fill, continuation 4 -/

/-- Expansion on a three-tape digit bank: tape zero is untouched, tape one
receives the repeated pattern, and tape two is the consumed counter.

**Proof sketch.** Restrict to the first two tapes and apply the public
expansion contract. The public counter-layout identity identifies the actual
three-tape entry and endpoint. Its two trajectory clauses give the envelope. -/
private theorem rt_expand_run {x : List Bool} (pat ws : List Bool) (s : ℕ)
    (value : Nat.ofDigits 2 (ws.map Bool.toNat) = s)
    (d : Cfg 3 Bool (CounterLoopState (Fin (pat.length + 1))) x)
    (entry : d.state = some (.dec .run))
    (counter : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      d.workTapes 2 (d.workTapePos 2 + p) = FinTM.bufferTape ws p) :
    let t := s * (pat.length + 1) + counterOverhead ws (s + 1)
    (expandTM 2 1 pat).runFrom d t =
      { d with
        state := some .done
        workTapes := fun j q =>
          if j = 2 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (ws.length : ℤ)
          then some true
          else if j = 1 ∧ d.workTapePos j ≤ q ∧
              q < d.workTapePos j + ((s * pat.length : ℕ) : ℤ)
          then FinTM.bufferTape (List.replicate s pat).flatten (q - d.workTapePos j)
          else d.workTapes j q
        workTapePos := Function.update d.workTapePos 1
          (d.workTapePos 1 + ((s * pat.length : ℕ) : ℤ)) } ∧
    (∀ u < t, ((expandTM 2 1 pat).runFrom d u).state ≠ some .done) ∧
    (∀ u ≤ t, ∀ j,
      |((expandTM 2 1 pat).runFrom d u).workTapePos j - d.workTapePos j| ≤
        ((s * pat.length + ws.length + 1 : ℕ) : ℤ)) := by
  let c : Cfg 2 Bool (Fin (pat.length + 1)) x :=
    { state := some 0, inputPos := d.inputPos, output := d.output,
      workTapes := fun j => d.workTapes j.castSucc,
      workTapePos := fun j => d.workTapePos j.castSucc }
  have start : counterLoopCfg (some (.dec .run)) c
      (d.workTapes 2) (d.workTapePos 2) = d := by
    rw [counter_cfg_eq]
    apply Cfg.ext
    · exact entry.symm
    · rfl
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  obtain ⟨run, cut, counterHeads, bodyHeads⟩ :=
    expandTM_run_ofCfg (1 : Fin 2) pat c rfl ws (d.workTapes 2)
      (d.workTapePos 2) counter s value
  rw [start] at run cut counterHeads bodyHeads
  refine ⟨?_, fun u hu => (cut u hu).1, ?_⟩
  · rw [run, counter_cfg_eq]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j q
      dsimp only
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.lastCases_last]
        simp [show (Fin.last 2 : Fin 3) = 2 from rfl]
      · simp only [Fin.lastCases_castSucc]
        fin_cases i <;> simp [c]
    · funext j
      dsimp only
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.lastCases_last]
        change d.workTapePos 2 = Function.update d.workTapePos 1 _ 2
        simp
      · simp only [Fin.lastCases_castSucc]
        fin_cases i <;> simp [c]
    · rfl
  · intro u hu j
    fin_cases j
    · have h := bodyHeads u hu 0
      change (if (0 : Fin 2) = 1 then _ else
        ((expandTM 2 1 pat).runFrom d u).workTapePos 0 = d.workTapePos 0) at h
      simp only [show (0 : Fin 2) ≠ 1 by decide, if_false] at h
      change |((expandTM 2 1 pat).runFrom d u).workTapePos 0 - d.workTapePos 0| ≤ _
      rw [h, sub_self, abs_zero]
      exact_mod_cast Nat.zero_le _
    · have h := bodyHeads u hu 1
      simp only [if_true, Finset.mem_Icc] at h
      change d.workTapePos 1 ≤ ((expandTM 2 1 pat).runFrom d u).workTapePos 1 ∧
        ((expandTM 2 1 pat).runFrom d u).workTapePos 1 ≤
          d.workTapePos 1 + ((s * pat.length : ℕ) : ℤ) at h
      change |((expandTM 2 1 pat).runFrom d u).workTapePos 1 - d.workTapePos 1| ≤ _
      exact abs_le.mpr ⟨by omega, by omega⟩
    · have h := Finset.mem_Icc.mp (counterHeads u hu)
      change d.workTapePos 2 - 1 ≤ ((expandTM 2 1 pat).runFrom d u).workTapePos 2 ∧
        ((expandTM 2 1 pat).runFrom d u).workTapePos 2 ≤ d.workTapePos 2 + ws.length at h
      change |((expandTM 2 1 pat).runFrom d u).workTapePos 2 - d.workTapePos 2| ≤ _
      exact abs_le.mpr ⟨by omega, by omega⟩

/-- Repeat a fixed digit pattern using a preserved radius word on tape zero.
The public copy, expansion and clear rows are joined by two R2 seams. -/
private def rt_repeatTM (pat : List Bool) :
    MultiTapeTM 3 Bool (SweepPhase ⊕ (CounterLoopState (Fin (pat.length + 1)) ⊕ SweepPhase)) :=
  seamCompTM (copyTM 3 0 2) .done
    (seamCompTM (expandTM 2 1 pat) .done (clearTM 3 2) .sweep) (.inl (.dec .run))

/-- One expansion preserves the original radius, restores its temporary
counter and advances the destination head by the number of cells written.
It can therefore be invoked twice with the same original radius word.

**Proof sketch.** Copy the delimited radius into blank counter space, apply
`rt_expand_run`, and clear the resulting all-true counter. The destination
and counter are distinct, so the two counter write masks cancel against the
initial blank frame. Combine the three first-exit certificates by R2. -/
private theorem rt_repeat_run {x : List Bool} (pat ws : List Bool) (s : ℕ)
    (value : Nat.ofDigits 2 (ws.map Bool.toNat) = s)
    (d : Cfg 3 Bool
      (SweepPhase ⊕ (CounterLoopState (Fin (pat.length + 1)) ⊕ SweepPhase)) x)
    (entry : d.state = some (.inl .sweep))
    (radius : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape ws p)
    (blank : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      d.workTapes 2 (d.workTapePos 2 + p) = none) :
    let t := 4 * ws.length + s * (pat.length + 1) + counterOverhead ws (s + 1) + 6
    (rt_repeatTM pat).runFrom d t =
      { d with
        state := some (.inr (.inr .done))
        workTapes := fun j q =>
          if j = 1 ∧ d.workTapePos j ≤ q ∧
              q < d.workTapePos j + ((s * pat.length : ℕ) : ℤ)
          then FinTM.bufferTape (List.replicate s pat).flatten (q - d.workTapePos j)
          else d.workTapes j q
        workTapePos := Function.update d.workTapePos 1
          (d.workTapePos 1 + ((s * pat.length : ℕ) : ℤ)) } ∧
    (∀ u < t, ((rt_repeatTM pat).runFrom d u).state ≠ some (.inr (.inr .done))) ∧
    (∀ u ≤ t, ∀ j,
      |((rt_repeatTM pat).runFrom d u).workTapePos j - d.workTapePos j| ≤
        ((s * pat.length + ws.length + 1 : ℕ) : ℤ)) := by
  let a : Cfg 3 Bool SweepPhase x := d.mapState (fun _ => .sweep)
  have ast : a.state = some .sweep := by simp [a, Cfg.mapState, entry]
  obtain ⟨copyRun, copyCut, copyHeads⟩ :=
    copyTM_run_ofCfg (0 : Fin 3) 2 (by decide) ws a ast radius
  let copied : Cfg 3 Bool SweepPhase x :=
    { a with
      state := some .done
      workTapes := fun j q =>
        if j = 2 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (ws.length : ℤ)
        then FinTM.bufferTape ws (q - d.workTapePos j) else d.workTapes j q }
  change (copyTM 3 0 2).runFrom a (2 * ws.length + 2) = copied at copyRun
  let b := copied.mapState (fun _ => (CounterLoopState.dec .run :
    CounterLoopState (Fin (pat.length + 1))))
  have counter : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      b.workTapes 2 (b.workTapePos 2 + p) = FinTM.bufferTape ws p := by
    intro p lo hi
    change (if (2 : Fin 3) = 2 ∧ d.workTapePos 2 ≤ d.workTapePos 2 + p ∧
        d.workTapePos 2 + p < d.workTapePos 2 + (ws.length : ℤ)
      then FinTM.bufferTape ws (d.workTapePos 2 + p - d.workTapePos 2)
      else d.workTapes 2 (d.workTapePos 2 + p)) = _
    by_cases interior : 0 ≤ p ∧ p < (ws.length : ℤ)
    · rw [if_pos (by omega)]; congr 1; omega
    · rw [if_neg (by omega), blank p lo hi]
      have edge : p = -1 ∨ p = (ws.length : ℤ) := by omega
      rcases edge with rfl | rfl <;> simp [FinTM.bufferTape]
  obtain ⟨expandRun, expandCut, expandHeads⟩ := rt_expand_run pat ws s value b rfl counter
  let expanded := (expandTM 2 1 pat).runFrom b
    (s * (pat.length + 1) + counterOverhead ws (s + 1))
  let c := expanded.mapState (fun _ => SweepPhase.sweep)
  have cst : c.state = some .sweep := by simp [c, expanded, expandRun, Cfg.mapState]
  have cpos (j : Fin 3) : c.workTapePos j =
      Function.update d.workTapePos 1
        (d.workTapePos 1 + ((s * pat.length : ℕ) : ℤ)) j := by
    simp only [c, expanded, expandRun, Cfg.mapState, b, copied, a]
  have ones : ∀ p : ℤ, -1 ≤ p → p ≤ ((List.replicate ws.length true).length : ℤ) →
      c.workTapes 2 (c.workTapePos 2 + p) =
        FinTM.bufferTape (List.replicate ws.length true) p := by
    intro p lo hi
    simp only [List.length_replicate] at hi
    simp only [c, expanded, expandRun, Cfg.mapState, b, copied, a,
      Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide),
      show (2 : Fin 3) ≠ 1 by decide, false_and, if_false, true_and]
    by_cases interior : 0 ≤ p ∧ p < (ws.length : ℤ)
    · rw [if_pos (by omega)]
      simp [FinTM.bufferTape, interior.1,
        show p.toNat < ws.length by omega]
    · rw [if_neg (by omega), if_neg (by omega), blank p lo hi]
      have edge : p = -1 ∨ p = (ws.length : ℤ) := by omega
      rcases edge with rfl | rfl <;> simp [FinTM.bufferTape]
  obtain ⟨clearRun, clearCut, clearHeads⟩ :=
    clearTM_run_ofCfg (2 : Fin 3) (List.replicate ws.length true) c cst ones
  let B : ℤ := (s * pat.length + ws.length + 1 : ℕ)
  have product_nonneg : (0 : ℤ) ≤ (s : ℤ) * pat.length :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have copyBound : ∀ u ≤ 2 * ws.length + 2, ∀ j,
      |((copyTM 3 0 2).runFrom a u).workTapePos j - d.workTapePos j| ≤ B := by
    intro u hu j
    have h := copyHeads j u hu
    change (if j = 0 ∨ j = 2 then _ ∈ Finset.Icc
      (d.workTapePos j - 1) (d.workTapePos j + ws.length) else _ = d.workTapePos j) at h
    split_ifs at h
    · obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp h
      exact abs_le.mpr ⟨by dsimp [B]; omega, by dsimp [B]; omega⟩
    · rw [h, sub_self, abs_zero]; dsimp [B]; positivity
  have clearBound : ∀ u ≤ 2 * (List.replicate ws.length true).length + 2, ∀ j,
      |((clearTM 3 2).runFrom c u).workTapePos j - d.workTapePos j| ≤ B := by
    intro u hu j
    have h := clearHeads j u hu
    by_cases j2 : j = 2
    · subst j
      simp only [if_true, Finset.mem_Icc, cpos, List.length_replicate,
        Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide)] at h
      rw [abs_le]; dsimp only [B]; constructor <;> omega
    · simp only [if_neg j2] at h
      rw [h, cpos]
      by_cases j1 : j = 1
      · subst j
        rw [Function.update_self, abs_le]
        dsimp only [B]; constructor <;> omega
      · rw [Function.update_of_ne j1, sub_self, abs_zero]
        dsimp only [B]; exact_mod_cast Nat.zero_le _
  obtain ⟨tailRun, tailCut, tailHeads⟩ := rt_copy_seam (expandTM 2 1 pat) .done
    (clearTM 3 2) .sweep .done d.workTapePos B
    (show (expandTM 2 1 pat).runFrom b _ = expanded from rfl)
    (by simp [expanded, expandRun]) expandCut expandHeads clearRun rfl clearCut clearBound
  obtain ⟨run, cut, heads⟩ := rt_copy_seam (copyTM 3 0 2) .done
    (seamCompTM (expandTM 2 1 pat) .done (clearTM 3 2) .sweep)
    (.inl (.dec .run)) (.inr .done) d.workTapePos B copyRun rfl copyCut copyBound
    tailRun rfl tailCut tailHeads
  have start : a.mapState Sum.inl = d := by
    apply Cfg.ext <;> simp [a, Cfg.mapState, entry]
  have duration : 2 * ws.length + 2 + 1 +
      (s * (pat.length + 1) + counterOverhead ws (s + 1) + 1 +
        (2 * (List.replicate ws.length true).length + 2)) =
      4 * ws.length + s * (pat.length + 1) + counterOverhead ws (s + 1) + 6 := by
    simp only [List.length_replicate]; omega
  rw [start, duration] at run cut heads
  refine ⟨?_, cut, heads⟩
  change (rt_repeatTM pat).runFrom d _ = _ at run
  rw [run]
  apply Cfg.ext
  · rfl
  · simp only [Cfg.mapState, c, expanded, expandRun, b, copied, a]
  · funext j q
    simp only [Cfg.mapState, c, expanded, expandRun, b, copied, a,
      List.length_replicate]
    by_cases j2 : j = 2
    · subst j
      simp only [Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide),
        show (2 : Fin 3) ≠ 1 by decide, false_and, if_false, true_and]
      split_ifs with h
      · have hb := blank (q - d.workTapePos 2) (by omega) (by omega)
        simpa only [add_sub_cancel] using hb.symm
      · rfl
    · simp only [j2, false_and, if_false]
  · exact funext cpos
  · simp only [Cfg.mapState, c, expanded, expandRun, b, copied, a]

/-- The public release adapter makes an advancing writer's positive return
usable as a first-exit phase, including an empty pattern.

**Proof sketch.** Cite the writer's exact return and the release theorem.
The public release trajectory equality transports its head envelope. -/
private theorem rt_writeReleased_run {Γ : Type*} {k : ℕ} {x : List Γ}
    (i : Fin k) (w : List Γ) (d : Cfg k Γ (Unit ⊕ Fin (w.length + 1)) x)
    (entry : d.state = some (.inl ())) :
    (seamReleaseTM (writeAdvTM k i w) 0).runFrom d (w.length + 1) =
      { d with
        state := some (.inr 0)
        workTapes := fun j q =>
          if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
          then FinTM.bufferTape w (q - d.workTapePos j) else d.workTapes j q
        workTapePos := Function.update d.workTapePos i (d.workTapePos i + w.length) } ∧
    (∀ u < w.length + 1,
      ((seamReleaseTM (writeAdvTM k i w) 0).runFrom d u).state ≠ some (.inr 0)) ∧
    (∀ u ≤ w.length + 1, ∀ j,
      |((seamReleaseTM (writeAdvTM k i w) 0).runFrom d u).workTapePos j -
        d.workTapePos j| ≤ (w.length : ℤ)) := by
  let c : Cfg k Γ (Fin (w.length + 1)) x := d.mapState (fun _ => 0)
  have ce : c.state = some 0 := by simp [c, Cfg.mapState, entry]
  obtain ⟨finish, cut, heads⟩ := writeAdvTM_run_ofCfg i w c ce
  obtain ⟨release, first⟩ := seamReleaseTM_firstReturn (writeAdvTM k i w) 0
    ce (Nat.succ_pos _) finish rfl cut
  have start : c.mapState (fun _ => (Sum.inl () : Unit ⊕ Fin (w.length + 1))) = d := by
    apply Cfg.ext <;> simp [c, Cfg.mapState, entry]
  rw [start] at release first
  refine ⟨release, first, ?_⟩
  intro u hu j
  have visited := seamReleaseTM_visitedByTapeHead (writeAdvTM k i w) 0 ce u j
  rw [start] at visited
  have member := Finset.mem_image_of_mem
    (fun v => ((seamReleaseTM (writeAdvTM k i w) 0).runFrom d v).workTapePos j)
    (Finset.mem_range.mpr (Nat.lt_succ_self u))
  change ((seamReleaseTM (writeAdvTM k i w) 0).runFrom d u).workTapePos j ∈
    (seamReleaseTM (writeAdvTM k i w) 0).visitedByTapeHead d u j at member
  rw [visited] at member
  obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp member
  rw [← eq]
  have h := heads j v (by have := Finset.mem_range.mp hv; omega)
  change (if j = i then _ ∈ Finset.Icc (d.workTapePos j)
    (d.workTapePos j + w.length) else _ = d.workTapePos j) at h
  split_ifs at h
  · obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp h
    exact abs_le.mpr ⟨by omega, by omega⟩
  · rw [h, sub_self, abs_zero]; exact_mod_cast Nat.zero_le _

/-- Two adjacent framed word writes are one write of their concatenation.

**Proof sketch.** Partition a cell into the first interval, the second, and
its complement. The public list-append lookup equations identify both
interior cases; the complement preserves the original cell. -/
private theorem rt_adjacentWrites {Γ : Type*} (tape : ℤ → Option Γ) (o : ℤ)
    (u v : List Γ) :
    (fun q => if o + (u.length : ℤ) ≤ q ∧ q < o + u.length + (v.length : ℤ)
      then FinTM.bufferTape v (q - (o + u.length))
      else if o ≤ q ∧ q < o + (u.length : ℤ)
      then FinTM.bufferTape u (q - o) else tape q) =
    (fun q => if o ≤ q ∧ q < o + ((u ++ v).length : ℤ)
      then FinTM.bufferTape (u ++ v) (q - o) else tape q) := by
  funext q
  simp only [List.length_append, Nat.cast_add]
  by_cases first : o ≤ q ∧ q < o + (u.length : ℤ)
  · rw [if_neg (by omega), if_pos first, if_pos (by omega)]
    simp only [FinTM.bufferTape, if_pos (show 0 ≤ q - o by omega)]
    exact (List.getElem?_append_left (show (q - o).toNat < u.length by omega)).symm
  · rw [if_neg first]
    by_cases second : o + (u.length : ℤ) ≤ q ∧ q < o + u.length + (v.length : ℤ)
    · rw [if_pos second, if_pos (by omega)]
      simp only [FinTM.bufferTape, if_pos (show 0 ≤ q - (o + u.length) by omega),
        if_pos (show 0 ≤ q - o by omega),
        List.getElem?_append_right (show u.length ≤ (q - o).toNat by omega)]
      congr 1
      omega
    · rw [if_neg second, if_neg (by omega)]

/-- The endpoint of writing one contiguous word and advancing its tape head. -/
private def rt_advanceCfg {k : ℕ} {Γ P : Type*} {x : List Γ}
    (d : Cfg k Γ P x) (i : Fin k) (w : List Γ) (q : P) : Cfg k Γ P x :=
  { d with
    state := some q
    workTapes := fun j p =>
      if j = i ∧ d.workTapePos j ≤ p ∧ p < d.workTapePos j + (w.length : ℤ)
      then FinTM.bufferTape w (p - d.workTapePos j) else d.workTapes j p
    workTapePos := Function.update d.workTapePos i (d.workTapePos i + w.length) }

/-- Consecutive advancing writes, with a control relabeling between them,
write the concatenation and advance by its length.

**Proof sketch.** The tape equality is `rt_adjacentWrites`; all other fields
follow from the two updates and addition of the word lengths. -/
private theorem rt_advanceCfg_append {k : ℕ} {Γ P S : Type*} {x : List Γ}
    (d : Cfg k Γ P x) (i : Fin k) (u v : List Γ) (q : P) (f : P → S) (r : S) :
    rt_advanceCfg ((rt_advanceCfg d i u q).mapState f) i v r =
      rt_advanceCfg (d.mapState f) i (u ++ v) r := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j p
    by_cases ji : j = i
    · subst j
      simp only [rt_advanceCfg, Cfg.mapState, Function.update_self, true_and]
      exact congrFun (rt_adjacentWrites (d.workTapes i) (d.workTapePos i) u v) p
    · simp [rt_advanceCfg, Cfg.mapState, ji]
  · funext j
    by_cases ji : j = i
    · subst j
      simp [rt_advanceCfg, Cfg.mapState, add_assoc]
    · simp [rt_advanceCfg, Cfg.mapState, ji]
  · rfl

/-- Control of a one-bit-pattern expansion with a preserved radius. -/
private abbrev rt_halfState := SweepPhase ⊕ (CounterLoopState (Fin 2) ⊕ SweepPhase)

/-- Two independently copied radius counters write the two unmarked halves.
A released advancing writer places the central mark between them. -/
private def rt_windowAdvTM :
    MultiTapeTM 3 Bool (rt_halfState ⊕ ((Unit ⊕ Fin 2) ⊕ rt_halfState)) :=
  seamCompTM (rt_repeatTM [false]) (.inr (.inr .done))
    (seamCompTM (seamReleaseTM (writeAdvTM 3 1 [true]) 0) (.inr 0)
      (rt_repeatTM [false]) (.inl .sweep)) (.inl (.inl ()))

/-- The digit window is written as two unmarked runs separated by one mark.
The radius and counter are restored, and the destination head ends just
past the window. The entire run is linear in radius and radius-word length.

**Proof sketch.** Invoke the preserved-radius expansion twice, around the
released one-symbol writer. Its exact restoration supplies the second copy's
preconditions. Two adjacent-write identities merge the three output masks.
The public R2 certificate combines cuts and shifted head envelopes. -/
private theorem rt_windowAdv_run {x : List Bool} (ws : List Bool) (s : ℕ)
    (value : Nat.ofDigits 2 (ws.map Bool.toNat) = s)
    (d : Cfg 3 Bool (rt_halfState ⊕ ((Unit ⊕ Fin 2) ⊕ rt_halfState)) x)
    (entry : d.state = some (.inl (.inl .sweep)))
    (radius : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape ws p)
    (blank : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      d.workTapes 2 (d.workTapePos 2 + p) = none) :
    ∃ t ≤ 12 * (s + ws.length) + 20,
      (∀ u < t, (rt_windowAdvTM.runFrom d u).state ≠
        some (.inr (.inr (.inr (.inr .done))))) ∧
      (∀ u ≤ t, ∀ j,
        |(rt_windowAdvTM.runFrom d u).workTapePos j - d.workTapePos j| ≤
          ((2 * s + ws.length + 2 : ℕ) : ℤ)) ∧
      rt_windowAdvTM.runFrom d t =
        rt_advanceCfg d 1 (List.replicate s false ++ true :: List.replicate s false)
          (.inr (.inr (.inr (.inr .done)))) := by
  let half := List.replicate s false
  let duration := 4 * ws.length + 2 * s + counterOverhead ws (s + 1) + 6
  let a : Cfg 3 Bool rt_halfState x := d.mapState (fun _ => .inl .sweep)
  have ae : a.state = some (.inl .sweep) := by simp [a, Cfg.mapState, entry]
  obtain ⟨arun, acut, ahead⟩ := rt_repeat_run [false] ws s value a ae radius blank
  have repeated : (List.replicate s [false]).flatten = half := by
    simp [half]
  simp only [List.length_singleton, Nat.mul_one, repeated] at arun acut ahead
  have durationEq : 4 * ws.length + s * (1 + 1) + counterOverhead ws (s + 1) + 6 =
      duration := by dsimp [duration]; omega
  rw [durationEq] at arun acut ahead
  have arun : (rt_repeatTM [false]).runFrom a duration =
      rt_advanceCfg a 1 half (.inr (.inr .done)) := by
    simpa only [rt_advanceCfg, half, List.length_replicate] using arun
  let a' := rt_advanceCfg a 1 half (.inr (.inr .done))
  let b := a'.mapState (fun _ => (Sum.inl () : Unit ⊕ Fin 2))
  have be : b.state = some (.inl ()) := rfl
  obtain ⟨brun, bcut, bhead⟩ := rt_writeReleased_run (1 : Fin 3) [true] b be
  change (seamReleaseTM (writeAdvTM 3 1 [true]) 0).runFrom b 2 =
    rt_advanceCfg b 1 [true] (.inr 0) at brun
  let b' := rt_advanceCfg b 1 [true] (.inr 0)
  let c := b'.mapState (fun _ => (Sum.inl .sweep : rt_halfState))
  have radiusC : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      c.workTapes 0 (c.workTapePos 0 + p) = FinTM.bufferTape ws p := by
    simpa [c, b', b, a', rt_advanceCfg, a, Cfg.mapState] using radius
  have blankC : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      c.workTapes 2 (c.workTapePos 2 + p) = none := by
    simpa [c, b', b, a', rt_advanceCfg, a, Cfg.mapState] using blank
  obtain ⟨crun, ccut, chead⟩ := rt_repeat_run [false] ws s value c rfl radiusC blankC
  simp only [List.length_singleton, Nat.mul_one, repeated, durationEq] at crun ccut chead
  have crun : (rt_repeatTM [false]).runFrom c duration =
      rt_advanceCfg c 1 half (.inr (.inr .done)) := by
    simpa only [rt_advanceCfg, half, List.length_replicate] using crun
  have posB (j : Fin 3) : b.workTapePos j =
      if j = 1 then d.workTapePos j + s else d.workTapePos j := by
    simp [b, a', rt_advanceCfg, a, Cfg.mapState, half, Function.update_apply]
    split_ifs with h
    · subst j; rfl
    · rfl
  have posC (j : Fin 3) : c.workTapePos j =
      if j = 1 then d.workTapePos j + s + 1 else d.workTapePos j := by
    simp only [c, b', rt_advanceCfg, Cfg.mapState, Function.update_apply,
      List.length_singleton, Nat.cast_one, posB]
    split_ifs with h
    · subst j; rfl
    · rfl
  let B : ℤ := (2 * s + ws.length + 2 : ℕ)
  have arad : ∀ u ≤ duration, ∀ j,
      |((rt_repeatTM [false]).runFrom a u).workTapePos j - d.workTapePos j| ≤ B := by
    intro u hu j
    exact (ahead u hu j).trans (by dsimp [B]; omega)
  have brad : ∀ u ≤ 2, ∀ j,
      |((seamReleaseTM (writeAdvTM 3 1 [true]) 0).runFrom b u).workTapePos j -
        d.workTapePos j| ≤ B := by
    intro u hu j
    have h := abs_le.mp (bhead u hu j)
    rw [posB] at h
    simp only [List.length_singleton, Nat.cast_one] at h
    split_ifs at h <;> exact abs_le.mpr ⟨by dsimp [B]; omega, by dsimp [B]; omega⟩
  have crad : ∀ u ≤ duration, ∀ j,
      |((rt_repeatTM [false]).runFrom c u).workTapePos j - d.workTapePos j| ≤ B := by
    intro u hu j
    have h := abs_le.mp (chead u hu j)
    rw [posC] at h
    split_ifs at h <;> exact abs_le.mpr ⟨by dsimp [B]; omega, by dsimp [B]; omega⟩
  obtain ⟨tailRun, tailCut, tailHeads⟩ := rt_copy_seam
    (seamReleaseTM (writeAdvTM 3 1 [true]) 0) (.inr 0)
    (rt_repeatTM [false]) (.inl .sweep) (.inr (.inr .done)) d.workTapePos B
    brun rfl bcut brad crun rfl ccut crad
  obtain ⟨run, cut, heads⟩ := rt_copy_seam (rt_repeatTM [false]) (.inr (.inr .done))
    (seamCompTM (seamReleaseTM (writeAdvTM 3 1 [true]) 0) (.inr 0)
      (rt_repeatTM [false]) (.inl .sweep)) (.inl (.inl ()))
    (.inr (.inr (.inr .done))) d.workTapePos B arun rfl acut arad
    tailRun rfl tailCut tailHeads
  have start : a.mapState Sum.inl = d := by
    apply Cfg.ext <;> simp [a, Cfg.mapState, entry]
  rw [start] at run cut heads
  have cost := counterOverhead_le ws
  rw [value] at cost
  refine ⟨duration + 1 + (2 + 1 + duration), by dsimp [duration]; omega, cut, heads, ?_⟩
  change rt_windowAdvTM.runFrom d _ = _ at run
  rw [run]
  have merged := rt_advanceCfg_append a 1 half [true] (.inr (.inr .done))
    (fun _ => (Sum.inl () : Unit ⊕ Fin 2)) (.inr 0)
  have merged' := rt_advanceCfg_append (a.mapState
    (fun _ => (Sum.inl () : Unit ⊕ Fin 2))) 1 (half ++ [true]) half (.inr 0)
    (fun _ => (Sum.inl .sweep : rt_halfState)) (.inr (.inr .done))
  dsimp only [c, b', b, a']
  rw [merged, merged']
  apply Cfg.ext <;> simp [rt_advanceCfg, Cfg.mapState, a, half, List.append_assoc]

/-- Finish the digit window by crossing its right delimiter and applying the
public backward skip, returning to the original destination head. -/
private def rt_windowTM :
    MultiTapeTM 3 Bool
      ((rt_halfState ⊕ ((Unit ⊕ Fin 2) ⊕ rt_halfState)) ⊕ (SeekPhase ⊕ SeekPhase)) :=
  seamCompTM rt_windowAdvTM (.inr (.inr (.inr (.inr .done))))
    (seamCompTM (skipTM 3 1) .done (skipBackTM 3 1) .run) (.inl .run)

/-- A complete digit-window writer with all three heads restored. Only the
destination window changes; source and scratch frames may be arbitrary.

**Proof sketch.** The advancing window writer leaves its head on the right
blank. Skip the empty word there, then skip back over the completed window.
The initial destination frame supplies both delimiters, even at radius zero.
The inherited R2 certificate gives the complete first-exit cut and envelope. -/
private theorem rt_window_run {x : List Bool} (ws : List Bool) (s : ℕ)
    (value : Nat.ofDigits 2 (ws.map Bool.toNat) = s)
    (d : Cfg 3 Bool
      ((rt_halfState ⊕ ((Unit ⊕ Fin 2) ⊕ rt_halfState)) ⊕ (SeekPhase ⊕ SeekPhase)) x)
    (entry : d.state = some (.inl (.inl (.inl .sweep))))
    (radius : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape ws p)
    (counter : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      d.workTapes 2 (d.workTapePos 2 + p) = none)
    (slot : ∀ p : ℤ, -1 ≤ p → p ≤ ((2 * s + 1 : ℕ) : ℤ) →
      d.workTapes 1 (d.workTapePos 1 + p) = none) :
    ∃ t ≤ 14 * (s + ws.length) + 27,
      (∀ u < t, (rt_windowTM.runFrom d u).state ≠ some (.inr (.inr .done))) ∧
      (∀ u ≤ t, ∀ j,
        |(rt_windowTM.runFrom d u).workTapePos j - d.workTapePos j| ≤
          ((2 * s + ws.length + 3 : ℕ) : ℤ)) ∧
      rt_windowTM.runFrom d t =
        { d with
          state := some (.inr (.inr .done))
          workTapes := fun j q =>
            if j = 1 ∧ d.workTapePos j ≤ q ∧
                q < d.workTapePos j + ((2 * s + 1 : ℕ) : ℤ)
            then FinTM.bufferTape
              (List.replicate s false ++ true :: List.replicate s false) (q - d.workTapePos j)
            else d.workTapes j q } := by
  let w := List.replicate s false ++ true :: List.replicate s false
  have length : w.length = 2 * s + 1 := by simp [w]; omega
  let a : Cfg 3 Bool (rt_halfState ⊕ ((Unit ⊕ Fin 2) ⊕ rt_halfState)) x :=
    d.mapState (fun _ => .inl (.inl .sweep))
  have ae : a.state = some (.inl (.inl .sweep)) := by simp [a, Cfg.mapState, entry]
  obtain ⟨t, cost, cutA, headsA, runA⟩ := rt_windowAdv_run ws s value a ae radius counter
  let a' := rt_advanceCfg a 1 w (.inr (.inr (.inr (.inr .done))))
  change rt_windowAdvTM.runFrom a t = a' at runA
  let b := a'.mapState (fun _ => SeekPhase.run)
  have bp : b.workTapePos 1 = d.workTapePos 1 + w.length := by
    simp [b, a', rt_advanceCfg, a, Cfg.mapState]
  have frame (p : ℤ) (lo : -1 ≤ p) (hi : p ≤ (w.length : ℤ)) :
      b.workTapes 1 (d.workTapePos 1 + p) = FinTM.bufferTape w p := by
    change (if (1 : Fin 3) = 1 ∧ d.workTapePos 1 ≤ d.workTapePos 1 + p ∧
        d.workTapePos 1 + p < d.workTapePos 1 + (w.length : ℤ)
      then FinTM.bufferTape w (d.workTapePos 1 + p - d.workTapePos 1)
      else d.workTapes 1 (d.workTapePos 1 + p)) = _
    by_cases interior : 0 ≤ p ∧ p < (w.length : ℤ)
    · rw [if_pos (by omega)]; congr 1; omega
    · rw [if_neg (by omega), slot p lo (by omega)]
      have edge : p = -1 ∨ p = (w.length : ℤ) := by omega
      rcases edge with rfl | rfl <;> simp [FinTM.bufferTape]
  have empty : ∀ p : ℤ, 0 ≤ p → p ≤ (([] : List Bool).length : ℤ) →
      b.workTapes 1 (b.workTapePos 1 + p) = FinTM.bufferTape [] p := by
    intro p lo hi
    have zero : p = 0 := by simp only [List.length_nil, Nat.cast_zero] at hi; omega
    subst p
    rw [bp, add_zero, frame _ (by omega) le_rfl]
    simp [FinTM.bufferTape]
  obtain ⟨runB, cutB, headsB⟩ := skipTM_run_ofCfg (1 : Fin 3) [] b rfl empty
  let b' : Cfg 3 Bool SeekPhase x := { b with
    state := some .done
    workTapePos := Function.update b.workTapePos 1 (b.workTapePos 1 + 1) }
  have runB : (skipTM 3 1).runFrom b 1 = b' := by
    simpa only [b', List.length_nil, Nat.cast_zero, add_zero] using runB
  let c := b'.mapState (fun _ => SeekPhase.run)
  have cp : c.workTapePos 1 = d.workTapePos 1 + w.length + 1 := by
    simp [c, b', Cfg.mapState, bp]
  obtain ⟨runC, cutC, headsC⟩ := skipBackTM_run_ofCfg (1 : Fin 3) w c rfl (by
    intro p lo hi
    change b.workTapes 1 (c.workTapePos 1 - w.length - 1 + p) = _
    rw [cp]
    convert frame p lo hi using 1; congr 1; omega)
  have otherB (j : Fin 3) (hj : j ≠ 1) : b.workTapePos j = d.workTapePos j := by
    simp [b, a', rt_advanceCfg, a, Cfg.mapState, hj]
  have otherC (j : Fin 3) (hj : j ≠ 1) : c.workTapePos j = d.workTapePos j := by
    simp [c, b', Cfg.mapState, hj, otherB j hj]
  let B : ℤ := (2 * s + ws.length + 3 : ℕ)
  have boundA : ∀ u ≤ t, ∀ j,
      |(rt_windowAdvTM.runFrom a u).workTapePos j - d.workTapePos j| ≤ B := by
    intro u hu j
    exact (headsA u hu j).trans (by dsimp [B]; omega)
  have boundB : ∀ u ≤ 1, ∀ j,
      |((skipTM 3 1).runFrom b u).workTapePos j - d.workTapePos j| ≤ B := by
    intro u hu j
    have h := headsB j u hu
    by_cases hj : j = 1
    · subst j
      simp only [if_true, Finset.mem_Icc, bp, List.length_nil, Nat.cast_zero,
        add_zero] at h
      exact abs_le.mpr ⟨by dsimp [B]; omega, by dsimp [B]; omega⟩
    · simp only [if_neg hj, otherB j hj] at h
      rw [h, sub_self, abs_zero]; dsimp only [B]; exact_mod_cast Nat.zero_le _
  have boundC : ∀ u ≤ w.length + 3, ∀ j,
      |((skipBackTM 3 1).runFrom c u).workTapePos j - d.workTapePos j| ≤ B := by
    intro u hu j
    have h := headsC j u hu
    by_cases hj : j = 1
    · subst j
      simp only [if_true, Finset.mem_Icc, cp] at h
      exact abs_le.mpr ⟨by dsimp [B]; omega, by dsimp [B]; omega⟩
    · simp only [if_neg hj, otherC j hj] at h
      rw [h, sub_self, abs_zero]; dsimp only [B]; exact_mod_cast Nat.zero_le _
  obtain ⟨tailRun, tailCut, tailHeads⟩ := rt_copy_seam (skipTM 3 1) .done
    (skipBackTM 3 1) .run .done d.workTapePos B runB rfl cutB boundB
    runC rfl cutC boundC
  obtain ⟨run, cut, heads⟩ := rt_copy_seam rt_windowAdvTM
    (.inr (.inr (.inr (.inr .done))))
    (seamCompTM (skipTM 3 1) .done (skipBackTM 3 1) .run) (.inl .run) (.inr .done)
    d.workTapePos B runA rfl cutA boundA tailRun rfl tailCut tailHeads
  have start : a.mapState Sum.inl = d := by
    apply Cfg.ext <;> simp [a, Cfg.mapState, entry]
  rw [start] at run cut heads
  refine ⟨t + 1 + (1 + 1 + (w.length + 3)), by omega, cut, heads, ?_⟩
  change rt_windowTM.runFrom d _ = _ at run
  rw [run]
  apply Cfg.ext
  · rfl
  · rfl
  · simp only [Cfg.mapState, c, b', b, a', rt_advanceCfg, a, length]
    rfl
  · funext j
    by_cases hj : j = 1
    · subst j
      simp only [Cfg.mapState, Function.update_self, cp]
      omega
    · simp only [Cfg.mapState, Function.update_of_ne hj, otherC j hj]
  · rfl

/-- The rich scan converts a completed digit window into unmarked tape cells.
All other symbols are left alone. -/
private def rt_windowCellMap {Q T : Type} : RecSym Q T → RecSym Q T
  | .digit b => .cell none b
  | γ => γ

set_option synthInstance.maxSize 256 in
/-- Map the completed window after the lifted Boolean pipeline has exited.
The selected tapes are a genuine Boolean lift throughout that first phase. -/
private def rt_cellWindowTM (Q T : Type) [DecidableEq Q] [DecidableEq T] :
    MultiTapeTM 3 (RecSym Q T)
      (((rt_halfState ⊕ ((Unit ⊕ Fin 2) ⊕ rt_halfState)) ⊕ (SeekPhase ⊕ SeekPhase)) ⊕
        ScanPhase Unit) :=
  seamCompTM (rt_windowTM.liftSymbols (RecSym.digitEmb Q T)) (.inr (.inr .done))
    (scanTM 3 1 (scanMap rt_windowCellMap) scanKeep ()) (.fwd ())

set_option synthInstance.maxSize 256 in
/-- On an isolated digit bank, write the window as `cell none` and restore
all heads, the radius word, temporary counter, native input and prior output.

**Proof sketch.** Transport the complete Boolean window run along `digitEmb`.
Its written slot is now a delimited digit word, so the public mapping scan
applies. The public scan-result identity identifies the cell word. R2 joins
these exact endpoints and first exits; the two stated envelopes suffice. -/
private theorem rt_cellWindow_run (Q T : Type) [DecidableEq Q] [DecidableEq T]
    {x : List Bool} (ws : List Bool) (s : ℕ)
    (value : Nat.ofDigits 2 (ws.map Bool.toNat) = s)
    (a : Cfg 3 Bool
      ((rt_halfState ⊕ ((Unit ⊕ Fin 2) ⊕ rt_halfState)) ⊕ (SeekPhase ⊕ SeekPhase)) x)
    (entry : a.state = some (.inl (.inl (.inl .sweep))))
    (radius : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      a.workTapes 0 (a.workTapePos 0 + p) = FinTM.bufferTape ws p)
    (counter : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      a.workTapes 2 (a.workTapePos 2 + p) = none)
    (slot : ∀ p : ℤ, -1 ≤ p → p ≤ ((2 * s + 1 : ℕ) : ℤ) →
      a.workTapes 1 (a.workTapePos 1 + p) = none) :
    let d := (a.liftSymbols (RecSym.digitEmb Q T)).mapState Sum.inl
    ∃ t ≤ 18 * (s + ws.length) + 32,
      (∀ u < t, ((rt_cellWindowTM Q T).runFrom d u).state ≠ some (.inr (.done ()))) ∧
      (∀ u ≤ t, ∀ j,
        |((rt_cellWindowTM Q T).runFrom d u).workTapePos j - d.workTapePos j| ≤
          ((2 * s + ws.length + 3 : ℕ) : ℤ)) ∧
      (rt_cellWindowTM Q T).runFrom d t =
        { d with
          state := some (.inr (.done ()))
          workTapes := fun j q =>
            if j = 1 ∧ d.workTapePos j ≤ q ∧
                q < d.workTapePos j + ((2 * s + 1 : ℕ) : ℤ)
            then FinTM.bufferTape
              ((List.replicate s false ++ true :: List.replicate s false).map
                (RecSym.cell none)) (q - d.workTapePos j)
            else d.workTapes j q } := by
  intro d
  let e := RecSym.digitEmb Q T
  let w := List.replicate s false ++ true :: List.replicate s false
  have length : w.length = 2 * s + 1 := by simp [w]; omega
  obtain ⟨t, cost, cut, heads, run⟩ := rt_window_run ws s value a entry radius counter slot
  let a' : Cfg 3 Bool
      ((rt_halfState ⊕ ((Unit ⊕ Fin 2) ⊕ rt_halfState)) ⊕ (SeekPhase ⊕ SeekPhase)) x :=
    { a with
    state := some (.inr (.inr .done))
    workTapes := fun j q =>
      if j = 1 ∧ a.workTapePos j ≤ q ∧ q < a.workTapePos j + (w.length : ℤ)
      then FinTM.bufferTape w (q - a.workTapePos j) else a.workTapes j q }
  have finish : rt_windowTM.runFrom a t = a' := by simpa only [a', length] using run
  have lifted : (rt_windowTM.liftSymbols e).runFrom (a.liftSymbols e) t =
      a'.liftSymbols e := by rw [MultiTapeTM.liftSymbols_runFrom, finish]
  let b := (a'.liftSymbols e).mapState (fun _ => ScanPhase.fwd ())
  have frame : ∀ p : ℤ, -1 ≤ p → p ≤ ((w.map e).length : ℤ) →
      b.workTapes 1 (b.workTapePos 1 + p) = FinTM.bufferTape (w.map e) p := by
    intro p lo hi
    simp only [List.length_map] at hi
    change (if (1 : Fin 3) = 1 ∧ a.workTapePos 1 ≤ a.workTapePos 1 + p ∧
        a.workTapePos 1 + p < a.workTapePos 1 + (w.length : ℤ)
      then FinTM.bufferTape w (a.workTapePos 1 + p - a.workTapePos 1)
      else a.workTapes 1 (a.workTapePos 1 + p)).map e = _
    rw [FinTM.bufferTape_map]
    by_cases interior : 0 ≤ p ∧ p < (w.length : ℤ)
    · rw [if_pos (by omega)]; congr 2; omega
    · rw [if_neg (by omega), slot p lo (by omega)]
      have edge : p = -1 ∨ p = (w.length : ℤ) := by omega
      rcases edge with rfl | rfl <;> simp [FinTM.bufferTape]
  obtain ⟨scan, scanCut, scanHeads⟩ := scanTM_run_ofCfg (1 : Fin 3)
    (scanMap rt_windowCellMap) scanKeep () (w.map e) b rfl frame
  rw [scanResult_map] at scan
  have mapped : (w.map e).map rt_windowCellMap = w.map (RecSym.cell none) := by
    simp [List.map_map, e, RecSym.digitEmb, rt_windowCellMap, Function.comp_def]
  simp only [List.length_map, mapped] at scan scanCut scanHeads
  let B : ℤ := (2 * s + ws.length + 3 : ℕ)
  have before : ∀ u < t,
      ((rt_windowTM.liftSymbols e).runFrom (a.liftSymbols e) u).state ≠
        some (.inr (.inr .done)) := by
    simpa only [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_state] using cut
  have radiusA : ∀ u ≤ t, ∀ j,
      |((rt_windowTM.liftSymbols e).runFrom (a.liftSymbols e) u).workTapePos j -
        a.workTapePos j| ≤ B := by
    simpa only [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_workTapePos] using heads
  have radiusB : ∀ u ≤ 2 * w.length + 2, ∀ j,
      |((scanTM 3 1 (scanMap rt_windowCellMap) scanKeep ()).runFrom b u).workTapePos j -
        a.workTapePos j| ≤ B := by
    intro u hu j
    have h := scanHeads j u hu
    change (if j = 1 then _ ∈ Finset.Icc (a.workTapePos j - 1)
      (a.workTapePos j + w.length) else _ = a.workTapePos j) at h
    split_ifs at h
    · have h := Finset.mem_Icc.mp h
      exact abs_le.mpr ⟨by dsimp [B]; omega, by dsimp [B]; omega⟩
    · rw [h, sub_self, abs_zero]; dsimp [B]; exact_mod_cast Nat.zero_le _
  obtain ⟨joined, first, bound⟩ := rt_copy_seam (rt_windowTM.liftSymbols e)
    (.inr (.inr .done)) (scanTM 3 1 (scanMap rt_windowCellMap) scanKeep ())
    (.fwd ()) (.done ()) a.workTapePos B lifted rfl before radiusA
    scan rfl (fun u hu => scanCut u hu ()) radiusB
  refine ⟨t + 1 + (2 * w.length + 2), by omega, first, bound, ?_⟩
  change (rt_cellWindowTM Q T).runFrom d _ = _ at joined
  rw [joined]
  apply Cfg.ext
  · rfl
  · rfl
  · funext j q
    simp only [Cfg.mapState, Cfg.liftSymbols, b, a', d, length]
    by_cases inside : j = 1 ∧ a.workTapePos j ≤ q ∧
        q < a.workTapePos j + ((2 * s + 1 : ℕ) : ℤ)
    · simp only [if_pos inside]; rfl
    · simp only [if_neg inside]; rfl
  · rfl
  · rfl

/-- A head envelope on a selected bank extends to the rich host. R1 keeps
unselected heads fixed, and its selected-head projection is exact.

**Proof sketch.** For a selected tape, transport both head positions. On an
unselected tape, the public frame contract at the current time and at zero
identifies both positions with the same ambient head. -/
private theorem rt_embed_radius {Γ S : Type*} {m k : ℕ} {x : List Γ}
    (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Γ S)
    (tapes : Fin k → ℤ → Option Γ) (heads : Fin k → ℤ) (pre : List Γ)
    (a : Cfg m Γ S x) (t : ℕ) (B : ℤ) (nonneg : 0 ≤ B)
    (bound : ∀ u ≤ t, ∀ i, |(M.runFrom a u).workTapePos i - a.workTapePos i| ≤ B) :
    let d := embedEmitCfg ι tapes heads pre a
    ∀ u ≤ t, ∀ j,
      |((embedEmitTM ι M).runFrom d u).workTapePos j - d.workTapePos j| ≤ B := by
  intro d u hu j
  rcases em (∃ i, ι i = j) with ⟨i, rfl⟩ | outside
  · change |((embedEmitTM ι M).runFrom (embedEmitCfg ι tapes heads pre a) u).workTapePos
      (ι i) - (embedEmitCfg ι tapes heads pre a).workTapePos (ι i)| ≤ B
    rw [embedEmitTM_runFrom, embedEmitCfg_selected_pos, embedEmitCfg_selected_pos]
    exact bound u hu i
  · have fixed (v : ℕ) : ((embedEmitTM ι M).runFrom d v).workTapePos j = heads j :=
      ((embedEmitTM_frame ι M tapes heads pre a v).1 j outside).2
    have initial : d.workTapePos j = heads j := fixed 0
    rw [fixed u, initial, sub_self, abs_zero]
    exact nonneg

set_option synthInstance.maxSize 256 in
/-- The complete cell-window phase on an isolated three-tape bank in an
arbitrary rich host. Unselected tapes and the prior rich output are preserved.
The source bank is explicitly a Boolean lift, never a decoding of rich tape.

**Proof sketch.** Embed `rt_cellWindow_run` through the public R1 lockstep
contract, with the caller's output as the forwarding prefix. State and
endpoint transport are exact; `rt_embed_radius` supplies all host-head bounds. -/
private theorem rt_cellWindow_embed_run (Q T : Type) [DecidableEq Q] [DecidableEq T]
    {k : ℕ} (ι : Fin 3 ↪ Fin k) {x : List Bool} (ws : List Bool) (s : ℕ)
    (value : Nat.ofDigits 2 (ws.map Bool.toNat) = s)
    (a : Cfg 3 Bool
      ((rt_halfState ⊕ ((Unit ⊕ Fin 2) ⊕ rt_halfState)) ⊕ (SeekPhase ⊕ SeekPhase)) x)
    (entry : a.state = some (.inl (.inl (.inl .sweep))))
    (radius : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      a.workTapes 0 (a.workTapePos 0 + p) = FinTM.bufferTape ws p)
    (counter : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      a.workTapes 2 (a.workTapePos 2 + p) = none)
    (slot : ∀ p : ℤ, -1 ≤ p → p ≤ ((2 * s + 1 : ℕ) : ℤ) →
      a.workTapes 1 (a.workTapePos 1 + p) = none)
    (output : a.output = [])
    (tapes : Fin k → ℤ → Option (RecSym Q T)) (heads : Fin k → ℤ)
    (pre : List (RecSym Q T)) :
    let b := (a.liftSymbols (RecSym.digitEmb Q T)).mapState Sum.inl
    let d := embedEmitCfg ι tapes heads pre b
    ∃ t ≤ 18 * (s + ws.length) + 32,
      (∀ u < t,
        ((embedEmitTM ι (rt_cellWindowTM Q T)).runFrom d u).state ≠ some (.inr (.done ()))) ∧
      (∀ u ≤ t, ∀ j,
        |((embedEmitTM ι (rt_cellWindowTM Q T)).runFrom d u).workTapePos j -
          d.workTapePos j| ≤ ((2 * s + ws.length + 3 : ℕ) : ℤ)) ∧
      (embedEmitTM ι (rt_cellWindowTM Q T)).runFrom d t =
        embedEmitCfg ι tapes heads pre
          { b with
            state := some (.inr (.done ()))
            workTapes := fun j q =>
              if j = 1 ∧ b.workTapePos j ≤ q ∧
                  q < b.workTapePos j + ((2 * s + 1 : ℕ) : ℤ)
              then FinTM.bufferTape
                ((List.replicate s false ++ true :: List.replicate s false).map
                  (RecSym.cell none)) (q - b.workTapePos j)
              else b.workTapes j q } ∧
      ((embedEmitTM ι (rt_cellWindowTM Q T)).runFrom d t).output = pre := by
  intro b d
  obtain ⟨t, cost, first, bound, finish⟩ :=
    rt_cellWindow_run Q T ws s value a entry radius counter slot
  have endrun := embedEmitTM_runFrom ι (rt_cellWindowTM Q T) tapes heads pre b t
  rw [finish] at endrun
  refine ⟨t, cost, ?_, ?_, endrun, ?_⟩
  · intro u hu
    change ((embedEmitTM ι (rt_cellWindowTM Q T)).runFrom
      (embedEmitCfg ι tapes heads pre b) u).state ≠ _
    rw [embedEmitTM_runFrom]
    exact first u hu
  · exact rt_embed_radius ι (rt_cellWindowTM Q T) tapes heads pre b t _
      (by positivity) bound
  · rw [endrun]
    simp [embedEmitCfg, Cfg.mapState, Cfg.liftSymbols, output]

/-- Identify a forwarding configuration by its selected bank and ambient
frame, using only the public R1 projections. -/
private theorem rt_embed_matches {Γ S : Type*} {m k : ℕ} {x : List Γ}
    (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Γ S)
    (tapes : Fin k → ℤ → Option Γ) (heads : Fin k → ℤ) (pre : List Γ)
    (a : Cfg m Γ S x) (d : Cfg k Γ S x)
    (state : a.state = d.state) (input : a.inputPos = d.inputPos)
    (bank : ∀ i, a.workTapes i = d.workTapes (ι i))
    (positions : ∀ i, a.workTapePos i = d.workTapePos (ι i))
    (outside : ∀ j, j ∉ Set.range ι → tapes j = d.workTapes j ∧ heads j = d.workTapePos j)
    (output : pre ++ a.output = d.output) : embedEmitCfg ι tapes heads pre a = d := by
  apply Cfg.ext
  · exact state
  · exact input
  · funext j
    rcases em (j ∈ Set.range ι) with ⟨i, rfl⟩ | off
    · rw [embedEmitCfg_selected_tape]; exact bank i
    · exact (((embedEmitTM_frame ι M tapes heads pre a 0).1 j off).1).trans
        (outside j off).1
  · funext j
    rcases em (j ∈ Set.range ι) with ⟨i, rfl⟩ | off
    · rw [embedEmitCfg_selected_pos]; exact positions i
    · exact (((embedEmitTM_frame ι M tapes heads pre a 0).1 j off).2).trans
        (outside j off).2
  · exact output

/-- The inherited bound writer starts on any globally blank selected bank
of a rich configuration; no purity condition is imposed on unselected tapes.
Its endpoint is stated directly on the host, with every other field restored.

**Proof sketch.** Build an actual blank Boolean source bank with the selected
head origins and empty output. Its lift and forwarding frame equal the given
host by `rt_embed_matches`. Invoke `rt_exists_digitBoundTM`, then identify the
transported endpoint by the same public projections. The binary bound is the
only selected-tape change, and all unselected rich cells stay in the frame. -/
private theorem rt_exists_cleanDigitBoundTM (Q T : Type) [DecidableEq Q] [DecidableEq T] :
    ∃ (K : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (R : MultiTapeTM (K + 1) (RecSym Q T) S) (entry exit : S) (C : ℕ),
      ∀ {k : ℕ} (ι : Fin (K + 1) ↪ Fin k) {x : List Bool}
        (d : Cfg k (RecSym Q T) S (x.map (RecSym.digitEmb Q T))),
        d.state = some entry → d.inputPos = 1 →
        (∀ i p, d.workTapes (ι i) p = none) →
      ∃ t ≤ C * (x.length + 1),
        (∀ u < t, ((embedEmitTM ι R).runFrom d u).state ≠ some exit) ∧
        (∀ u ≤ t, ∀ j,
          |((embedEmitTM ι R).runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * ((x.length + 1).bits.length + 1) : ℕ) : ℤ)) ∧
        (embedEmitTM ι R).runFrom d t =
          {d with
            state := some exit
            workTapes := fun j p => if j = ι 0 then
              FinTM.bufferTape ((x.length + 1).bits.map RecSym.digit) (p - d.workTapePos j)
              else d.workTapes j p} := by
  obtain ⟨K, S, hfin, heq, R, en, ex, C, bound⟩ := rt_exists_digitBoundTM Q T
  refine ⟨K, S, hfin, heq, R, en, ex, C, ?_⟩
  intro k ι x d state input blank
  let e := RecSym.digitEmb Q T
  let a : Cfg (K + 1) Bool S x :=
    { state := some en, inputPos := 1, workTapes := fun _ _ => none,
      workTapePos := fun i => d.workTapePos (ι i), output := [] }
  have initial : embedEmitCfg ι d.workTapes d.workTapePos d.output (a.liftSymbols e) = d := by
    apply rt_embed_matches ι R
    · exact state.symm
    · rw [input]; rfl
    · intro i; funext p
      simp [a, Cfg.liftSymbols, blank]
    · intro i; rfl
    · intro j _; exact ⟨rfl, rfl⟩
    · simp [a, Cfg.liftSymbols]
  obtain ⟨t, cost, first, heads, run⟩ := bound ι a rfl rfl (fun _ _ => rfl) rfl
    d.workTapes d.workTapePos d.output
  rw [initial] at first heads run
  refine ⟨t, cost, first, heads, ?_⟩
  rw [run]
  apply rt_embed_matches ι R
  · rfl
  · rw [input]; rfl
  · intro i; funext p
    change (if i = 0 then FinTM.bufferTape (x.length + 1).bits (p - d.workTapePos (ι i))
      else none).map e = if ι i = ι 0 then _ else d.workTapes (ι i) p
    by_cases zero : i = 0
    · subst i
      simp only [if_true]
      exact (FinTM.bufferTape_map e _ _).symm
    · rw [if_neg zero, if_neg (fun h => zero (ι.injective h)), blank]
      rfl
  · intro i; rfl
  · intro j off
    have ne : j ≠ ι 0 := by intro h; exact off ⟨0, h.symm⟩
    exact ⟨by funext p; simp only [if_neg ne], rfl⟩
  · simp [a, Cfg.liftSymbols]

/-- Move a delimited word to a distinct tape, clearing its source. Both
public sweeps return their heads; one R2 seam intercepts the copy exit. -/
private def rt_moveWordTM {Γ : Type*} (k : ℕ) (src dst : Fin k) :
    MultiTapeTM k Γ (SweepPhase ⊕ SweepPhase) :=
  seamCompTM (copyTM k src dst) .done (clearTM k src) .sweep

/-- Copy and clear a framed word, preserving arbitrary surrounding symbols.
This connects either scratch field to the rich destination without using a
Boolean lift on a tape that may contain foreign symbols.

**Proof sketch.** The public copy leaves the source frame intact, so the
public clear applies immediately. Their exact endpoints give the two disjoint
write masks, and their envelopes and first exits compose by the inherited
R2 certificate. No destination-blank assumption is needed by either sweep. -/
private theorem rt_moveWord_run {Γ : Type*} {k : ℕ} {x : List Γ}
    (src dst : Fin k) (different : src ≠ dst) (w : List Γ)
    (d : Cfg k Γ (SweepPhase ⊕ SweepPhase) x) (entry : d.state = some (.inl .sweep))
    (frame : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p) :
    (rt_moveWordTM k src dst).runFrom d (4 * w.length + 5) =
      { d with
        state := some (.inr .done)
        workTapes := fun j p =>
          if j = src ∧ d.workTapePos j ≤ p ∧ p < d.workTapePos j + (w.length : ℤ)
          then none
          else if j = dst ∧ d.workTapePos j ≤ p ∧ p < d.workTapePos j + (w.length : ℤ)
          then FinTM.bufferTape w (p - d.workTapePos j) else d.workTapes j p } ∧
    (∀ u < 4 * w.length + 5,
      ((rt_moveWordTM k src dst).runFrom d u).state ≠ some (.inr .done)) ∧
    (∀ u ≤ 4 * w.length + 5, ∀ j,
      |((rt_moveWordTM k src dst).runFrom d u).workTapePos j - d.workTapePos j| ≤
        (w.length : ℤ) + 1) := by
  let a := d.mapState (fun _ => SweepPhase.sweep)
  have ae : a.state = some .sweep := by simp [a, Cfg.mapState, entry]
  obtain ⟨copy, copyCut, copyHeads⟩ := copyTM_run_ofCfg src dst different w a ae frame
  let b : Cfg k Γ SweepPhase x :=
    { a with
      state := some .sweep
      workTapes := fun j p =>
        if j = dst ∧ a.workTapePos j ≤ p ∧ p < a.workTapePos j + (w.length : ℤ)
        then FinTM.bufferTape w (p - a.workTapePos j) else a.workTapes j p }
  have source : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      b.workTapes src (b.workTapePos src + p) = FinTM.bufferTape w p := by
    intro p lo hi
    simpa only [b, a, Cfg.mapState, different, false_and, if_false] using frame p lo hi
  obtain ⟨clear, clearCut, clearHeads⟩ := clearTM_run_ofCfg src w b rfl source
  have radCopy : ∀ u ≤ 2 * w.length + 2, ∀ j,
      |((copyTM k src dst).runFrom a u).workTapePos j - d.workTapePos j| ≤
        (w.length : ℤ) + 1 := by
    intro u hu j
    have h := copyHeads j u hu
    change (if j = src ∨ j = dst then _ ∈ Finset.Icc
      (d.workTapePos j - 1) (d.workTapePos j + w.length) else _ = d.workTapePos j) at h
    split_ifs at h
    · have h := Finset.mem_Icc.mp h
      exact abs_le.mpr ⟨by omega, by omega⟩
    · rw [h, sub_self, abs_zero]; positivity
  have radClear : ∀ u ≤ 2 * w.length + 2, ∀ j,
      |((clearTM k src).runFrom b u).workTapePos j - d.workTapePos j| ≤
        (w.length : ℤ) + 1 := by
    intro u hu j
    have h := clearHeads j u hu
    change (if j = src then _ ∈ Finset.Icc
      (d.workTapePos j - 1) (d.workTapePos j + w.length) else _ = d.workTapePos j) at h
    split_ifs at h
    · have h := Finset.mem_Icc.mp h
      exact abs_le.mpr ⟨by omega, by omega⟩
    · rw [h, sub_self, abs_zero]; positivity
  obtain ⟨run, first, heads⟩ := rt_copy_seam (copyTM k src dst) .done
    (clearTM k src) .sweep .done d.workTapePos ((w.length : ℤ) + 1)
    copy rfl copyCut radCopy clear rfl clearCut radClear
  have start : a.mapState Sum.inl = d := by
    apply Cfg.ext <;> simp [a, Cfg.mapState, entry]
  have time : 2 * w.length + 2 + 1 + (2 * w.length + 2) = 4 * w.length + 5 := by omega
  rw [start, time] at run first heads
  exact ⟨run, first, heads⟩

/-- Finite control of the isolated cell-window phase. -/
private abbrev rt_cellWindowState :=
  (((rt_halfState ⊕ ((Unit ⊕ Fin 2) ⊕ rt_halfState)) ⊕ (SeekPhase ⊕ SeekPhase)) ⊕
    ScanPhase Unit)

set_option synthInstance.maxSize 256 in
/-- A rich host whose selected bank holds exactly one digit radius word can
run the isolated cell-window writer. The destination is selected tape one;
all other host cells, heads, input position and output are restored.

**Proof sketch.** The globally specified bank is the lift of an explicit
Boolean bank, with its native input position copied by value. Identify the
entry and endpoint by `rt_embed_matches`, around the proved R1 window run.
Unselected rich symbols never enter the Boolean bank. -/
private theorem rt_cellWindow_ready_run (Q T : Type) [DecidableEq Q] [DecidableEq T]
    {k : ℕ} (ι : Fin 3 ↪ Fin k) {x : List Bool} (ws : List Bool) (s : ℕ)
    (value : Nat.ofDigits 2 (ws.map Bool.toNat) = s)
    (d : Cfg k (RecSym Q T) rt_cellWindowState (x.map (RecSym.digitEmb Q T)))
    (entry : d.state = some (.inl (.inl (.inl (.inl .sweep)))))
    (bank : ∀ i p, d.workTapes (ι i) p =
      if i = 0 then FinTM.bufferTape (ws.map RecSym.digit) (p - d.workTapePos (ι i))
      else none) :
    ∃ t ≤ 18 * (s + ws.length) + 32,
      (∀ u < t,
        ((embedEmitTM ι (rt_cellWindowTM Q T)).runFrom d u).state ≠ some (.inr (.done ()))) ∧
      (∀ u ≤ t, ∀ j,
        |((embedEmitTM ι (rt_cellWindowTM Q T)).runFrom d u).workTapePos j -
          d.workTapePos j| ≤ ((2 * s + ws.length + 3 : ℕ) : ℤ)) ∧
      (embedEmitTM ι (rt_cellWindowTM Q T)).runFrom d t =
        { d with
          state := some (.inr (.done ()))
          workTapes := fun j p =>
            if j = ι 1 ∧ d.workTapePos j ≤ p ∧
                p < d.workTapePos j + ((2 * s + 1 : ℕ) : ℤ)
            then FinTM.bufferTape
              ((List.replicate s false ++ true :: List.replicate s false).map
                (RecSym.cell none)) (p - d.workTapePos j)
            else d.workTapes j p } := by
  let e := RecSym.digitEmb Q T
  let a : Cfg 3 Bool
      ((rt_halfState ⊕ ((Unit ⊕ Fin 2) ⊕ rt_halfState)) ⊕ (SeekPhase ⊕ SeekPhase)) x :=
    { state := some (.inl (.inl (.inl .sweep))),
      inputPos := ⟨d.inputPos.val, by simpa using d.inputPos.isLt⟩,
      workTapes := fun i p =>
        if i = 0 then FinTM.bufferTape ws (p - d.workTapePos (ι i)) else none,
      workTapePos := fun i => d.workTapePos (ι i), output := [] }
  let b := (a.liftSymbols e).mapState (Sum.inl : _ → rt_cellWindowState)
  have selected (i : Fin 3) : b.workTapes i = d.workTapes (ι i) := by
    funext p
    rw [bank]
    change (if i = 0 then FinTM.bufferTape ws (p - d.workTapePos (ι i))
      else none).map e = _
    split_ifs
    · exact (FinTM.bufferTape_map e _ _).symm
    · rfl
  have initial : embedEmitCfg ι d.workTapes d.workTapePos d.output b = d := by
    apply rt_embed_matches ι (rt_cellWindowTM Q T)
    · exact entry.symm
    · apply Fin.ext; rfl
    · exact selected
    · intro i; rfl
    · intro j _; exact ⟨rfl, rfl⟩
    · simp [b, a, Cfg.mapState, Cfg.liftSymbols]
  have radius : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      a.workTapes 0 (a.workTapePos 0 + p) = FinTM.bufferTape ws p := by
    intro p _ _
    change (if (0 : Fin 3) = 0 then
      FinTM.bufferTape ws (d.workTapePos (ι 0) + p - d.workTapePos (ι 0)) else none) = _
    rw [if_pos rfl]; congr 1; omega
  obtain ⟨t, cost, first, heads, run, _⟩ := rt_cellWindow_embed_run Q T ι ws s value a
    rfl radius (by intro p _ _; rfl) (by intro p _ _; rfl) rfl
    d.workTapes d.workTapePos d.output
  change (embedEmitTM ι (rt_cellWindowTM Q T)).runFrom
    (embedEmitCfg ι d.workTapes d.workTapePos d.output b) t = _ at run
  rw [initial] at run first heads
  refine ⟨t, cost, first, heads, ?_⟩
  rw [run]
  apply rt_embed_matches ι (rt_cellWindowTM Q T)
  · rfl
  · apply Fin.ext; rfl
  · intro i; funext p
    change (if i = 1 ∧ d.workTapePos (ι i) ≤ p ∧
        p < d.workTapePos (ι i) + ((2 * s + 1 : ℕ) : ℤ)
      then _ else b.workTapes i p) =
      if ι i = ι 1 ∧ d.workTapePos (ι i) ≤ p ∧
        p < d.workTapePos (ι i) + ((2 * s + 1 : ℕ) : ℤ)
      then _ else d.workTapes (ι i) p
    simp only [ι.injective.eq_iff, selected]
    rfl
  · intro i; rfl
  · intro j off
    have ne : j ≠ ι 1 := by intro h; exact off ⟨1, h.symm⟩
    exact ⟨by funext p; simp only [ne, false_and, if_false], rfl⟩
  · simp [a, Cfg.mapState, Cfg.liftSymbols]

/-- A buffer is already blank outside its written interval. -/
private theorem rt_bufferMask {Γ : Type*} (w : List Γ) (o p : ℤ) :
    (if o ≤ p ∧ p < o + (w.length : ℤ)
      then FinTM.bufferTape w (p - o) else none) = FinTM.bufferTape w (p - o) := by
  by_cases inside : o ≤ p ∧ p < o + (w.length : ℤ)
  · rw [if_pos inside]
  · rw [if_neg inside]
    unfold FinTM.bufferTape
    split_ifs with nonneg
    · exact (List.getElem?_eq_none (by omega)).symm
    · rfl

/-- Control of the rich window phase, including its scratch preparation and
cleanup. Every transition between rows is a public R2 seam. -/
private abbrev rt_richWindowState :=
  SweepPhase ⊕ (rt_cellWindowState ⊕ ((SweepPhase ⊕ SweepPhase) ⊕ SweepPhase))

set_option synthInstance.maxSize 512 in
/-- Copy the caller's radius onto an isolated bank, write and map the window,
move it to the caller's destination, and clear the copied radius. -/
private def rt_richWindowTM (Q T : Type) [DecidableEq Q] [DecidableEq T]
    (k : ℕ) (radius dst : Fin k) (ι : Fin 3 ↪ Fin k) :
    MultiTapeTM k (RecSym Q T) rt_richWindowState :=
  seamCompTM (copyTM k radius (ι 0)) .done
    (seamCompTM (embedEmitTM ι (rt_cellWindowTM Q T)) (.inr (.done ()))
      (seamCompTM (rt_moveWordTM k (ι 1) dst) (.inr .done)
        (clearTM k (ι 0)) .sweep) (.inl (.inl .sweep)))
    (.inl (.inl (.inl (.inl (.inl .sweep)))))

set_option synthInstance.maxSize 512 in
/-- Write a rich cell window from a framed radius, using a clean three-tape
bank disjoint from the caller's source and destination. Every scratch cell
and every head is restored, even for the empty radius word.

**Proof sketch.** Copy the radius into the blank bank and identify it globally
as a pure digit buffer. Apply the isolated cell-window contract, then move its
window to the destination and clear the copied radius. R2 composes the four
first exits and envelopes. The two cleared bank intervals cancel against the
original blank bank; every other host cell is framed throughout. -/
private theorem rt_richWindow_run (Q T : Type) [DecidableEq Q] [DecidableEq T]
    {k : ℕ} (src dst : Fin k) (ι : Fin 3 ↪ Fin k)
    (sourceOutside : src ∉ Set.range ι) (destOutside : dst ∉ Set.range ι)
    {x : List Bool} (ws : List Bool) (s : ℕ)
    (value : Nat.ofDigits 2 (ws.map Bool.toNat) = s)
    (d : Cfg k (RecSym Q T) rt_richWindowState (x.map (RecSym.digitEmb Q T)))
    (entry : d.state = some (.inl .sweep))
    (radius : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape (ws.map RecSym.digit) p)
    (blank : ∀ i p, d.workTapes (ι i) p = none) :
    ∃ t ≤ 26 * (s + ws.length) + 48,
      (∀ u < t, ((rt_richWindowTM Q T k src dst ι).runFrom d u).state ≠
        some (.inr (.inr (.inr .done)))) ∧
      (∀ u ≤ t, ∀ j,
        |((rt_richWindowTM Q T k src dst ι).runFrom d u).workTapePos j -
          d.workTapePos j| ≤ ((2 * s + ws.length + 3 : ℕ) : ℤ)) ∧
      (rt_richWindowTM Q T k src dst ι).runFrom d t =
        { d with
          state := some (.inr (.inr (.inr .done)))
          workTapes := fun j p =>
            if j = dst ∧ d.workTapePos j ≤ p ∧
                p < d.workTapePos j + ((2 * s + 1 : ℕ) : ℤ)
            then FinTM.bufferTape
              ((List.replicate s false ++ true :: List.replicate s false).map
                (RecSym.cell none)) (p - d.workTapePos j)
            else d.workTapes j p } := by
  let w : List (RecSym Q T) :=
    (List.replicate s false ++ true :: List.replicate s false).map (RecSym.cell none)
  have length : w.length = 2 * s + 1 := by simp [w]; omega
  have srcNe : src ≠ ι 0 := by intro h; exact sourceOutside ⟨0, h.symm⟩
  have dstNe (i : Fin 3) : ι i ≠ dst := by intro h; exact destOutside ⟨i, h⟩
  have bankNe : ι 0 ≠ ι 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (ι.injective h)
  let a := d.mapState (fun _ => SweepPhase.sweep)
  have ae : a.state = some .sweep := by simp [a, Cfg.mapState, entry]
  obtain ⟨copy, copyCut, copyHeads⟩ :=
    copyTM_run_ofCfg src (ι 0) srcNe (ws.map RecSym.digit) a ae (by simpa using radius)
  simp only [List.length_map] at copy copyCut copyHeads
  let a' : Cfg k (RecSym Q T) SweepPhase (x.map (RecSym.digitEmb Q T)) :=
    { a with
      state := some .done
      workTapes := fun j p =>
        if j = ι 0 ∧ d.workTapePos j ≤ p ∧ p < d.workTapePos j + (ws.length : ℤ)
        then FinTM.bufferTape (ws.map RecSym.digit) (p - d.workTapePos j)
        else d.workTapes j p }
  change (copyTM k src (ι 0)).runFrom a (2 * ws.length + 2) = a' at copy
  let b := a'.mapState (fun _ =>
    (.inl (.inl (.inl (.inl .sweep))) : rt_cellWindowState))
  have bank (i : Fin 3) (p : ℤ) : b.workTapes (ι i) p =
      if i = 0 then FinTM.bufferTape (ws.map RecSym.digit) (p - b.workTapePos (ι i))
      else none := by
    change (if ι i = ι 0 ∧ d.workTapePos (ι i) ≤ p ∧
      p < d.workTapePos (ι i) + (ws.length : ℤ) then _ else d.workTapes (ι i) p) = _
    simp only [ι.injective.eq_iff, blank]
    by_cases zero : i = 0
    · subst i
      simp only [true_and, if_true]
      simpa only [List.length_map] using rt_bufferMask (ws.map RecSym.digit)
        (d.workTapePos (ι 0)) p
    · simp [zero]
  obtain ⟨t, cost, windowCut, windowHeads, window⟩ :=
    rt_cellWindow_ready_run Q T ι ws s value b rfl bank
  let c : Cfg k (RecSym Q T) rt_cellWindowState (x.map (RecSym.digitEmb Q T)) :=
    { b with
      state := some (.inr (.done ()))
      workTapes := fun j p =>
        if j = ι 1 ∧ d.workTapePos j ≤ p ∧ p < d.workTapePos j + (w.length : ℤ)
        then FinTM.bufferTape w (p - d.workTapePos j) else b.workTapes j p }
  have win : (embedEmitTM ι (rt_cellWindowTM Q T)).runFrom b t = c := by
    simpa only [c, length] using window
  let f := c.mapState (fun _ => (Sum.inl SweepPhase.sweep : SweepPhase ⊕ SweepPhase))
  have wf : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      f.workTapes (ι 1) (f.workTapePos (ι 1) + p) = FinTM.bufferTape w p := by
    intro p _ _
    change (if ι 1 = ι 1 ∧ d.workTapePos (ι 1) ≤ d.workTapePos (ι 1) + p ∧
        d.workTapePos (ι 1) + p < d.workTapePos (ι 1) + (w.length : ℤ)
      then FinTM.bufferTape w (d.workTapePos (ι 1) + p - d.workTapePos (ι 1))
      else b.workTapes (ι 1) (d.workTapePos (ι 1) + p)) = _
    rw [bank]; simp only [show (1 : Fin 3) ≠ 0 by decide, if_false, true_and]
    rw [rt_bufferMask]; congr 1; omega
  obtain ⟨move, moveCut, moveHeads⟩ := rt_moveWord_run (ι 1) dst (dstNe 1) w f rfl wf
  let f' := (rt_moveWordTM k (ι 1) dst).runFrom f (4 * w.length + 5)
  let g := f'.mapState (fun _ => SweepPhase.sweep)
  have ge : g.state = some .sweep := by simp [g, f', move, Cfg.mapState]
  have gp : g.workTapePos = d.workTapePos := by
    simp only [g, f', move, f, c, b, a', a, Cfg.mapState]
  have gf : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      g.workTapes (ι 0) (g.workTapePos (ι 0) + p) =
        FinTM.bufferTape (ws.map RecSym.digit) p := by
    intro p _ _
    simp only [g, f', move, Cfg.mapState, f, c, bankNe, dstNe, false_and, if_false]
    rw [bank]
    simp only [if_true]
    congr 1; omega
  obtain ⟨clear, clearCut, clearHeads⟩ := clearTM_run_ofCfg (ι 0) (ws.map RecSym.digit) g ge
    (by simpa only [List.length_map] using gf)
  simp only [List.length_map] at clear clearCut clearHeads
  let B : ℤ := (2 * s + ws.length + 3 : ℕ)
  have radA : ∀ u ≤ 2 * ws.length + 2, ∀ j,
      |((copyTM k src (ι 0)).runFrom a u).workTapePos j - d.workTapePos j| ≤ B := by
    intro u hu j
    have h := copyHeads j u hu
    change (if j = src ∨ j = ι 0 then _ ∈ Finset.Icc
      (d.workTapePos j - 1) (d.workTapePos j + ws.length) else _ = d.workTapePos j) at h
    split_ifs at h
    · have h := Finset.mem_Icc.mp h
      exact abs_le.mpr ⟨by dsimp [B]; omega, by dsimp [B]; omega⟩
    · rw [h, sub_self, abs_zero]; dsimp [B]; positivity
  have radF : ∀ u ≤ 4 * w.length + 5, ∀ j,
      |((rt_moveWordTM k (ι 1) dst).runFrom f u).workTapePos j - d.workTapePos j| ≤ B := by
    intro u hu j
    exact (moveHeads u hu j).trans (by dsimp [B]; omega)
  have radG : ∀ u ≤ 2 * ws.length + 2, ∀ j,
      |((clearTM k (ι 0)).runFrom g u).workTapePos j - d.workTapePos j| ≤ B := by
    intro u hu j
    have h := clearHeads j u hu
    rw [gp] at h
    split_ifs at h
    · have h := Finset.mem_Icc.mp h
      exact abs_le.mpr ⟨by dsimp [B]; omega, by dsimp [B]; omega⟩
    · rw [h, sub_self, abs_zero]; dsimp [B]; positivity
  obtain ⟨tailRun, tailCut, tailHeads⟩ := rt_copy_seam (rt_moveWordTM k (ι 1) dst)
    (.inr .done) (clearTM k (ι 0)) .sweep .done d.workTapePos B
    (show (rt_moveWordTM k (ι 1) dst).runFrom f _ = f' from rfl)
    (by simp [f', move]) moveCut radF clear rfl clearCut radG
  obtain ⟨middleRun, middleCut, middleHeads⟩ := rt_copy_seam
    (embedEmitTM ι (rt_cellWindowTM Q T)) (.inr (.done ()))
    (seamCompTM (rt_moveWordTM k (ι 1) dst) (.inr .done) (clearTM k (ι 0)) .sweep)
    (.inl (.inl .sweep)) (.inr .done) d.workTapePos B
    win rfl windowCut windowHeads tailRun rfl tailCut tailHeads
  obtain ⟨run, first, heads⟩ := rt_copy_seam (copyTM k src (ι 0)) .done
    (seamCompTM (embedEmitTM ι (rt_cellWindowTM Q T)) (.inr (.done ()))
      (seamCompTM (rt_moveWordTM k (ι 1) dst) (.inr .done) (clearTM k (ι 0)) .sweep)
        (.inl (.inl .sweep)))
    (.inl (.inl (.inl (.inl (.inl .sweep))))) (.inr (.inr .done)) d.workTapePos B
    copy rfl copyCut radA middleRun rfl middleCut middleHeads
  have start : a.mapState Sum.inl = d := by
    apply Cfg.ext <;> simp [a, Cfg.mapState, entry]
  rw [start] at run first heads
  refine ⟨_, by omega, first, heads, ?_⟩
  change (rt_richWindowTM Q T k src dst ι).runFrom d _ = _ at run
  rw [run]
  apply Cfg.ext
  · rfl
  · simp only [g, f', move, f, c, b, a', a, Cfg.mapState]
  · funext j p
    simp only [g, f', move, f, c, b, a', a, Cfg.mapState, length]
    by_cases j0 : j = ι 0
    · subst j
      simp only [bankNe, dstNe, false_and, if_false, true_and]
      rw [blank]
      split_ifs <;> rfl
    · by_cases j1 : j = ι 1
      · subst j
        simp only [j0, dstNe, false_and, if_false, true_and]
        rw [blank]
        split_ifs <;> rfl
      · simp only [j0, j1, false_and, if_false]
        rfl
  · exact gp
  · simp only [g, f', move, f, c, b, a', a, Cfg.mapState]

/-- Write the canonical bound field directly on a rich destination, using
an isolated clean bank and restoring that bank completely.

**Proof sketch.** The inherited bound writer is applied through its clean
rich-bank bridge. Move its canonical word to the destination by the public
copy/clear composite. The source clear restores the initial blank bank, while
all other tapes are framed. R2 joins the cuts and the logarithmic envelopes. -/
private theorem rt_exists_boundFieldTM (Q T : Type) [DecidableEq Q] [DecidableEq T] :
    ∃ (K : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (R : ∀ {k : ℕ}, (Fin (K + 1) ↪ Fin k) → Fin k → MultiTapeTM k (RecSym Q T) S)
      (entry exit : S) (C : ℕ),
      ∀ {k : ℕ} (ι : Fin (K + 1) ↪ Fin k) (dst : Fin k), dst ∉ Set.range ι →
      ∀ {x : List Bool} (d : Cfg k (RecSym Q T) S (x.map (RecSym.digitEmb Q T))),
        d.state = some entry → d.inputPos = 1 → (∀ i p, d.workTapes (ι i) p = none) →
      ∃ t ≤ C * (x.length + 1),
        (∀ u < t, ((R ι dst).runFrom d u).state ≠ some exit) ∧
        (∀ u ≤ t, ∀ j,
          |((R ι dst).runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * ((x.length + 1).bits.length + 1) : ℕ) : ℤ)) ∧
        (R ι dst).runFrom d t =
          { d with
            state := some exit
            workTapes := fun j p =>
              if j = dst ∧ d.workTapePos j ≤ p ∧
                  p < d.workTapePos j + ((x.length + 1).bits.length : ℤ)
              then FinTM.bufferTape ((x.length + 1).bits.map RecSym.digit)
                (p - d.workTapePos j) else d.workTapes j p } := by
  obtain ⟨K, P, fin, eq, R, en, ex, C, bound⟩ := rt_exists_cleanDigitBoundTM Q T
  letI := fin
  letI := eq
  refine ⟨K, P ⊕ (SweepPhase ⊕ SweepPhase), inferInstance, inferInstance,
    fun {k} ι dst => seamCompTM (embedEmitTM ι R) ex (rt_moveWordTM k (ι 0) dst) (.inl .sweep),
    .inl en, .inr (.inr .done), C + 10, ?_⟩
  intro k ι dst outside x d entry input blank
  let a := d.mapState (fun _ => en)
  have ae : a.state = some en := by simp [a, Cfg.mapState, entry]
  obtain ⟨t, cost, cut, heads, run⟩ := bound ι a ae input blank
  let a' : Cfg k (RecSym Q T) P (x.map (RecSym.digitEmb Q T)) :=
    { a with
      state := some ex
      workTapes := fun j p => if j = ι 0 then
        FinTM.bufferTape ((x.length + 1).bits.map RecSym.digit) (p - d.workTapePos j)
        else d.workTapes j p }
  change (embedEmitTM ι R).runFrom a t = a' at run
  let b := a'.mapState (fun _ => (Sum.inl SweepPhase.sweep : SweepPhase ⊕ SweepPhase))
  let w : List (RecSym Q T) := (x.length + 1).bits.map RecSym.digit
  have length : w.length = (x.length + 1).bits.length := by simp [w]
  have different : ι 0 ≠ dst := by intro h; exact outside ⟨0, h⟩
  have frame : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      b.workTapes (ι 0) (b.workTapePos (ι 0) + p) = FinTM.bufferTape w p := by
    intro p _ _
    change (if ι 0 = ι 0 then FinTM.bufferTape w
      (d.workTapePos (ι 0) + p - d.workTapePos (ι 0)) else _) = _
    rw [if_pos rfl]; congr 1; omega
  obtain ⟨move, moveCut, moveHeads⟩ := rt_moveWord_run (ι 0) dst different w b rfl frame
  have short : (x.length + 1).bits.length ≤ x.length + 1 := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact Nat.lt_two_pow_self
  let B : ℤ := ((C + 10) * ((x.length + 1).bits.length + 1) : ℕ)
  have radA : ∀ u ≤ t, ∀ j,
      |((embedEmitTM ι R).runFrom a u).workTapePos j - d.workTapePos j| ≤ B := by
    intro u hu j
    exact (heads u hu j).trans (by dsimp [B]; exact_mod_cast
      (show C * ((x.length + 1).bits.length + 1) ≤
        (C + 10) * ((x.length + 1).bits.length + 1) by nlinarith))
  have radB : ∀ u ≤ 4 * w.length + 5, ∀ j,
      |((rt_moveWordTM k (ι 0) dst).runFrom b u).workTapePos j - d.workTapePos j| ≤ B := by
    intro u hu j
    exact (moveHeads u hu j).trans (by dsimp [B]; rw [length]; exact_mod_cast
      (show (x.length + 1).bits.length + 1 ≤
        (C + 10) * ((x.length + 1).bits.length + 1) by nlinarith))
  obtain ⟨joined, first, radius⟩ := rt_copy_seam (embedEmitTM ι R) ex
    (rt_moveWordTM k (ι 0) dst) (.inl .sweep) (.inr .done) d.workTapePos B
    run rfl cut radA move rfl moveCut radB
  have start : a.mapState Sum.inl = d := by
    apply Cfg.ext <;> simp [a, Cfg.mapState, entry]
  rw [start] at joined first radius
  refine ⟨t + 1 + (4 * w.length + 5), by rw [length]; nlinarith,
    first, radius, ?_⟩
  rw [joined]
  apply Cfg.ext
  · rfl
  · rfl
  · funext j p
    simp only [Cfg.mapState, b, a', a, length]
    by_cases source : j = ι 0
    · subst j
      simp only [different, false_and, if_false, true_and]
      rw [blank]
      have mask := rt_bufferMask w (d.workTapePos (ι 0)) p
      rw [length] at mask
      split_ifs with inside
      · rfl
      · simpa only [if_neg inside] using mask.symm
    · simp only [source, false_and, if_false]
      rfl
  · rfl
  · rfl

/-- **R8.7, the record template** (design §12.8b). There is a module over the
record alphabet with an entry and an exit state and `K + 2` tapes with the
following contract. Start it at its entry with the native input `x` as digits
and its head at `1`; on tape `1` a delimited `Bool` word `ws` as digits, whose
little-endian value is the radius `s`; tape `0` blank on the template's slot
and one cell either side; and the other tapes blank. It reaches its exit within
`C` times the template length plus `|ws| + |x| + 1`, and not earlier, with
`Turing.recordTemplate |x| s` written at the head of tape `0` and nothing else
changed. Up to the exit every work head stays within `C` times the template
length plus `|ws| + 1` of its entry position, independently of `|x|`.

**Proof sketch.** Compose by R2 seams, running every `Bool` row lifted along
`Turing.RecSym.digitEmb` on dedicated digit tapes, isolated by R1
(`Turing.MultiTapeTM.liftSymbols_runFrom`). The bound field:
`Turing.exists_inputLengthTM` gives `Nat.bits |x|` on a scratch tape; one more
increment with the same width extension gives `Nat.bits (|x| + 1)`, which is the
bound field (`Turing.binDigits_posWidth_succ`); copy it to tape `0`
(`Turing.copyTM_run_ofCfg`) and clear the scratch. The window field: with `ws`
copied to a scratch counter before each expansion (an expansion leaves its
counter all `true`), `Turing.expandTM_run_ofCfg` with pattern `[false]` writes
`s` digits, `Turing.writeAdvTM` one `true` digit, and `Turing.expandTM` again `s`
digits, all in the digit image as the transport requires; a `Turing.scanTM` map
(`Turing.scanResult_map`) turns `digit b` into `cell none b`. Clear the
counters and return the heads by `Turing.skipBackTM`. The expansions cost
`O(s + |ws|)` by `Turing.counterOverhead_le`, and `2s + 1` is at most the
template length.

**Fill appendix (continuation 3, partial).** The clean-bank bound phase is
proved as `rt_exists_boundTM`: the public input-length row, the catalog
increment, and the one-cell overflow extension are composed by R2 and the
public phase host. `rt_exists_digitBoundTM` transports that phase through R1
onto an isolated digit bank, keeping arbitrary unselected rich tapes and
prior output. `rt_template_fields` identifies its canonical bound word and
the two unmarked window halves with these frozen fields. The window's two
expansions, copies, map, cleanup and final template composition remain
unfinished; this public row retains its original admission.

**Fill appendix (continuation 4, proved).** The bound field is now connected
to the destination and its isolated bank is cleared. The window copies the
radius into a separate clean digit bank, copies a fresh counter before each
expansion, and releases the one-bit advancing writer between the two halves.
A rich mapping scan converts the completed digits to `cell none`; rich
copy/clear rows transfer the window and clear every scratch word. All stages
are joined by R2 seams, including the destination skip and final rewind.
The original signature is proved with complete first-exit and head-envelope
clauses, using `rt_template_fields` and the public field-layout projections.
This supersedes the preceding continuation's admission status. -/
theorem exists_recordTemplateTM (Q T : Type) [Fintype Q] [DecidableEq Q] [Fintype T]
    [DecidableEq T] :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + 2) (RecSym Q T) P) (entry exit : P) (C : ℕ),
      ∀ {x : List Bool} (s : ℕ) (ws : List Bool), Nat.ofDigits 2 (ws.map Bool.toNat) = s →
      ∀ d : Cfg (K + 2) (RecSym Q T) P (x.map (RecSym.digitEmb Q T)),
        d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = FinTM.bufferTape (ws.map RecSym.digit) p) →
        (∀ p : ℤ, -1 ≤ p → p ≤ ((joinFields (recordTemplate Q T x.length s)).length : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + p) = none) →
        (∀ j : Fin (K + 2), 2 ≤ j.val → ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * ((joinFields (recordTemplate Q T x.length s)).length + ws.length +
            x.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j : Fin (K + 2),
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((joinFields (recordTemplate Q T x.length s)).length + ws.length + 1) :
                ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with
              state := some exit
              workTapes := fun j q =>
                if j = 0 ∧ d.workTapePos j ≤ q ∧
                    q < d.workTapePos j + ((joinFields (recordTemplate Q T x.length s)).length : ℤ)
                  then fieldsTape (recordTemplate Q T x.length s) (q - d.workTapePos j)
                else d.workTapes j q } := by
  obtain ⟨K, S, fin, eq, R, en, ex, C, bound⟩ := rt_exists_boundFieldTM Q T
  letI := fin
  letI := eq
  letI : Fintype rt_richWindowState := by
    set_option synthInstance.maxSize 512 in
      infer_instance
  letI : DecidableEq rt_richWindowState := Classical.typeDecidableEq _
  let bank : Fin (K + 1) ↪ Fin (K + 6) :=
    ⟨fun i => ⟨i.val + 2, by omega⟩, by
      intro i j h
      apply Fin.ext
      have := congrArg Fin.val h
      simp at this
      omega⟩
  let winBank : Fin 3 ↪ Fin (K + 6) :=
    ⟨fun i => ⟨i.val + K + 3, by omega⟩, by
      intro i j h
      apply Fin.ext
      have := congrArg Fin.val h
      simp at this
      omega⟩
  have bankPos (i : Fin (K + 1)) : 2 ≤ (bank i).val := by dsimp [bank]; omega
  have winPos (i : Fin 3) : 2 ≤ (winBank i).val := by dsimp [winBank]; omega
  have b0 : (0 : Fin (K + 6)) ∉ Set.range bank := by
    rintro ⟨i, hi⟩; have := bankPos i; rw [hi] at this; contradiction
  have w0 : (0 : Fin (K + 6)) ∉ Set.range winBank := by
    rintro ⟨i, hi⟩; have := winPos i; rw [hi] at this; contradiction
  have w1 : (1 : Fin (K + 6)) ∉ Set.range winBank := by
    rintro ⟨i, hi⟩; have := winPos i; rw [hi] at this; contradiction
  let W := rt_richWindowTM Q T (K + 6) 1 0 winBank
  let tail := seamCompTM W (.inr (.inr (.inr .done))) (skipBackTM (K + 6) 0) .run
  let rest := seamCompTM (skipTM (K + 6) 0) .done tail (.inl (.inl .sweep))
  let M := seamCompTM (R bank 0) ex rest (.inl .run)
  refine ⟨K + 4, S ⊕ (SeekPhase ⊕ (rt_richWindowState ⊕ SeekPhase)),
    inferInstance, Classical.typeDecidableEq _, M, .inl en, .inr (.inr (.inr .done)), C + 60, ?_⟩
  intro x s ws value d entry input radius slot blank
  let wb : List (RecSym Q T) := (x.length + 1).bits.map RecSym.digit
  let wc : List (RecSym Q T) :=
    (List.replicate s false ++ true :: List.replicate s false).map (RecSym.cell none)
  let L := (joinFields (recordTemplate Q T x.length s)).length
  have wl : wb.length = (x.length + 1).bits.length := by simp [wb]
  have cl : wc.length = 2 * s + 1 := by simp [wc]; omega
  have ll : L = wb.length + 2 * s + 2 := by
    change (joinFields (recordTemplate Q T x.length s)).length = _
    rw [joinFields_recordTemplate_length, wl]
    rfl
  have template : recordTemplate Q T x.length s = [wb, wc] := rt_template_fields Q T x.length s
  let a := d.mapState (fun _ => en)
  have ae : a.state = some en := by simp [a, Cfg.mapState, entry]
  obtain ⟨t, cost, cutA, headsA, runA⟩ := bound bank 0 b0 a ae input
    (fun i p => blank (bank i) (bankPos i) p)
  let a' : Cfg (K + 6) (RecSym Q T) S (x.map (RecSym.digitEmb Q T)) :=
    { a with
      state := some ex
      workTapes := fun j p =>
        if j = 0 ∧ d.workTapePos j ≤ p ∧ p < d.workTapePos j + (wb.length : ℤ)
        then FinTM.bufferTape wb (p - d.workTapePos j) else d.workTapes j p }
  have boundEnd : (R bank 0).runFrom a t = a' := by simpa only [a', wl] using runA
  let b := a'.mapState (fun _ => SeekPhase.run)
  have boundFrame (p : ℤ) (lo : -1 ≤ p) (hi : p ≤ (wb.length : ℤ)) :
      b.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape wb p := by
    change (if (0 : Fin (K + 6)) = 0 ∧ d.workTapePos 0 ≤ d.workTapePos 0 + p ∧
        d.workTapePos 0 + p < d.workTapePos 0 + (wb.length : ℤ)
      then FinTM.bufferTape wb (d.workTapePos 0 + p - d.workTapePos 0)
      else d.workTapes 0 (d.workTapePos 0 + p)) = _
    by_cases interior : 0 ≤ p ∧ p < (wb.length : ℤ)
    · rw [if_pos (by omega)]; congr 1; omega
    · rw [if_neg (by omega), slot p lo (by change p ≤ (L : ℤ); omega)]
      have edge : p = -1 ∨ p = (wb.length : ℤ) := by omega
      rcases edge with rfl | rfl <;> simp [FinTM.bufferTape]
  obtain ⟨runB, cutB, headsB⟩ := skipTM_run_ofCfg (0 : Fin (K + 6)) wb b rfl
    (fun p lo hi => boundFrame p (by omega) hi)
  let b' : Cfg (K + 6) (RecSym Q T) SeekPhase (x.map (RecSym.digitEmb Q T)) :=
    { b with
      state := some .done
      workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + wb.length + 1) }
  change (skipTM (K + 6) 0).runFrom b (wb.length + 1) = b' at runB
  let c := b'.mapState (fun _ => (Sum.inl SweepPhase.sweep : rt_richWindowState))
  have cp : c.workTapePos 0 = d.workTapePos 0 + wb.length + 1 := by
    simp [c, b', Cfg.mapState]
  have co (j : Fin (K + 6)) (ne : j ≠ 0) : c.workTapePos j = d.workTapePos j := by
    simp [c, b', Cfg.mapState, ne]
  have cr : ∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
      c.workTapes 1 (c.workTapePos 1 + p) = FinTM.bufferTape (ws.map RecSym.digit) p := by
    simpa [c, b', b, a', a, Cfg.mapState] using radius
  have cb (i : Fin 3) (p : ℤ) : c.workTapes (winBank i) p = none := by
    have ne : winBank i ≠ 0 := by intro h; exact w0 ⟨i, h⟩
    simp only [c, b', b, a', a, Cfg.mapState, ne, false_and, if_false]
    exact blank (winBank i) (winPos i) p
  obtain ⟨u, ucost, cutC, headsC, runC⟩ :=
    rt_richWindow_run Q T 1 0 winBank w1 w0 ws s value c rfl cr cb
  let c' : Cfg (K + 6) (RecSym Q T) rt_richWindowState (x.map (RecSym.digitEmb Q T)) :=
    { c with
      state := some (.inr (.inr (.inr .done)))
      workTapes := fun j p =>
        if j = 0 ∧ c.workTapePos j ≤ p ∧ p < c.workTapePos j + (wc.length : ℤ)
        then FinTM.bufferTape wc (p - c.workTapePos j) else c.workTapes j p }
  have windowEnd : W.runFrom c u = c' := by simpa only [c', cl] using runC
  let e := c'.mapState (fun _ => SeekPhase.run)
  have ep : e.workTapePos 0 = d.workTapePos 0 + wb.length + 1 := cp
  have eo (j : Fin (K + 6)) (ne : j ≠ 0) : e.workTapePos j = d.workTapePos j := co j ne
  have old (p : ℤ) (lo : -1 ≤ p) (hi : p ≤ (wb.length : ℤ)) :
      e.workTapes 0 (e.workTapePos 0 - wb.length - 1 + p) = FinTM.bufferTape wb p := by
    change (if (0 : Fin (K + 6)) = 0 ∧ c.workTapePos 0 ≤ e.workTapePos 0 - wb.length - 1 + p ∧
        e.workTapePos 0 - wb.length - 1 + p < c.workTapePos 0 + (wc.length : ℤ)
      then _ else b.workTapes 0 (e.workTapePos 0 - wb.length - 1 + p)) = _
    rw [if_neg (by rw [cp, ep]; omega), ep]
    convert boundFrame p lo hi using 1; congr 1; omega
  obtain ⟨runE, cutE, headsE⟩ := skipBackTM_run_ofCfg (0 : Fin (K + 6)) wb e rfl old
  let B : ℤ := ((C + 60) * (L + ws.length + 1) : ℕ)
  have big : (L : ℤ) + ws.length + 4 ≤ B := by
    dsimp [B]
    exact_mod_cast (show L + ws.length + 4 ≤ (C + 60) * (L + ws.length + 1) by nlinarith)
  have radA : ∀ v ≤ t, ∀ j,
      |((R bank 0).runFrom a v).workTapePos j - d.workTapePos j| ≤ B := by
    intro v hv j
    exact (headsA v hv j).trans (by dsimp [B]; exact_mod_cast
      (show C * ((x.length + 1).bits.length + 1) ≤ (C + 60) * (L + ws.length + 1) by
        rw [← wl]; nlinarith))
  have radB : ∀ v ≤ wb.length + 1, ∀ j,
      |((skipTM (K + 6) 0).runFrom b v).workTapePos j - d.workTapePos j| ≤ B := by
    intro v hv j
    have h := headsB j v hv
    change (if j = 0 then _ ∈ Finset.Icc (d.workTapePos j)
      (d.workTapePos j + wb.length + 1) else _ = d.workTapePos j) at h
    split_ifs at h
    · have h := Finset.mem_Icc.mp h
      exact abs_le.mpr ⟨by omega, by omega⟩
    · rw [h, sub_self, abs_zero]; omega
  have shift (j : Fin (K + 6)) : |c.workTapePos j - d.workTapePos j| ≤ wb.length + 1 := by
    by_cases zero : j = 0
    · subst j; rw [cp]; have : (0 : ℤ) ≤ wb.length := Int.natCast_nonneg _
      rw [abs_of_nonneg (by omega)]; omega
    · rw [co j zero, sub_self, abs_zero]; positivity
  have radC : ∀ v ≤ u, ∀ j,
      |(W.runFrom c v).workTapePos j - d.workTapePos j| ≤ B := by
    intro v hv j
    calc
      |(W.runFrom c v).workTapePos j - d.workTapePos j| =
          |((W.runFrom c v).workTapePos j - c.workTapePos j) +
            (c.workTapePos j - d.workTapePos j)| := by congr 1; ring
      _ ≤ |(W.runFrom c v).workTapePos j - c.workTapePos j| +
          |c.workTapePos j - d.workTapePos j| := abs_add_le _ _
      _ ≤ ((2 * s + ws.length + 3 : ℕ) : ℤ) + (wb.length + 1) :=
        add_le_add (headsC v hv j) (shift j)
      _ ≤ B := by omega
  have radE : ∀ v ≤ wb.length + 3, ∀ j,
      |((skipBackTM (K + 6) 0).runFrom e v).workTapePos j - d.workTapePos j| ≤ B := by
    intro v hv j
    have h := headsE j v hv
    by_cases zero : j = 0
    · subst j
      simp only [if_true, Finset.mem_Icc, ep] at h
      exact abs_le.mpr ⟨by omega, by omega⟩
    · simp only [if_neg zero, eo j zero] at h
      rw [h, sub_self, abs_zero]; omega
  obtain ⟨tailRun, tailCut, tailHeads⟩ := rt_copy_seam W (.inr (.inr (.inr .done)))
    (skipBackTM (K + 6) 0) .run .done d.workTapePos B
    windowEnd rfl cutC radC runE rfl cutE radE
  obtain ⟨restRun, restCut, restHeads⟩ := rt_copy_seam (skipTM (K + 6) 0) .done
    tail (.inl (.inl .sweep)) (.inr .done) d.workTapePos B
    runB rfl cutB radB tailRun rfl tailCut tailHeads
  obtain ⟨run, cut, heads⟩ := rt_copy_seam (R bank 0) ex rest (.inl .run)
    (.inr (.inr .done)) d.workTapePos B
    boundEnd rfl cutA radA restRun rfl restCut restHeads
  have start : a.mapState Sum.inl = d := by
    apply Cfg.ext <;> simp [a, Cfg.mapState, entry]
  rw [start] at run cut heads
  refine ⟨_, by
    change _ ≤ (C + 60) * (L + ws.length + x.length + 1)
    nlinarith,
    cut, heads, ?_⟩
  change M.runFrom d _ = _ at run
  rw [run]
  apply Cfg.ext
  · rfl
  · rfl
  · funext j p
    by_cases zero : j = 0
    · subst j
      simp only [Cfg.mapState, e, c', c, b', b, a', a, Function.update_self, true_and]
      have layoutLength : (joinFields [wb, wc]).length = L := by rw [← template]
      rw [template, layoutLength]
      by_cases whole : d.workTapePos 0 ≤ p ∧ p < d.workTapePos 0 + (L : ℤ)
      · rw [if_pos whole]
        by_cases left : p < d.workTapePos 0 + (wb.length : ℤ)
        · rw [if_neg (by omega), if_pos ⟨whole.1, left⟩]
          have h := fieldsTape_field [wb, wc] 0 (by simp) (p - d.workTapePos 0)
            (by omega) (by simp; omega)
          simpa [fieldOffset] using h.symm
        · by_cases gap : p = d.workTapePos 0 + (wb.length : ℤ)
          · rw [if_neg (by omega), if_neg (by omega)]
            have blankGap := slot (wb.length : ℤ) (by omega) (by change _ ≤ (L : ℤ); omega)
            rw [gap, blankGap]
            have h := fieldsTape_field [wb, wc] 0 (by simp) (wb.length : ℤ)
              (by omega) (by simp)
            simpa [fieldOffset, FinTM.bufferTape] using h.symm
          · rw [if_pos (by omega)]
            have h := fieldsTape_field [wb, wc] 1 (by simp)
              (p - (d.workTapePos 0 + wb.length + 1)) (by omega) (by simp; omega)
            have offset : (fieldOffset [wb, wc] 1 : ℤ) = wb.length + 1 := by simp [fieldOffset]
            rw [offset] at h
            convert h.symm using 1; congr 1; omega
      · rw [if_neg whole, if_neg (by omega), if_neg (by omega)]
    · simp [Cfg.mapState, e, c', c, b', b, a', a, zero]
  · funext j
    by_cases zero : j = 0
    · subst j
      simp only [Cfg.mapState, Function.update_self, ep]
      omega
    · simp only [Cfg.mapState, Function.update_of_ne zero, eo j zero]
  · rfl

/-- **R8.7, the initial record** (design §12.8a §3, §12.8b). For a start state
`q₀` and an initial tag `τ₀`, there is a module over the record alphabet with
an entry and an exit state and `K + 2` tapes with the following contract.
Start it at its entry with the native input `x` as digits and its head at `1`;
on tape `1` a delimited `Bool` word `ws` as digits, of value `s`; tape `0` blank
on a record's slot and one cell either side; and the other tapes blank. It
reaches its exit within `C` times the record length plus `|ws| + s + |x| + 1`,
and not earlier, with the record of `Cfg.init q₀ x` at radius `s` with tag `τ₀`
written at the head of tape `0` and nothing else changed. Up to the exit every
work head stays within `C` times the record length plus `|ws| + s + 1` of its
entry position, independently of `|x|`. The radius enters the space bound
because at `k = 0` the record has no window field.

**Proof sketch.** Run `Turing.exists_recordTemplateTM` onto a scratch tape. Then
write the record field by field by R2 seams (`Turing.cfgRecord_init`):
`Turing.writeConstTM` writes `[st (some q₀)]`; the position field is the
template's bound field copied (`Turing.copyTM_run_ofCfg`), mapped to
`digit false` (`Turing.scanTM`), with `digit true` written on its first cell, the
digits of `1`; the `k` tape fields are copies of the template's window field;
`Turing.writeConstTM` writes `[tag τ₀]`; `Turing.skipTM` crosses each written
field. Clear the template (`Turing.clearTM_run_ofCfg` per field) and return the
heads by `Turing.skipBackTM`.

**Fill appendix (continuation 3, partial).** Row 17 is still open after its
bound-field prefix. The dependent initial-record machine is not implemented;
this public row retains its original admission and the field-by-field route
above.

**Fill appendix (continuation 4, partial).** Row 17 is now proved without
admissions and supplies the scratch template required by this route. The
field-by-field initial-record constructor remains unimplemented, so this
row retains its original admission. Next compose the state field, the copied
and zeroed position field with its leading `true`, the `k` copied window
fields, and the tag; then clear the template and rewind. The `k = 0` case
must retain the separate radius term in the issued space bound. -/
theorem exists_recordInitTM (k : ℕ) {Q T : Type} [Fintype Q] [DecidableEq Q] [Fintype T]
    [DecidableEq T] (q₀ : Q) (τ₀ : T) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + 2) (RecSym Q T) P) (entry exit : P) (C : ℕ),
      ∀ {x : List Bool} (s : ℕ) (ws : List Bool), Nat.ofDigits 2 (ws.map Bool.toNat) = s →
      ∀ d : Cfg (K + 2) (RecSym Q T) P (x.map (RecSym.digitEmb Q T)),
        d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = FinTM.bufferTape (ws.map RecSym.digit) p) →
        (∀ p : ℤ, -1 ≤ p → p ≤ (recordLength k x.length s : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + p) = none) →
        (∀ j : Fin (K + 2), 2 ≤ j.val → ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * (recordLength k x.length s + ws.length + s + x.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j : Fin (K + 2),
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * (recordLength k x.length s + ws.length + s + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with
              state := some exit
              workTapes := fun j q =>
                if j = 0 ∧ d.workTapePos j ≤ q ∧
                    q < d.workTapePos j + (recordLength k x.length s : ℤ)
                  then fieldsTape (cfgRecord s (Cfg.init q₀ x : Cfg k Bool Q x) τ₀)
                    (q - d.workTapePos j)
                else d.workTapes j q } := by
  sorry

/-- **R8.7, record validity** (design §12.8a §3, §12.8b). There is a module over
the record alphabet with an entry and two distinct verdict anchors and `K + 2`
tapes with the following contract. Start it at its entry with a list `fs` of
`k + 3` fields laid out at the head of tape `0`, the template
`Turing.recordTemplate n s` at the head of tape `1`, and the other tapes blank.
It reaches `yes` if `fs` is a valid record at `(k, n, s)` and `no` otherwise,
within `C` times the two layout lengths plus `n + 1`, with no verdict earlier
and nothing else changed. Up to the verdict every work head stays within `C`
times the two layout lengths plus one of its entry position. The native input
is arbitrary and not read. The field count is necessary: a tape holding the
layout of a record also holds, at the same head, the layout of its first two
fields, which is not a record.

**Proof sketch.** Check the conjuncts of `Turing.recordValid_iff` field by field,
crossing fields by `Turing.skipTM` and returning by `Turing.skipBackTM`. The
state and tag fields: a `Turing.scanTM` fold accepts exactly one cell of the
right kind. The position field: a fold accepts digits only; its width is
compared with the template's bound field by copying both to scratch
(`Turing.copyTM_run_ofCfg`), mapping both to one symbol (`Turing.scanTM` map),
and the framed compare (`Turing.compareTM_run_ofCfg`); its value is at most
`n + 1` exactly when, counting the copy of the field down to zero while
decrementing the copy of the bound once per round, the bound does not
underflow: the `Bool` loop `Turing.counterLoopTM` lifted onto the two
dedicated digit tapes (`Turing.MultiTapeTM.liftSymbols_runFrom`), its round a
released decrement (`Turing.seamReleaseTM`, `Turing.decrementTM_run_succ_ofCfg`)
and its escape the bound's underflow. After the width check the value is below
`2 ^ posWidth n ≤ 2(n + 1)`, so this costs `O(n + |fs|)`; no rich loop (R8.0b)
is needed. Each tape field: the width against
the template's window field by the same mapped compare, and a fold accepts only
`cell` symbols with exactly one mark. Clear the scratch. -/
theorem exists_recordValidTM (k : ℕ) (Q T : Type) [Fintype Q] [DecidableEq Q] [Fintype T]
    [DecidableEq T] :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + 2) (RecSym Q T) P) (entry yes no : P) (C : ℕ), yes ≠ no ∧
      ∀ {y : List (RecSym Q T)} (n s : ℕ) (fs : List (List (RecSym Q T))), fs.length = k + 3 →
      ∀ d : Cfg (K + 2) (RecSym Q T) P y, d.state = some entry →
        RecordAt d 0 fs → RecordAt d 1 (recordTemplate Q T n s) →
        (∀ j : Fin (K + 2), 2 ≤ j.val → ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * ((joinFields fs).length + (joinFields (recordTemplate Q T n s)).length + n + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no) ∧
          (∀ u ≤ t, ∀ j : Fin (K + 2),
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((joinFields fs).length + (joinFields (recordTemplate Q T n s)).length + 1) :
                ℕ) : ℤ)) ∧
          (RecordValid k n s Q T fs → R.runFrom d t = { d with state := some yes }) ∧
          (¬ RecordValid k n s Q T fs → R.runFrom d t = { d with state := some no }) := by
  sorry

/-- **R8.7, enumerating the valid records** (design §12.8a §3, §12.8b). There is
a duplicate-free list `enum n s` of exactly the valid records at `(k, n, s)`, and
a module over the record alphabet with two entries `first` and `next`, two
distinct verdict anchors and `K + 2` tapes, walking it, with the following
contract. Let the template `Turing.recordTemplate n s` be at the head of tape `1`
and the tapes from `2` on be blank.
* From `first`, with tape `0` blank on a record's slot and one cell either side,
  the module writes `enum n s`'s first record at the head of tape `0` and
  answers `yes`; if there is no valid record, it answers `no` with nothing
  changed.
* From `next`, with record `i` of `enum n s` at the head of tape `0`, it rewrites
  it in place into record `i + 1` and answers `yes`, or, after the last record,
  answers `no` with nothing changed.
In both cases it reaches the verdict within `C` to the power of the record and
template lengths plus one, with no verdict earlier and every other cell, every
head, the input position and the output restored. Up to the verdict every work
head stays within `C` times those lengths plus one of its entry position. The
native input is arbitrary and not read. The time is exponential because
consecutive valid records can be far apart in the odometer order; the space is
linear, which is what Savitch's midpoint enumeration needs, and the order
itself is never consumed. There is no valid record exactly when the tag type is
empty.

**Proof sketch.** Take `enum n s` to be the valid records sorted in the
odometer order: over cells, the colex order of a fixed rank of the record
symbols within each field kind, field `0` least significant. From `first`,
write the least shaped candidate (each cell the least symbol of its kind, the
widths copied from the template, as in `Turing.exists_recordInitTM`) and test
it by `Turing.exists_recordValidTM`; if it is invalid, continue as from `next`.
From `next`, work on a scratch copy (`Turing.exists_fieldsCopyTM`): advance it by
the carry odometer, one `Turing.scanTM` carry step per field
(`Turing.scanResult_carry`), the carry passing from field to field in finite
control; test the candidate by `Turing.exists_recordValidTM`; repeat under
`Turing.counterLoopTMVia` (R8.0b). Its counter is an all-`true` digit word made
of a fixed number of copies of the template's fields (three digits per window
cell cover the six cell symbols, one per position digit, and a constant for the
state and tag), so its value exceeds the number of shaped candidates and it
never runs out. On a valid candidate, clear the record
(`Turing.clearTM_run_ofCfg` per field) and copy the candidate back; on the
final carry, answer `no` with the record untouched. Each candidate costs
`O(L + n)` with `n + 1 < 2 ^ posWidth n`, and there are at most `B ^ L` shaped
candidates for `B` the alphabet size, which `C ^ (L + |template| + 1)` absorbs.
The heads move only over the record, the template and scratch copies of them. -/
theorem exists_recordNextTM (k : ℕ) (Q T : Type) [Fintype Q] [DecidableEq Q] [Fintype T]
    [DecidableEq T] :
    ∃ enum : ℕ → ℕ → List (List (List (RecSym Q T))),
      (∀ n s, (enum n s).Nodup) ∧ (∀ n s fs, fs ∈ enum n s ↔ RecordValid k n s Q T fs) ∧
      ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
        (R : MultiTapeTM (K + 2) (RecSym Q T) P) (first next yes no : P) (C : ℕ), yes ≠ no ∧
        ∀ {y : List (RecSym Q T)} (n s : ℕ) (d : Cfg (K + 2) (RecSym Q T) P y),
          RecordAt d 1 (recordTemplate Q T n s) →
          (∀ j : Fin (K + 2), 2 ≤ j.val → ∀ p, d.workTapes j p = none) →
          (d.state = some first →
            (∀ p : ℤ, -1 ≤ p → p ≤ (recordLength k n s : ℤ) →
              d.workTapes 0 (d.workTapePos 0 + p) = none) →
            ∃ t ≤ C ^ (recordLength k n s + (joinFields (recordTemplate Q T n s)).length + 1),
              (∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no) ∧
              (∀ u ≤ t, ∀ j : Fin (K + 2),
                |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
                  ((C * (recordLength k n s + (joinFields (recordTemplate Q T n s)).length + 1) :
                    ℕ) : ℤ)) ∧
              R.runFrom d t =
                match (enum n s)[0]? with
                | some gs =>
                  { d with
                    state := some yes
                    workTapes := fun j q =>
                      if j = 0 ∧ d.workTapePos j ≤ q ∧
                          q < d.workTapePos j + (recordLength k n s : ℤ)
                        then fieldsTape gs (q - d.workTapePos j)
                      else d.workTapes j q }
                | none => { d with state := some no }) ∧
          (∀ (i : ℕ) (hi : i < (enum n s).length), d.state = some next →
            RecordAt d 0 (enum n s)[i] →
            ∃ t ≤ C ^ (recordLength k n s + (joinFields (recordTemplate Q T n s)).length + 1),
              (∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no) ∧
              (∀ u ≤ t, ∀ j : Fin (K + 2),
                |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
                  ((C * (recordLength k n s + (joinFields (recordTemplate Q T n s)).length + 1) :
                    ℕ) : ℤ)) ∧
              R.runFrom d t =
                match (enum n s)[i + 1]? with
                | some gs =>
                  { d with
                    state := some yes
                    workTapes := fun j q =>
                      if j = 0 ∧ d.workTapePos j ≤ q ∧
                          q < d.workTapePos j + (recordLength k n s : ℤ)
                        then fieldsTape gs (q - d.workTapePos j)
                      else d.workTapes j q }
                | none => { d with state := some no }) := by
  sorry

end Turing
