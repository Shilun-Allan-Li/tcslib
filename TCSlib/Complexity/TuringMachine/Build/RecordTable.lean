/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.CfgRecord
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.InputLength

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

**Status: statements.** Every definition is real. Every layout fact and every
row is sorried with a proof sketch, pending the §12.8b fill, except
`Turing.RecordValid.joinFields_length`, which is proved from the record
length.

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
  — layout and record facts (statements).
* `Turing.TableWF.field_ne_nil`, `Turing.tableOffset_eq`,
  `Turing.tableOffset_length`, `Turing.TableAt.recordAt_take` — table facts
  (statements).
* `Turing.tableRewindTM_run_ofCfg` — the adapter's framed contract
  (statement).
* `Turing.exists_fieldsCopyTM`, `Turing.exists_tableFindTM`,
  `Turing.exists_tableAppendTM` — the table rows (statements).
* `Turing.exists_recordTemplateTM`, `Turing.exists_recordInitTM`,
  `Turing.exists_recordValidTM`, `Turing.exists_recordNextTM` — the deferred
  record rows of R8.7 (statements).

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
field, and each further field adds its length and one separator. -/
theorem joinFields_length {Γ : Type*} (fs : List (List Γ)) (hfs : fs ≠ []) :
    (joinFields fs).length = (fs.map List.length).sum + fs.length - 1 := by
  sorry

/-- **The end offset of a field layout** (design §12.8b; the formula of
`Turing.fieldOffset`'s docstring, made a lemma). For a nonempty field list,
`fieldOffset fs |fs|` is the layout length plus one: the cell after the blank
that ends the layout, where `Turing.seekEndTM` stops and a further field would
start.

**Proof sketch.** `fieldOffset fs |fs|` sums `|f| + 1` over all fields, which is
`Turing.joinFields_length` plus one. -/
theorem fieldOffset_length {Γ : Type*} (fs : List (List Γ)) (hfs : fs ≠ []) :
    fieldOffset fs fs.length = (joinFields fs).length + 1 := by
  sorry

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
  sorry

/-- **Record fields are nonempty** (design §12.8b). No field of a record is
empty, so a table of records has no double blank inside it and the seek rows
apply.

**Proof sketch.** The state and tag fields have one cell, the tape fields
`2s + 1`, and the position field `posWidth |x| ≥ 1` cells, since
`Nat.bits (|x| + 1)` is nonempty. -/
theorem cfgRecord_field_ne_nil {k : ℕ} {Q T : Type} {x : List Bool} (s : ℕ)
    (c : Cfg k Bool Q x) (τ : T) : ∀ u ∈ cfgRecord s c τ, u ≠ [] := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **The template's bound field is `Nat.bits (n + 1)`** (design §12.8b). The
position width is the bit length of `n + 1`, so the fixed-width digits of
`n + 1` are its canonical binary word. A machine obtains the bound field from
`Turing.exists_inputLengthTM`'s `Nat.bits n` by one more increment.

**Proof sketch.** `binDigits w v` lists `v.testBit j` for `j < w`, and
`Nat.bits v` lists the same bits up to the bit length of `v`, which is
`posWidth n` at `v = n + 1`. -/
theorem binDigits_posWidth_succ (n : ℕ) :
    binDigits (posWidth n) (n + 1) = Nat.bits (n + 1) := by
  sorry

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
  sorry

/-- **Entry offsets in closed form** (design §12.8b). When no entry is empty,
entry `j` starts after the header and its separator and, for each earlier
entry, its layout and one separator.

**Proof sketch.** Split `Turing.fieldOffset` over the header and the flattened
entries, and use `Turing.fieldOffset_length` on each earlier entry. -/
theorem tableOffset_eq {Γ : Type*} (h : List Γ) (es : List (List (List Γ)))
    (hes : ∀ e ∈ es, e ≠ []) (j : ℕ) :
    tableOffset h es j =
      h.length + 1 + ((es.take j).map fun e => (joinFields e).length + 1).sum := by
  sorry

/-- **The end of a table** (design §12.8b). The offset past the last entry is
the table's layout length plus one: the second trailing blank, where
`Turing.seekEndTM` stops from the origin.

**Proof sketch.** At `j = |es|` the field index is `|tableFields h es|`; apply
`Turing.fieldOffset_length`, the field list being nonempty. -/
theorem tableOffset_length {Γ : Type*} (h : List Γ) (es : List (List (List Γ))) :
    tableOffset h es es.length = (joinFields (tableFields h es)).length + 1 := by
  sorry

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
  sorry

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
field. The first-return cut is `Turing.seamCompTM_firstReturn_ofCfg`. -/
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
  sorry

/-! ### Copying a field list -/

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
in the fields crossed. -/
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
  sorry

/-! ### The table rows -/

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
have to differ. -/
theorem exists_tableFindTM {Γ : Type*} [DecidableEq Γ] (e : Bool ↪ Γ) (m : ℕ) (hm : 0 < m)
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
the new layout written over `[o, o + L')`. -/
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
template length. -/
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
  sorry

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
heads by `Turing.skipBackTM`. -/
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
