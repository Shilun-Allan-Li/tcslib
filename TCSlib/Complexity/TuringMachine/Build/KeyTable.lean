/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.RecordTable
import TCSlib.Complexity.TuringMachine.Build.WordArith

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Keyed tables: lookup and assignment by a key held on another tape

A **keyed table** is a list of entries `(key, value)` of binary words, laid out on one work tape
in the record-table layout of `Build/RecordTable` (`Turing.TableAt`): the header `[true]`, then
for each entry the two fields `true :: key` and `true :: value`, fields separated by one blank,
two blanks before the header and after the last field. The leading `true` of each field keeps
every field nonempty, so the layout is well formed (`Turing.TableWF`) even for empty keys or
values, and a blank pair marks the table's end.

The two rows are the host of a memory: **lookup** copies the value stored under a key, held on
another tape, into a register (the all-`false` word if the key is absent), and **assignment**
overwrites the value stored under a key in place, or appends a new entry. They are the memory of
a word RAM run on a Turing machine (`WordRAM.exists_simulation`), where keys are addresses and
values are words, but they are generic in both.

The record-table rows `Turing.exists_tableFindTM` and `Turing.exists_tableAppendTM` select by a
finite-state predicate and do not read a key from another tape; they are not used here.

## Main definitions

* `Turing.keyFields`, `Turing.keyTableLength`, `Turing.KeyTableAt`: the layout.
* `Turing.keyLookup`, `Turing.keyAssign`: the two operations on lists of entries.
* `Turing.keyTableWrite`: the tapes after laying a keyed table out.

## Main results

* `Turing.exists_keyLookupTM`: lookup, within `O(table + key + value)` steps.
* `Turing.exists_keyAssignTM`: assignment, within the same bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9: a RAM's memory kept by a Turing machine as a
  list of address and value pairs, scanned at each access.)
-/

namespace Turing

/-! ## The layout -/

/-- **The fields of a keyed table's entries**: each entry `(k, v)` gives the two fields
`true :: k` and `true :: v`. -/
def keyFields (es : List (List Bool × List Bool)) : List (List (List Bool)) :=
  es.map fun e => [true :: e.1, true :: e.2]

/-- The fields of a keyed table's entries, as an equation. -/
theorem keyFields_def (es : List (List Bool × List Bool)) :
    keyFields es = es.map fun e => [true :: e.1, true :: e.2] := rfl

/-- **The length of a keyed table's layout**: the cells from the header's first to the last
field's last, separators included (the sentinels excluded). -/
def keyTableLength (es : List (List Bool × List Bool)) : ℕ :=
  (joinFields (tableFields [true] (keyFields es))).length

/-- The length of a keyed table's layout, as an equation. -/
theorem keyTableLength_def (es : List (List Bool × List Bool)) :
    keyTableLength es = (joinFields (tableFields [true] (keyFields es))).length := rfl

/-- **A keyed table on a tape**: tape `r` holds the record-table layout of the header `[true]`
and the entries `keyFields es` from the origin `o` (`Turing.TableAt`, with its two blank cells on
either side), and every cell after the layout is blank, so that the table can grow. -/
def KeyTableAt {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K) (o : ℤ)
    (es : List (List Bool × List Bool)) : Prop :=
  TableAt d r o [true] (keyFields es) ∧
    ∀ q : ℤ, o + (keyTableLength es : ℤ) ≤ q → d.workTapes r q = none

/-- `KeyTableAt`, as an equivalence with its definition. -/
theorem keyTableAt_iff {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (o : ℤ) (es : List (List Bool × List Bool)) :
    KeyTableAt d r o es ↔ TableAt d r o [true] (keyFields es) ∧
      ∀ q : ℤ, o + (keyTableLength es : ℤ) ≤ q → d.workTapes r q = none :=
  Iff.rfl

/-- **The tapes after laying a keyed table out**: on tape `r`, the cells `[o, o + L)` hold the
layout of `es`, `L = keyTableLength es`; every other cell, of every tape, is unchanged. -/
def keyTableWrite {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K) (o : ℤ)
    (es : List (List Bool × List Bool)) : Fin K → ℤ → Option Bool :=
  fun j q =>
    if j = r ∧ o ≤ q ∧ q < o + (keyTableLength es : ℤ)
      then fieldsTape (tableFields [true] (keyFields es)) (q - o)
    else d.workTapes j q

/-- `keyTableWrite`, as an equation. -/
theorem keyTableWrite_apply {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (o : ℤ) (es : List (List Bool × List Bool)) (j : Fin K) (q : ℤ) :
    keyTableWrite d r o es j q =
      if j = r ∧ o ≤ q ∧ q < o + (keyTableLength es : ℤ)
        then fieldsTape (tableFields [true] (keyFields es)) (q - o)
      else d.workTapes j q :=
  rfl

/-! ## The operations -/

/-- **Lookup**: the value of the first entry whose key is `k`, if any. -/
def keyLookup (es : List (List Bool × List Bool)) (k : List Bool) : Option (List Bool) :=
  (es.find? fun e => e.1 = k).map Prod.snd

/-- Lookup, as an equation. -/
theorem keyLookup_def (es : List (List Bool × List Bool)) (k : List Bool) :
    keyLookup es k = (es.find? fun e => e.1 = k).map Prod.snd := rfl

/-- **Assignment**: if some entry has the key `k`, every such entry's value becomes `v`;
otherwise the entry `(k, v)` is appended. -/
def keyAssign (es : List (List Bool × List Bool)) (k v : List Bool) :
    List (List Bool × List Bool) :=
  if es.any (fun e => e.1 = k) then es.map fun e => if e.1 = k then (k, v) else e
  else es ++ [(k, v)]

/-- Assignment, as an equation. -/
theorem keyAssign_def (es : List (List Bool × List Bool)) (k v : List Bool) :
    keyAssign es k v =
      if es.any (fun e => e.1 = k) then es.map fun e => if e.1 = k then (k, v) else e
      else es ++ [(k, v)] := rfl

/-! ## The rows

Both rows are five-tape machines over `Bool`: tape `0` holds the table, with its head at the
origin; tape `1` the key; tape `2` the value register; tapes `3` and `4` are blank scratch tapes
(`Turing.ScratchBlank`), left blank. Every head ends where it started. -/

/-- **Keyed lookup.** From the entry, with a keyed table `es` at the head of tape `0`, a key `k`
on tape `1` and a register word `w` on tape `2`, every value of the table as long as `w`, and
blank scratch tapes: the row writes over `w` the value stored under `k`, or `|w|` zeros if `k` is
absent, and stops at its exit within `C·(L + |k| + |w| + 1)` steps and radius, where `L` is the
table's layout length. [AB09, Exercise 1.9]

**Proof sketch.** For each entry in turn: compare its key field after the marker with tape `1`
in lockstep (`Turing.compareTM`'s method, returning both heads); on a match, copy the value field
after the marker to tape `2` (`Turing.copyTM`), return to the origin and exit; otherwise skip the
entry's two fields (`Turing.skipTM`). At the blank pair after the last field, clear tape `2` to
zeros over its own length and return to the origin. Each entry is crossed a constant number of
times. A comparison stops at the first differing cell, so it and the return of tape `1`'s head
cost at most a constant times the entry's key field plus one; summed over the entries this is
`O(L)`, and the final copy and return are `O(L + |k| + |w|)`. -/
theorem exists_keyLookupTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} (o : ℤ) (es : List (List Bool × List Bool)) (k w : List Bool)
        (d : Cfg 5 Bool S x),
        d.state = some entry → d.workTapePos 0 = o → KeyTableAt d 0 o es → WordAt d 1 k →
        WordAt d 2 w → (∀ e ∈ es, e.2.length = w.length) → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (keyTableLength es + k.length + w.length + 1))
          (C * (keyTableLength es + k.length + w.length + 1))
          { d with state := some exit,
                   workTapes :=
                     wordWrite d 2 ((keyLookup es k).getD (List.replicate w.length false)) } := by
  sorry

/-- **Keyed assignment.** From the entry, with a keyed table `es` at the head of tape `0`, a key
`k` on tape `1` and a value `v` on tape `2`, every value of the table as long as `v`, and blank
scratch tapes: the row lays out `keyAssign es k v` from the origin, overwriting the value under
`k` in place or appending `(k, v)`, and stops at its exit within `C·(L + |k| + |v| + 1)` steps
and radius, where `L` is the old table's layout length. [AB09, Exercise 1.9]

**Proof sketch.** Search as in `Turing.exists_keyLookupTM`. On a match, copy tape `2` over the
value field after its marker (same length, so the layout is unchanged elsewhere), and continue
the search through the rest of the table, overwriting every further match. If there was no match,
the head reaches the first blank of the pair after the table: write a separator, the field
`true :: k` from tape `1`, a separator and the field `true :: v` from tape `2`; the cells beyond
were blank (`KeyTableAt`), so the new layout's trailing blank pair is there. Return to the
origin. -/
theorem exists_keyAssignTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} (o : ℤ) (es : List (List Bool × List Bool)) (k v : List Bool)
        (d : Cfg 5 Bool S x),
        d.state = some entry → d.workTapePos 0 = o → KeyTableAt d 0 o es → WordAt d 1 k →
        WordAt d 2 v → (∀ e ∈ es, e.2.length = v.length) → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (keyTableLength es + k.length + v.length + 1))
          (C * (keyTableLength es + k.length + v.length + 1))
          { d with state := some exit, workTapes := keyTableWrite d 0 o (keyAssign es k v) } := by
  sorry

end Turing
