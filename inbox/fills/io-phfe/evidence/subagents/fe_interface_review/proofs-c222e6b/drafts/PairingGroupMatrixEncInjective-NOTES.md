# BilinearGroup.groupMatrixEnc_injective candidate

Status: independent scratch full candidate checked by inspection only. Root native check
pending; no Lean/lake/build/Git/live edits/extra agent were used. Frozen header/prose exact,
one tactic block, no remaining holes/sorry, no helper or statement change. Matrix entries
stay arbitrary group values. Neither a scalar encoding nor a discrete logarithm is used.

## Generic API reuse and zero dimensions

List.eq_iff_flatten_eq (core) states exactly that equal flattened words AND equal lists of
block lengths imply equal block lists. Use it twice:

* Recover the list of row words from the actual encoded-word equality (groupMatrixEnc_eq).
  List.length_flatten/map_ofFn/length_ofFn/ofFn_const/sum_replicate_nat show each row has
  cols*wG bits, so both lists of row lengths agree.
* List.ofFn_injective yields equality of each row word. Recover its point-word list by the
  same List.eq_iff_flatten_eq; every point word has wG bits by List.length_ofFn.
* Apply List.ofFn_injective to the point list and then to the fixed-width point encoding;
  B.encG_injective gives equality of the two group entries.

These general List APIs include zero row/column/encoding lengths. No positivity hypothesis
or manual concatenation cancellation is added. The proof does not depend on the admitted
length_groupMatrixEnc theorem: its only group serialization reader is groupMatrixEnc_eq.
All other length facts are direct applications of existing generic List theorems.

No foreign/core/Mathlib definition or generated equation is explicitly passed to simp/rw/
unfold. All supplied simp arguments are published equations. Local hRows/hRow/hBlocks are
concrete proof steps inside the frozen existing theorem, not new helper interfaces.

## Actual search and inspection record

Read current live MatrixDH/Defs.lean:48-83 to preserve exact header and encoding shape.

Searched these patterns before writing:

* `eq_iff_flatten_eq|flatten.*(inj|eq_iff)|Injective.*flatten|injective.*flatten|ofFn_injective`
  over Mathlib List, installed core Init/List and TCSlib Encoding files.
* `eq_iff_flatten_eq|flatten_injective|ofFn_injective` over TCSlib/Cryptography.
* `encodeMatrix_injective|encodeVector_injective` in Encoding/Modular.lean.
* `(theorem|lemma) ofFn_injective` in Mathlib/List/OfFn and installed core List/OfFn.

Exact generic APIs were inspected in place:

* Installed Lean Init/Data/List/Lemmas.lean:2023, List.eq_iff_flatten_eq, exact iff orientation
  (flatten equality first, equal mapped lengths second).
* Mathlib/Data/List/OfFn.lean:192, List.ofFn_injective; :37, List.map_ofFn.
* Pairing/Group.lean:130-132, encG : G -> Fin wG -> Bool and encG_injective.
* Current prior-invocation verified APIs: List.length_flatten (Init/List/Lemmas:1869),
  List.length_ofFn (Init/List/OfFn:40), List.ofFn_const (Mathlib/List/OfFn:117),
  List.sum_replicate_nat (Init/List/Lemmas:2350).

## Source-relative parallels / overlap disclosure

The nearest in-tree parallel is Encoding/Modular.lean:101-140,
encodeVector_injective and encodeMatrix_injective. Read their full proofs. They already
apply List.eq_iff_flatten_eq to point blocks/rows and List.ofFn_injective to coordinates.
The group proof follows that generic List API route, with point recovery delegated to the
existing B.encG_injective field instead of numeral/residue round trips. No generic flatten
or cancellation material is copied/reproved, and no scalar Encoding module is imported.
The algorithm-specific two-level block bookkeeping necessarily parallels those proofs;
this overlap is disclosed rather than introduced as a private generic helper.

No new helper target/native search is needed because the general core iff exactly covers
both flatten steps. Root native verification should focus only on inferred Fin dimensions
and recursive list-length simplification of the outer row-length lists.
