# BilinearGroup.length_groupMatrixEnc candidate

Status: independent scratch candidate checked by inspection only; native verification pending.
No Lean, lake, build, Git, live edit or additional agent was run. Exact live theorem name is
length_groupMatrixEnc. Frozen header/prose byte-preserved, one tactic block, no holes/sorry,
no helper or representation change; all lines ≤100 columns.

Read groupMatrixEnc_eq, then List.length_flatten turns each concatenation length into a
sum of block lengths. List.map_ofFn/Function.comp_apply transport the length function
inside each finite list. Every point word has width wG by List.length_ofFn, because encG
has type B.G -> Fin wG -> Bool. List.ofFn_const and List.sum_replicate_nat collapse the
column and row lists to cols*wG and rows*(cols*wG). Nat.mul_assoc matches the frozen RHS.
The generic formulas cover either dimension being zero. No scalar encoding, discrete log,
point-surjectivity, or algebraic representation of M is used.

All simp items are published equation/algebra lemmas. No foreign/core/Mathlib definition
is explicitly named in simp/rw/unfold; in particular flatten, ofFn, map and encG are consumed
only through their public readers/type. No additional import is proposed.

## Actual reuse searches and exact references

* Read current live Pairing/MatrixDH/Defs.lean:1-120, especially groupMatrixEnc_eq (59)
  and exact frozen length_groupMatrixEnc (67).
* Searched `(theorem|lemma) (length_flatten|length_flatMap|length_ofFn)|length_flatten|length_flatMap|sum_ofFn`
  over Mathlib List files and installed Lean Init/List/Lemmas.lean. Located core
  List.length_flatten at Init/Data/List/Lemmas.lean:1869 and List.length_ofFn in
  Init/Data/List/OfFn.lean:40.
* Searched `(theorem|lemma) (sum_ofFn|prod_ofFn|map_ofFn|ofFn_const|sum_replicate|prod_replicate)`
  over Mathlib/List, BigOperators, installed core List sources. Narrow reads verified:
  - Mathlib/Data/List/OfFn.lean:37, List.map_ofFn;
  - Mathlib/Data/List/OfFn.lean:117, List.ofFn_const;
  - Init/Data/List/Lemmas.lean:2350, List.sum_replicate_nat.
* `rg -n 'length_flatten.*map_ofFn|map_ofFn.*length_flatten|length_flatten.*length_ofFn'`
  over TCSlib/Mathlib found the existing public-list-reader proof pattern.
* Read TCSlib/Cryptography/Encoding/Modular.lean:75-96. Its encodeVector_length and
  encodeMatrix_length use the same generic List equations for scalar numeral words; they
  cannot directly apply to group words, but no scalar encoding is imported or copied.
* A search found consumer-specific length_flatten_of_length in PrivateKey/FromPRF/
  ReductionMachine.lean:535. No import/copy is needed: the already-published general List
  equations suffice, avoiding unrelated cryptographic machinery or a duplicate helper.
* Read Pairing/Group.lean encG field at line 130 in the immediately preceding serialization
  invocation; current search confirmed its fixed Fin wG return type.

Native focus is only ordinary recursive simplification of both ofFn/flatten layers and
availability of List.map_ofFn/List.ofFn_const in the current import closure. There is no
remaining mathematical obligation beyond the displayed generic length identities.
