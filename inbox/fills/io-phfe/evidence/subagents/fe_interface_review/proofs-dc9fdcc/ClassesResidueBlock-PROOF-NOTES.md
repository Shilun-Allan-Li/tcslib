# Classes.decodeResidues_block proof draft after native reuse searches

Status: one proof block for the searched proposed helper, inspected but not elaborated.
No live files edited; no Lean, lake, build, or Git commands. No further helper or import
is proposed. Native elaboration remains with the root.

## Deliverable and exact search match

`ClassesResidueBlock.proof.lean.inc` contains the full proposed docstring, proof sketch,
exact searched header, and proof. A Python assertion matched its header to the anonymous
example in `evidence/search/classes-residue-block/ClassesResidueBlockExact.lean.txt`,
changing only `example` to the proposed theorem name. The docstring was preserved from
`ClassesResidueBlock.statement.lean.inc` verbatim.

Exactly one tactic block; no admitted terms or additional helpers; maximum line width
83 columns. The helper is total for arbitrary positive p and every fixed-length word:
there is no p<=2^width, canonical-word, prime, positive-width, or in-range-block condition.
The last operation is the same natural-to-ZMod cast from decodeResidues_apply; therefore
a noncanonical block value remains reduced modulo p, not rejected. At width zero both
lists are empty; count zero supplies no coordinate i.

## Native reuse-search prerequisite already satisfied

Read-only native evidence:
`evidence/search/classes-residue-block/run/results.jsonl`.

- Exact probe: rc1, one expected inability-to-close error, no sorry; source SHA-256
  `7b24bfa998da888383e41706d44690982fd6339f9a100181744270238195c989`.
- Apply probe: rc0, but still one admitted search result; source SHA-256
  `6b9e39f0b35a54d48522f38fc59db8d6f87221d76920858e87ed895ca019b54a`.
- Both root-run records completed on 2026-11-18 around 14:35 UTC. Parent reported only
  partial irrelevant ZMod equality suggestions; no complete existing proof was found.
- Both archived source tails contain only the prefix through decodeResidues_apply,
  the anonymous target and namespace end; helper and later Classes admissions are absent.

The rc0 apply? result is **not** a proved target. These records satisfy the prerequisite
to draft this source-specific bridge, not a native check of this candidate proof.

## Proof structure and reused APIs

1. `decodeResidues_apply` changes the decoder coordinate to a cast of the exact drop/take
   list block. Congruence through listToNat and the residue cast reduces the goal to
   equality of two bit lists.
2. `List.ext_getElem` supplies length and element goals. Published length readers give
   `min width (count*width - i.val*width) = width`. The existing coordinate bound
   `i.isLt`, multiplied by width via `Nat.mul_le_mul_right`, bounds the whole row;
   `Nat.succ_mul` and omega close this elementary natural-subtraction inequality.
3. The published take/drop/ofFn element equations read a coordinate as
   `word` at offset `i.val*width + j`. `finProdFinEquiv_apply_val` reads the canonical
   coordinate as `j + width*i.val`; natural addition/multiplication commutativity and
   `Fin.ext` identify the two finite indices.

No generic list-slice, vector-reindex, encoding, or decoder algorithm is redefined.
The nearest Encoding.ModularDecode hblock/hchunk arguments are local proof facts and
are not referenced. The proof consumes public list/Fin equations only; no foreign
TCSlib/Mathlib/core definition is passed to simp/rw/unfold, and no generated defining
equation is used. finProdFinEquiv_apply_val is its published simps projection reader.

Exact public sources inspected:

- `Classes.lean:140`, `decodeResidues_apply` (only local decoder dependency).
- Pinned core `Init/Data/List/Lemmas.lean:292`, `List.ext_getElem`.
- Core `Init/Data/List/Nat/TakeDrop.lean:29`, `List.length_take`;
  same file :49, `List.getElem_take`; :234, `List.getElem_drop`.
- Core `Init/Data/List/OfFn.lean:40`, `List.length_ofFn`; :47,
  `List.getElem_ofFn`.
- Mathlib `Logic/Equiv/Fin/Basic.lean:325`, declared simps projection reader
  `finProdFinEquiv_apply_val`, giving second+width*first.
- Existing `List.length_drop`, `Nat.min_eq_left`, `Nat.mul_le_mul_right`,
  `Nat.succ_le_of_lt`, `Nat.succ_mul`, `Nat.add_comm`, `Nat.mul_comm`, and `Fin.ext`.

No existing admitted Classes result is a dependency. The current imported modules
already provide the used generic list/finite-coordinate equations and omega.

## Actual additional searches and reads

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
cat /private/tmp/io-phfe-drafts/proofs-fe/ClassesResidueBlock.statement.lean.inc
sed -n '115,182p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
rg -n 'drop_ofFn|take_ofFn|ofFn_drop|ofFn_take|take.*ofFn|drop.*ofFn' /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean .lake/packages/mathlib/Mathlib .lake/packages/batteries | head -65
sed -n '318,350p' .lake/packages/mathlib/Mathlib/Logic/Equiv/Fin/Basic.lean
rg -n 'theorem (length_drop|length_take|drop_take)|lemma (length_drop|length_take|drop_take)|getElem_drop|getElem_take' /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/List/Nat/TakeDrop.lean | head -55
rg -n 'take_ofFn|drop_ofFn|ofFn_drop|ofFn_take' .lake/packages/mathlib/Mathlib/Data/List/OfFn.lean /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/List/OfFn.lean
sed -n '25,54p' /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/List/Nat/TakeDrop.lean
sed -n '221,240p' /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/List/Nat/TakeDrop.lean
sed -n '38,51p' /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/List/OfFn.lean
sed -n '126,141p' .lake/packages/mathlib/Mathlib/Data/Fin/Tuple/Take.lean
rg -n -A 5 -B 3 'theorem ext_getElem|theorem length_drop|theorem length_ofFn' /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/List/Lemmas.lean /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/List/Nat/TakeDrop.lean /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/List/OfFn.lean | head -50
rg -n 'ofFn.*(drop|take)|drop.*ofFn|take.*ofFn' .lake/packages/mathlib/Mathlib/Data/Fin/Tuple | head -40
cat evidence/search/classes-residue-block/run/results.jsonl
tail -23 evidence/search/classes-residue-block/ClassesResidueBlockExact.lean.txt
tail -23 evidence/search/classes-residue-block/ClassesResidueBlockApply.lean.txt
```

There is no published full row-slice List.drop_ofFn/take_ofFn pair in the searched
roots. The nearby `Fin.ofFn_take_eq_take_ofFn` (Mathlib Data/Fin/Tuple/Take:135) handles
only a prefix and does not address the offset row/drop. Using it would still need
an offset/cast alignment and a new precise module import. The existing list
extensionality and take/drop coordinate readers are the direct complete API here.

The earlier broader reuse inventory remains in `ClassesResidueBlock-SEARCH.md`.
No additional public helper was introduced to manufacture this proof.

## Pending validation

Textual header/doc equality, one tactic block, line width, and no-admission checks
passed. Native typechecking, binder/proof-irrelevance normalization and standard-axiom
checks remain with the root. No mathematical obstruction or semantic weakening was found.
