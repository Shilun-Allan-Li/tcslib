# Classes duplicated-word bridge: search-only proposal

Status: statement/probe preparation only. No helper proof, live source edit, Lean, lake,
build, or Git command. The statement's term `sorry` is an intentional scratch placeholder,
not a delivered proof and not authorized for promotion as a new live admission. Root must
run exact?/apply? on the anonymous target before commissioning a helper proof.

## Exact missing helper and why it is enough

`ClassesResidueBlock.statement.lean.inc` proposes one public technical reader,
`decodeResidues_block`, placed immediately after `decodeResidues_apply`:

```lean
theorem decodeResidues_block (p : ℕ+) (count width : ℕ)
    (word : Fin (count * width) → Bool) (i : Fin count) :
    decodeResidues p count width word i =
      (listToNat (List.ofFn (fun j : Fin width => word (finProdFinEquiv (i, j)))) :
        ZMod (p : ℕ))
```

It states that a residue coordinate is read from precisely its canonical finite-product
bit block. It requires **no** p<=2^width, prime, positive width/count, encoder-image,
canonical-word, or in-range-block hypothesis. Thus it preserves total interpretation:
a block whose natural value is at least p is reduced modulo p, never rejected.
Width zero gives the empty block and zero residue. Count zero has no coordinate i.

This pointwise block bridge is preferable to introducing an append/concatenation
algorithm or an arbitrary row-reindexing theorem. It is reusable for any fixed-width
residue word and exactly matches duplicatePrivateBits' current coordinate-level API.
No new runtime operation, representation, decoder, or sampler is introduced.

The eventual existing `phfeClass_eval_eq_quad` proof can read
`phfeClass_eval`, `quadClass_eval`, and `phfeEval_eq`. Apply the proposed block reader
at `Fin.castAdd n i` and `Fin.natAdd n i`, then the already-published
`duplicatePrivateBits_eq`, `Equiv.symm_apply_apply`,
`finSumFinEquiv_symm_apply_castAdd` / `_natAdd`, and `Sum.elim_inl` / `_inr`.
Each duplicate's row bit list becomes the exact original row bit list. The decoded
private vectors therefore agree coordinatewise even for noncanonical aliases. No
extra generic concatenation or duplicate-specific public theorem is presently proposed.

## Reuse findings

Existing `decodeResidues_apply` exposes a List.drop/List.take block, not its finite
row-major coordinate function. `Encoding.ModularDecode` exposes guard, failure, encoding
round-trip, and matrix-reindexing readers; it has no public arbitrary-word block or
append reader. The nearby block equalities in its round-trip proofs are *local hblock /
hchunk proof steps*, not public APIs, and should not be copied as a second generic
public list lemma.

Important existing APIs to reuse in the eventual proof:

| API | Source | Role |
| --- | --- | --- |
| `decodeResidues_apply` | Classes:140 | Direct cast of the exact drop/take block |
| `List.ext_getElem` | Core List | Prove the two finite block lists equal |
| `List.length_ofFn`, `List.length_take`, `List.length_drop` | Core List | Exact block length |
| `List.getElem_take`, `List.getElem_drop` | Core Init/Data/List/Nat/TakeDrop:49,234 | Read a sliced coordinate |
| `List.getElem_ofFn` | Core Init/Data/List/OfFn:47 | Read the supplied fixed-width word |
| `finProdFinEquiv_apply_val` | Mathlib Logic/Equiv/Fin/Basic:325 via declared simps reader | Canonical bit offset j+width*i |
| `List.ofFn_mul` | Mathlib Data/List/OfFn:67 | Alternative published block flattening |
| `List.drop_take_succ_flatten_eq_getElem` | Mathlib Algebra/BigOperators/Group/List/Lemmas:136 | Alternative generic flattened-block slice |
| `finSumFinEquiv_symm_apply_castAdd`, `_natAdd` | Mathlib Logic/Equiv/Fin/Basic:236,246 | Select the two duplicated residue rows |

The alternative generic flatten/slice lemma is already reused in ModularDecode:94 and
SIS/Encoding:190. Prefer these APIs over re-proving a generic list-slice theorem.

`Encoding.DyadicUniform.bitsToVector` was also inspected: its deterministic coordinate
reader is already the same listOfFn-to-residue operation on curried bit blocks, via
`bitsToVector_apply` and `bitsToResidue_eq`. It does **not** bridge the existing
uncurried decodeResidues API to its curried input, so it does not eliminate the proposed
reader. No import is needed merely to wrap that equivalent cast notation, and no dyadic
uniformity result is needed. This proposal changes no existing Encoding module.

## Exact?/apply? probe target and isolation

`ClassesResidueBlock.probe.lean.inc` is a single anonymous example with one `exact?`
search block. Root should prepare a Classes prefix ending immediately after the current
`decodeResidues_apply` proof (before the docstring beginning `Equal modulus values`).
Append that target and the matching namespace end; add precise
`import Lean.Elab.Tactic.LibrarySearch` with the prefix imports. The prefix must not
import full Classes or load this proposed helper, the later existing admitted
`phfeClass_eval_eq_quad`, or the Classes statement placeholder.

Run the same anonymous target twice, first exact? and then by replacing just that token
with apply?. Keep full native diagnostics, suggested terms and remaining goals. A
trailing section/namespace typo is not a successful probe. No search has been executed
for this helper in this invocation; requested searches=2, verified search records=0.
If a complete published match is found, consume it and drop the helper proposal.

## Cycle-free home and file-size fallback

Current live Classes is 569 lines. No split is needed solely for this short reader.
The `pad_one` completeness proof is the principal size uncertainty: selecting padded
ordered tuples, grouping coefficients, and reindexing the polynomial support may add
several hundred lines. Splitting only after the file exceeds 1000 is avoidable.

A cycle-free refinement, preserving namespaces and public theorem headers:

1. Move current class/representation definitions and ordinary readers into
   `FunctionalEncryption/Classes/Defs.lean`. Keep the decoder/block bridge next to
   decodeResidues there. Defs imports FE.Defs.Raw and the precise modular/finite tuple
   roots, never the parent Classes facade.
2. Put larger encoding/embedding proofs in `Classes/Embedding.lean`, importing
   `Classes.Defs` (and precise Mathlib proof roots). Public names remain unchanged.
3. Put `BidegreeAtMost`, its reader, and `pad_one` with its substantial completeness
   support in `Classes/Completeness.lean`, importing `Classes.Defs` and the precise
   MvPolynomial roots; import Classes.Embedding only if the eventual proof needs it.
4. Make existing `FunctionalEncryption/Classes.lean` a proper facade importing Defs,
   Embedding, Completeness, with corresponding Contents/References prose.

The resulting direction is FE.Defs.Raw -> Classes.Defs ->
Classes.{Embedding,Completeness} -> Classes facade -> current Layered/Quadratic/PHFE.Data
consumers. No child imports the parent facade, so no cycle occurs. Existing downstream
imports continue to work. All moved names stay under their original namespace and
headers; audits/source-line inventories/import closures must be refreshed for the move.
This is a proposal only: no module was created or moved here.

## Actual search/read record

Working tree: `/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

- Read Classes ranges 305-370, 417-537, 535-570; ModularDecode ranges 40-85,160-265,
  132-164; current direct Classes import consumers; measured Classes=569 and
  ModularDecode=258 lines with `wc -l` (later source edits may shift locations).
- Name/shape search:

  ```sh
  rg -n 'decodeResidues.*append|decodeResidues.*duplicate|decodeVector.*append|append.*decodeVector|decodeVector.*concat|decodeVector.*block|decode.*take.*drop|decode.*castAdd|decode.*natAdd' TCSlib/Cryptography/Encoding TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption .lake/packages/mathlib/Mathlib | head -75
  rg -n 'decodeResidues.*block|decodeResidues.*row|decodeResidues.*prod|decodeVector.*row|decodeMatrix.*row|decodeVector.*ofFn|decodeMatrix.*ofFn|listToNat.*finProdFinEquiv|listToNat.*ofFn' TCSlib/Cryptography .lake/packages/mathlib/Mathlib | head -80
  rg -n 'decodeResidues.*(reindex|row|block)|decodeVector.*(reindex|row|block)|decodeMatrix.*(append|block)|ofFn.*drop.*take|drop.*take.*ofFn' TCSlib/Cryptography/Encoding TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption .lake/packages/mathlib/Mathlib/Data/List/OfFn.lean
  ```

- Generic tuple/list reuse searches included `ofFn_append`, `append_left/right`,
  `ofFn_mul`, `drop/take...ofFn`, `getElem_take/drop`, `drop_take_succ_flatten...`,
  finite-sum equivalence readers, and finite-product coordinate simps readers.
  Read Mathlib List/OfFn:25-95, Tuple/Basic append readers, Logic/Equiv/Fin/Basic:216-250,
  322-349, Group/List/Lemmas:128-144, and existing SIS/Encoding:168-209.
- Read DyadicUniform:45-140 and searched all its bitsToVector/Matrix readers plus
  crossreferences to decodeVector; no existing decodeResidues bridge was found.
- An initial generic search included nonexistent `TCSlib/NumberTheory`; the correct
  namespace directory is `TCSlib/Cryptography/NumberTheory`. A speculative
  Logic/Equiv/Fin/Prod.lean path also did not exist. Searches over the actual Mathlib
  roots located the equivalence and generic slicing declaration as listed above.

Live Classes SHA-256 at preparation: 49f4874d3244b2de7dfce02ab50c1840fe616844939766a030a11e2c6b1e96bc.
No mathematical obstruction was found. The remaining work is a short representation
bridge plus published coordinate-reader consumption, with exact?/apply? still required.
