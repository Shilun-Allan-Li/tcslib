# Existing Classes.phfeClass_eval_encoded proof draft

Status: exact-header/prose replacement, inspected but not natively elaborated. No live
source edits, Lean, lake, build, or Git commands. No helper or new import is proposed.

## Deliverable

`ClassesPhfeClassEvalEncoded.lean.inc` preserves the complete current frozen docstring,
source tag, proof sketch, and theorem header of `phfeClass_eval_encoded`; only its
existing admitted body is replaced. A Python assertion matched that live block.
One tactic block, no admitted terms, maximum line width 86 columns.

Proof body:

```lean
  rw [phfeClass_eval, decodeTensor_encodeTensorBits (w.eval kappa) hwidth C,
    decodeResidues_encodeVector p (l.eval kappa) (w.eval kappa) hwidth x xword hx,
    decodeResidues_encodeVector p (n.eval kappa) (w.eval kappa) hwidth y yword hy]
```

## Exact reused APIs

- `Classes.lean:402`, `phfeClass_eval`, exposes the class evaluation as phfeEval of
  the decoded coefficient tensor and decoded public/private residue vectors.
- `Classes.lean:258`, `decodeTensor_encodeTensorBits`, restores C under the supplied
  hwidth. The root reports this round trip is now natively proved via the published
  modular matrix parser round trip.
- `Classes.lean:196`, `decodeResidues_encodeVector`, restores each of x and y from
  the existing hx/hy word equalities under that same hwidth. Root reports this API
  is natively proved.

The exact arguments are written explicitly for both vector dimensions and the width;
there is no fresh cast lemma, encoding inverse, or pointwise list argument. Only
published readers/round trips are passed to rw. No class bundle, tensor decoder,
encoder, or other foreign definition is unfolded; no generated equation is used.
The proof has no admitted dependency among these APIs as inspected/reported now.

The original width-coverage condition and both canonical-word equalities are retained
unchanged. They establish representation completeness only; this proof makes no claim
that arbitrary noncanonical words are rejected. Arbitrary-word decoding remains total
modulo p. Zero public/private dimensions, width zero when hwidth permits it, and degree
zero are handled by the existing round trips without further hypotheses.

## Actual searches/reads

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
rg -n -A 26 -B 10 'theorem phfeClass_eval_encoded|theorem phfeClass_eval ' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
rg -n -A 15 -B 5 'theorem decodeTensor_encodeTensorBits|theorem decodeResidues_encodeVector|theorem decodeResidues_block' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
rg -n 'phfeClass_eval_encoded|decodeTensor_encodeTensorBits|decodeResidues_encodeVector' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption
rg -n 'rw \[.*eval,.*decode|simpa only \[.*eval.*decode' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption | head -25
```

The searches confirmed exact reader/round-trip matches and no need for a new helper.
The last assembly-pattern search found no matches; no existing helper body was copied.

## Validation limits and findings

Textual frozen header/prose, width, single-block, and no-admission checks passed.
Native elaboration, standard-axiom check, and inventory refresh remain with the root.
No false or unattainable statement or missing public reader was found. The separate
`phfeClass_eval_eq_quad` theorem is not drafted in this invocation.
