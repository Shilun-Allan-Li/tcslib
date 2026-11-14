# Manual review of the final public-provider reuse amendment

Previous candidate: `252ec646b9a5605c11aa245629a4ce8f404f74e8`.
Reviewed candidate: `47ced271090f45918645c842cd358c5079092754`.

The complete Git diff changes exactly one file:
`TCSlib/Cryptography/Authentication/Signatures/Lamport/Machine.lean`.
`Authentication.lean`, the owned `Lamport.lean`, every other helper, and all
other repository paths are byte-identical between these two commits.

The amendment adds the precise import
`TCSlib.Cryptography.Asymptotic.ReductionSupport`, removes the newly introduced
public `LamportMachine.take_poly` and `LamportMachine.drop_poly` lemmas, and
changes their former call sites to use the existing public
`TCSlib.Cryptography.takeLen_poly` and `TCSlib.Cryptography.dropLen_poly`.

The provider's declarations at `ReductionSupport.lean:248` and `:256` have exactly
the required types, up to binder names:

```lean
PolyTimeComputable a → PolyTimeComputable b →
  PolyTimeComputable (fun w => (b w).take (a w).length)

PolyTimeComputable a → PolyTimeComputable b →
  PolyTimeComputable (fun w => (b w).drop (a w).length)
```

Every replacement preserves the argument order and the same resulting lambda.
The affected consumers are `first_poly`, `second_poly`, `advIn_poly`,
`blocked_poly` and `out_poly`. Only their proof terms change. No computational
definition, handler field, reader equation, theorem statement, attribute,
namespace, section parameter or proof sketch is changed by this amendment.
The source search found no remaining `take_poly` or `drop_poly` reference under
the owned Lamport helper directory at the reviewed commit.

This resolves the exact public-lemma duplication debt: the two matching public
provider facts are now imported and used, and their local re-proofs are absent.
There is no new local alias concealing another copy.

One wording qualification is necessary: the amendment does intentionally remove
two **new helper API names**, `LamportMachine.take_poly` and
`LamportMachine.drop_poly`. Thus “no interface change whatsoever” would be too
broad. All **remaining** exported declarations retain their statements, and no
issue-base public API is removed, because `Machine.lean` and these two helper
names did not exist at the issue base. No local consumer still references the
removed names.

**Result:** the provider reuse and scope are correct in this source-only review;
no further source fix was identified. This review does not replace the guarded
Lean checks, final seals or axiom census for the amended candidate. No Lean was
run and no TCSlib source or existing evidence/report file was edited.
