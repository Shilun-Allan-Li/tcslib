# BilinearGen.mddhEnc_injective candidate

Status: scratch full candidate, inspection only; native verification pending. No Lean/lake/
build/Git/live edit/extra agent was run. Frozen header/prose copied byte-for-byte; one tactic
block, no remaining holes/sorry, no new helper/import/statement change; all lines ≤100.
The substantive dependency BilinearGroup.groupMatrixEnc_injective is still pending native
verification/integration, so no standard-only matrix-codec chain is claimed.

## Public-parameter API search and alignment

The current live parameter API provides PublicParams.encode_eq but NO encode_injective
lemma. This absence was searched before manual record reconstruction. A new public helper
is not required: the frozen existing theorem's sketch already specifies reading the public
encoding and applying group encoding injection. The proof uses exactly that route in one
concrete local hPP equality, then aligns pp BEFORE invoking matrix-codec injectivity.

Read mddhEnc_eq; Turing.pairEncode_injective separates pp encoding from the paired matrix
words. For hPP, destruct the actual two public-parameter records. PublicParams.encode_eq
and pairEncode_injective give equality of description words and generator words. Substitute
the description equality first, making the generator group types identical. Existing
List.ofFn_injective and encG_injective give generator equality. The record equality then
holds by reflexivity and proof irrelevance for reachability/nonidentity witnesses.

Eliminate hPP in the MAIN goal, so both challenge matrices now have the same dependent
source-group type. A second pairEncode_injective gives equal base/response words. Consume
the pending groupMatrixEnc_injective separately on those two exact types; constructor
reflexivity finishes. Neither matrix is assigned scalar exponents or passed through a
scalar encoding. Empty row/response-column dimensions are retained by the generic matrix
codec statement; no new positivity hypothesis is added.

Only published equation/injectivity readers are explicitly used. Record/subtype case and
equality elimination are primitive constructor reasoning, not generated foreign-definition
equation reads. No hidden group equivalence, DLOG, inverse encoder, or sampler is constructed.

## Actual source searches/inspections

* Read MatrixDH/Defs.lean:81-122 for MDDHChallenge fields, mddhEnc_eq and exact frozen target.
* `rg -n 'encode_injective|encode.*inj|inj.*encode|publicParams.*inj|eq_of_encode'` over
  MatrixDH/Parameters, Pairing, and FE/Defs/Raw found no public-parameter codec injectivity.
* `rg -n 'PublicParams.*(Equiv|encode|inj)|encode.*PublicParams|publicParams.*encode'`
  in PHFE/Raw and Parameters located only encode_eq and PHFE's identity-type parameter
  equivalence. That PHFE codec is downstream and would create a bad dependency here; it
  does not assert the needed word injectivity in any case.
* Read Parameters.lean:53-101 for the exact PublicParams fields, GroupDescription subtype
  and encode_eq (90). Read the earlier PairingDlinEncInjective scratch fragment for its
  closely related description-alignment pattern; it is not used as a pending dependency.
* Reconfirmed TuringMachine/Encoding.lean:173, pairEncode_injective, and
  Mathlib/Data/List/OfFn.lean:192, List.ofFn_injective. The public group encG_injective field
  is Pairing/Group.lean:132; pending groupMatrixEnc_injective is MatrixDH/Defs.lean:74.

## Overlap / possible future promotion

The short description-first/generator-second part parallels the prepared dlinEnc_injective
proof. Here it applies to the explicitly factored pp.encode component, while DLIN serializes
those fields as separate pieces of a longer tuple. No private proof is copied, and both
consume the same public pair/list/group injectivity APIs instead of re-proving them.
A future PublicParams.encode_injective lemma could centralize the two-field record step;
it has NOT been introduced or proved without native exact?/apply? searches. This candidate
needs only the concrete existing frozen theorem, as requested, and records that API gap.

Native focus is dependent rcases/equality elimination for pp, then unification of the base
and response dimensions when applying the pending matrix-codec reader. Correctness and
DLIN assumption admissions are not dependencies.
