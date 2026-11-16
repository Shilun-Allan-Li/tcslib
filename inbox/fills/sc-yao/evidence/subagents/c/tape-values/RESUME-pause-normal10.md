# TapeValues relocation checkpoint

Saved 2026-11-16T02:52:31.724727+00:00.
User requested pause; no further proof edits or checks are running.
Last child check session85924 (TapeValues-10) completed PASS, exit0,zero errors/warnings.
All prior child check/seal/trace sessions also completed. No live child handles/PIDs.

## Exact current state

Source: TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TapeValues.lean.
SHA256 45cfdfb40f744c76ea9eac52177ea83eadc15b9b7a0ab429ee6ee0340f988e16.
326 lines,maxwidth=97,17 public declarations.
No sorry/admit; final normal10 PASS. No TapeValues seals/axiom/style checks yet.
The matching completed olean is included under oleans/.

Public interface: keyEmbedding/rowEmbedding and equation readers; Rest and
Rest_eq; equiv and equiv_eq; equiv_shift/equiv_key/equiv_nonce_first/
equiv_nonce_second/equiv_unused_key/equiv_unused_row; permutation with
permutation_eq/permutation_apply. Private helpers only compose existing
Mathlib image-split/currying/append/product equivalences.

The full target is Rest × structural raw data:
((Fin C.size→Bool→K) × (∀i,assignment_i→K×K)), K=Fin n→Bool.
Rest = full shift table × unused key block functions × unused row block functions.
The complementary coordinates are defined by the embedding ranges. All unused
gates/assignment codes remain there; no full-permutation uniformity is assumed.
hA uses C.gates[i.val].args.length<=2. No positive-width premise.

## Approved coordination

Root assigned this split as B1 priority. b confirmed this structural target
and will compose SeedCoordinates.paramEquiv/dataEquiv; DO NOT import that
module into TapeValues, since it depends on NonceCoordinates/SelectedSeed.
No new Index/Data alias is needed. The actual derived permutation must remain
a function of Rest's shift field; a.CoordinateSwap accepts this arbitrary P.
Caller proofs can use classical inference for Fintype Rest (not yet probed).

## Resume next

1. Revalidate saved source/hash and live jobs; do not duplicate a live check.
2. Prove seed_perm from caller hP using permutation_apply and equiv_shift.
3. Prove seed_eq from four addressed key/nonce-half/shift readers by product
   extensionality; RHS is the extracted raw data plus permutation(Rest).
4. Specialize to inverse tape: seed(ofFn(equiv.symm(p,d)))=(d.keys,d.nonces,
   permutation p), using Equiv.apply_symm_apply. Do not define another real seed.
5. Add explicit numeric unused-key/row-code membership contracts if useful:
   vertex>=C.size, gate>=gatecount, code>=2^arity. Existing forward unused
   readers already retain every complementary block.
6. Probe Fintype/Nonempty Rest and n=0/inverse endpoint; finish style/
   whole-file4seals/all-stored-constant axiom+dependency trace, preserving logs.
7. Send immutable handoff before root copies live evidence.

All Lean commands through LEAN_SLOT_TAG=sc-yao-c /private/tmp/sc-yao-lean-slot.sh
and explicit own TCSLIB_OLEANS=.lake/sc-yao-oleans. Never lake. Use check.py
under evidence/subagents/c/tape-values/. Whole declarations one proof per edit.
All errors counted by both error: and error(... forms.

## Previous immutable handoff

SamplerEndpoints is fully checked/audited and already sent to root:
/private/tmp/sc-yao-c-verified-sampler-endpoints.tar.gz
/private/tmp/sc-yao-c-verified-sampler-endpoints-SHA256SUMS
archiveSHA256 0c44358d91abec76d6f3b6160d8a721b685fc8226f00aca7066b8f4d96044222.
It has no real semantic definitions; root's SY1 correction was followed.
