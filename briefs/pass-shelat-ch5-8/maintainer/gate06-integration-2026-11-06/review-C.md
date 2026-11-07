# Internal Gate 06C route review

Read-only internal reviewer, source merge `0a549ec16dd44b8d3694c3a23a04f943b63fcf2d`.
No edits, Lean/cache runs or Git mutations. Proposed proof terms remain unchecked.
No new user ruling was identified as necessary.

1. Delete SequentialZK's local Protocol.ProverBounded (identical to Interaction's) and its
   inventory entry. Read it through Protocol.proverBounded_iff. EfficientProverProof(Err)
   already expose boundedP; InteractiveProof.complete supplies the honest message bound.
2. Replace PerfectZKAbort.seqRep's admission with
   `simpa only [one_div] using StatZK.seqRep h.statZK hB Q`.
   Its sketch should cite the existing abort-to-statistical bridge's retries, followed by
   multiplication of the error by Q. Use [Gol01] consistently.
   Adjacent Rule 10 gap: PerfectZK.seqRep unfolds foreign PerfectZK. Add public
   `perfectZK_iff : PerfectZK π R ↔ StatZK π R (fun _ => 0) := Iff.rfl`
   beside the definition, then consume it and the public input bridge with mul_zero.
3. G3-7d's 3COL corollary can use Q(N)=2(N+1)^2, PolyExpr.normal 2 2, combining
   col_efficientProverProofErr, EfficientProverProofErr.seqRep/.efficientProverProof,
   col_zk and ZK.seqRep with boundedP. Quantitative negligibility still needs proof:
   eventually 2^-N ≤ 1/(2N), so (1-1/(2N))^(2N^2) ≤ exp(-N) ≤ 2^-N.
   Available APIs include one_sub_inv_pow_mul_le_exp, exp_neg_le_inv_two_pow,
   negligible_two_pow_neg and Negligible.mono. A small Composability/ThreeColoring leaf is
   appropriate; cite PS10 Theorem 124.1, Propositions 127.6/128.8, Theorem 175.1 and declare
   the larger polynomial phase count. Generic seqRep has different scheduling from the
   existing colProtocolRep; do not identify them without a proof.
4. DL-6: Lamport already consumes public coinBlock. Move the shared implementation/equation
   and length lemma to an existing upstream home such as Asymptotic/Adversary; reconcile and
   retire phaseSlice, global coinSlice and shadow GI.coinSlice. Use the public equation,
   avoiding explicit foreign unfolding. Ledger's Lamport-definition entry is stale.
   DL-7: Collection.ofFn_padFin_of_le is in CollectionsHelpers and returns the input followed
   by padding. Equal-length uses must simplify ha, Nat.sub_self, List.replicate_zero and
   List.append_nil; remove the duplicate Lamport lemma after repointing its uses.

**Not yet clear to merge — integration edits, a quantitative negligibility lemma and verification remain.**
