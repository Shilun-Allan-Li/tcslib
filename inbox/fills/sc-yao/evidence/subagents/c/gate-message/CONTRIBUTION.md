# Subagent c: encoded gate-hybrid sampler endpoints

Source `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateHybridMessage.lean`. Namespace `...YaoHybridProof.GateHybridMessage`.
176 lines,width<=94,10 source/10 stored constants,no sorry/new simp attributes.

## Contract

message encodes GateHybrids.tableWith(stageBit), Alice's false-key blocks and
FakeObjects.decodePair ordered by output-wire values. sample places that
message and FakeObjects.activeAnswers in Bob's encoded View, then pairs the
encoded view with the prescribed Alice output. The outer order is exactly
pairEncode(view.encode)(aliceOutput). Every definition has its full equation.

activeAnswers_relabel identifies false active answers under the relabeled
seed with the original keys selected by the wire values. decodePair_relabel
identifies each output-value-ordered pair with the original false/true pair.
message_relabel composes these readers with GateHybrids.tableWith_start to
identify the entire real encoded payload with stage0 under the relabeled seed.
sample_relabel includes the original selected OT-key vector and gives the
full per-seed real-payload Bob-view identity with prescribed Alice output.

message_end is exactly FakeObjects.message at stage2*gatecount; sample_end
gives the corresponding canonical fake-message/active-answer view endpoint.
It matches FakeSimulator.idealB_eq after Bob's private tape is identified as
empty and the circuit's output-wire values are identified with the prescribed
Bob result. Those actual-protocol/functionality instantiations remain lead glue.

For H0=H1 the lead combines sample_relabel with the proved CoinSeedRelabel
seed_relabel and the existing acceptProb_comp_equiv. This module proves no
new probability fact and assumes no complete sampler identity.

## Reuse and overlap disclosure

This is the new parameterized hybrid message/view family approved by root.
The table/key/pair encoding mirrors the public real/fake encodings because
its endpoints must be exact; the fake message itself is consumed via
FakeObjects.message_eq, never copied or redefined as a second fake sampler.
The row/table semantics come only from GateHybrids. Its per-seed endpoint
proofs are direct compositions of published RelabelGarbling.keyAt_relabel,
GateHybrids.tableWith_start/tableWith_end and FakeObjects readers. Bool XOR
cancellation uses the core published equations. View is imported from its
precise defining module ZeroKnowledge.Interaction.

TwoMoveViews.realB_eq and encode_viewV_eq were consulted for the canonical
view shape; a's BobSimulator/FakeSimulator ideal endpoint readers supply the
matching ideal view. No protocol execution or probability machinery is
re-derived here. SY5 unmerged sc-garble search results are recorded alongside
the GateHybrids search; no matching hybrid semantic family was found in the
searched paths, and no unmerged helper or frozen-definition body is used.

## Verification

Final normal03 PASS. Final03-seals all4 strict/coe by evalA/B PASS with
-DmaxErrors=0. Axioms-02 enumerates all10 stored constants, standard axioms
only and every transitive closure sorried=[]. Final style lint0findings.
Both error forms counted in all result manifests. The original01 lexical
failure (reserved parameter name) and normal02 source are preserved. The
02 audit also passed; then its unused TwoMoveViews import was narrowed to
Interaction and the full normal/seal/axiom/style audit repeated on03.
No raw logs/probes were overwritten: final03-seals is a separate evidence tree.
Seal runners follow the previously provenance-recorded c/gate-hybrids tools
with evidence path changes only. Lead must run final merged checks.

No commits by this agent.
