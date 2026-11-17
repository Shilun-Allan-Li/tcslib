<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.deletePath_ne_none_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Deleting a Strict Subprotocol Yields a Protocol

**Claim.** If a subprotocol has strictly fewer leaves than the protocol containing it, deletion along the witnessing path returns a protocol rather than `none`.

**Proof.** Induct on the path. In the reflexive case the subprotocol is the whole protocol, so their leaf counts are equal, contradicting strict inequality. At a branching node, the path continues into one child. If deletion farther down that path returns a protocol, the definition of deletion returns a protocol at the current node as well. If it returns `none`, the path has reached its reflexive case; the strict leaf-count hypothesis rules this out, since the untouched sibling cannot make the whole protocol have strictly more leaves than the removed subprotocol in that case. Thus deletion is nonempty in each branching case.

**Caveat.** The supplied proof source omits the intermediate leaf-count reasoning in the branching cases, so the precise derivation of strictness for the recursive path is not visible there.
