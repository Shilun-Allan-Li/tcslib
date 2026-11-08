<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean :: CommunicationComplexity.Deterministic.OneWay.Protocol.toFiniteMessage_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of the finite-message embedding

**Claim.** The finite-message protocol obtained from a one-way protocol has complexity equal to the one-way message cost plus the ceiling of the base-two logarithm of the output type's cardinality.

**Proof.** The embedding first has Alice send a message from the original codebook, then has Bob send an index in a finite type of cardinality $|\alpha|$, and finally outputs the value represented by that index. The finite-message complexity adds the ceiling-logarithmic cost of each message type to the maximum complexity of its continuations. The terminal output has complexity zero; since the continuation families are nonempty, their supremum is their constant complexity. Thus the two successive message costs are $\mathrm{cost}(p)$ and $\lceil\log_2 |\alpha|\rceil$, giving the stated sum.
