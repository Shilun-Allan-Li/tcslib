<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_action_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty action serialization

**Claim.** For every natural number $n$ and every action of a one-work-tape binary Turing machine with state set $\{0,\dots,n\}$, the action serialization has length at least $1$.

**Proof.** The serialization begins with the encoding of the input-tape movement. Each of the three possible movements has a two-bit encoding, so this initial block alone has length $2$. The remaining fields are concatenated after it and cannot reduce the length. Hence the full serialization has length at least $1$.
