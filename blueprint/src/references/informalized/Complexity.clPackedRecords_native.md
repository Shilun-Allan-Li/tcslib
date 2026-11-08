<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPackedRecords_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time computability of packed records

**Claim.** For every finite-state Boolean Turing machine $M$ and natural numbers $C,e,c,A,d$, the function sending a Boolean word $x$ to its packed records is computable in polynomial time.

**Proof.** The packed-records word is the pair encoding of three words: the prepared header, the machine's records, and the visit rows. The header is polynomial-time computable by `Complexity.clPrepHeader_native`; the records are polynomial-time computable by `Complexity.clRecords_native`; and the visit rows are polynomial-time computable by `Complexity.clVisitRows_native`. Pairing two polynomial-time computable functions preserves polynomial-time computability (`Complexity.clNative_pair`). Apply that result first to the records and visit rows, then to the header and the resulting encoding. This gives a polynomial-time machine for the full packed-records function.

**Key facts.** `Complexity.clPrepHeader_native`, `Complexity.clRecords_native`, `Complexity.clVisitRows_native`, `Complexity.clNative_pair`.
