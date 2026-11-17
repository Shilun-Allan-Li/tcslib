<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRecordArgument_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Recorder Layout

**Claim.** For every finite-state Boolean Turing machine $M$ and natural numbers $C,e,c,A,d$, the function sending a Boolean word $x$ to the packed encoding of the recorder layout formed from the arithmetic preparation header with these parameters is polynomial-time computable.

**Proof.** First form the arithmetic preparation header from $x$. The preparation-header result states that this map is polynomial-time computable (`clPrepHeader_native`). The header-layout result states that, for fixed $M$, converting a header into the packed encoding of its recorder layout is polynomial-time computable (`clHeaderLayout_native`). Applying the polynomial-time composition theorem to these two maps shows that their composite is polynomial-time computable (`PolyTimeComputable.comp`). This composite is precisely the function in the claim.

**Key facts.** `Complexity.clHeaderLayout_native`, `Complexity.clPrepHeader_native`, `Complexity.PolyTimeComputable.comp`.
