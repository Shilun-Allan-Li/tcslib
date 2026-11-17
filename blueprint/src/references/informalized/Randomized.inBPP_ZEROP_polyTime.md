<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.inBPP_ZEROP_polyTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Polynomial Identity Testing

**Claim.** The language of encodings of well-formed integer arithmetic circuits computing the zero polynomial belongs to BPP.

**Proof.** The proof first uses the theorem that this zero-polynomial language belongs to coRP in the polynomial-time model (\texttt{Randomized.inCoRP\_ZEROP\_polyTime}). The general inclusion of coRP in BPP then converts that membership into BPP membership (\texttt{Randomized.InCoRP.inBPP\_polyTime}).

**Key facts.** `Randomized.inCoRP_ZEROP_polyTime`, `Randomized.InCoRP.inBPP_polyTime`.
