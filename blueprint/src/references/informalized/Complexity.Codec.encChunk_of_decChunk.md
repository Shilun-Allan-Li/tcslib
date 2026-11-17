<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.encChunk_of_decChunk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding preserves the encoded chunk

**Claim.** If decoding a Boolean list $ch$ yields the cell value $cv$, then encoding $cv$ reproduces $ch$.

**Proof.** By definition, decoding returns a value only when there exists a cell value whose encoding is $ch$; in that case it returns a chosen such value. The hypothesis that decoding equals $\mathrm{some}(cv)$ identifies $cv$ with that chosen value. The defining property of the choice therefore gives $\mathrm{encChunk}(cv)=ch$.
