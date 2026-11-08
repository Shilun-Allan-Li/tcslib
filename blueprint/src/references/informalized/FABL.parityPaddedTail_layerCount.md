<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityPaddedTail_layerCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padded parity tail layer count

**Claim.** For natural numbers $n$, $r$, and $q$, the padded parity tail with parameters $n$, $r$, and $q$ has exactly $q+2$ layers.

**Proof.** By definition, the padded tail consists of one initial layer followed by the standard tail at parameter $q$. The layer count of the initial layer is one plus the layer count of its remainder. The standard tail has $q+1$ layers, so the padded tail has $1+(q+1)=q+2$ layers.
