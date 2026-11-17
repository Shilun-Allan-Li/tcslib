<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityStandardTail_layerCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity circuit tail layer count

**Claim.** For natural numbers $r$ and $q$ and a gate $g$ that is either AND or OR, the parity circuit tail constructed with parameters $r$, $q$, and $g$ has layer count $q+1$.

**Proof.** Induct on $q$, allowing the gate to vary. When $q=0$, the tail is the single output layer, so its layer count is one. At a successor index, the construction adds one layer before the standard tail at index $q$, with the dual gate. The induction hypothesis gives that remainder layer count as $q+1$, hence the new count is $1+(q+1)=q+2$, as required for index $q+1$.
