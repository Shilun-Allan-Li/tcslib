<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.aux_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Containment of Auxiliary Leaf Rectangles

**Claim.** Every auxiliary leaf rectangle of a protocol constrained to $A\times B$ is contained in $A\times B$.

**Proof.** Induct on the protocol. At an output node, the only rectangle is $A\times B$ itself. At an Alice node, each rectangle comes from one of the two subprotocols with the first-input set restricted further to $A\cap\{x:f(x)=b\}$. By induction it lies in that smaller first-input set times $B$, and hence in $A\times B$. At a Bob node, each rectangle lies by induction in $A$ times the corresponding smaller second-input set, which is contained in $B$; it therefore lies in $A\times B$.
