<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toDeterministic_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution commutes with fixing randomness

**Claim.** For a public-coin finite-message protocol, the deterministic protocol obtained by fixing $\omega$ returns on $x,y$ the same output as the original protocol run with shared randomness $\omega$.

**Proof.** The deterministic protocol is the pullback of the original protocol along the maps $x\mapsto(\omega,x)$ and $y\mapsto(\omega,y)$. The pullback execution formula (`comap_run`) says that running this protocol on $x,y$ agrees with running the original on the images of those inputs. Those images are precisely $(\omega,x)$ and $(\omega,y)$, and that execution is the randomized execution by definition.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`.
