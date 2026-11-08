<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.prod_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the product protocol

**Claim.** The private-coin product protocol returns the pair of outputs obtained by running each factor on the common public inputs and its own coordinates of the paired private coins.

**Proof.** The private-coin product is obtained by reindexing inputs of the deterministic product so that each factor receives its own coin and the common public input. The execution rule for reindexing (`Deterministic.FiniteMessage.Protocol.comap_run`) evaluates that product at exactly these inputs. The deterministic product execution theorem (`Deterministic.FiniteMessage.Protocol.prod_run`) says its output is the pair of the two factor executions on their respective input coordinates. Substituting the coin and public-input pairs gives the stated outputs.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.prod_run`.
