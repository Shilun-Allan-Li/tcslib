<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.pi_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product execution by coordinates

**Claim.** Running the product of private-coin protocols returns the function whose value at each coordinate is the output of that factor on its corresponding private coins and the common inputs.

**Proof.** The private-coin product first forms the deterministic product protocol on input coordinates consisting of a coin and a public input, then reindexes a coin vector together with the common public input. The execution rule for reindexing (`Deterministic.FiniteMessage.Protocol.comap_run`) evaluates the deterministic product at precisely those coordinate inputs. The deterministic product execution theorem (`Deterministic.FiniteMessage.Protocol.pi_run`) states that its output at each coordinate is the corresponding factor's execution. Substituting the paired coins and public inputs yields the asserted componentwise equality.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.pi_run`.
