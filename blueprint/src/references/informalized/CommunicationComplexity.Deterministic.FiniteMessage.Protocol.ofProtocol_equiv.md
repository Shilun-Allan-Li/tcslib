<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_equiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary-to-finite-message realization

**Claim.** Every binary deterministic protocol has a finite-message protocol with the same output on every input pair and the same communication complexity.

**Proof.** Take the finite-message protocol obtained by embedding the binary protocol via `ofProtocol`. The output-preservation theorem says that, for every input pair, this embedded protocol returns the same value as the original (`ofProtocol_run`). Thus their runs are equal as functions of the two inputs. The complexity-preservation theorem gives equality of their communication complexities (`ofProtocol_complexity`). Together these establish both required properties.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_complexity`.
