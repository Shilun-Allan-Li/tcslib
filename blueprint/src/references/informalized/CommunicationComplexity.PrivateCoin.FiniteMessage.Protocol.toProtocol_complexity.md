<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toProtocol_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity Under Private-Coin Conversion

**Claim.** The binary protocol associated with a private-coin finite-message protocol has the same communication complexity as the original protocol.

**Proof.** The private-coin conversion to a binary protocol is the deterministic finite-message protocol conversion applied to the same protocol, with the paired randomness and input spaces as its inputs. The deterministic conversion preserves complexity (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_complexity`), which gives the asserted equality.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_complexity`.
