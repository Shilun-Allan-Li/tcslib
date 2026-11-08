<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toProtocol_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution Preserved by Conversion

**Claim.** Converting a private-coin finite-message protocol to a binary protocol preserves its output for every input and every specified pair of private coins.

**Proof.** Both private-coin execution functions run their underlying protocols on the paired inputs formed from the coins and ordinary inputs. The deterministic finite-message conversion preserves the run function (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_run`). Applying that identity to the paired inputs gives equality of the two outputs.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_run`.

**Caveat.** The informal statement labels $p$ public-coin, but the formal statement and proof concern a private-coin finite-message protocol; the claim above follows the formal statement.
