<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean :: CommunicationComplexity.flipAt_bijective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bijectivity of a single-coordinate flip

**Claim.** For any coordinate $i$, the operation that flips an input at coordinate $i$ is a bijection on the space of Boolean inputs.

**Proof.** Use the same flip as a proposed inverse. Applying it twice returns the original input, by the involution property of the single-coordinate flip (`CommunicationComplexity.flipAt_flipAt`). Thus every input is the image of its own flip, and if two inputs have the same image, flipping that common image recovers both inputs. The map is therefore surjective and injective, hence bijective.

**Key facts.** `CommunicationComplexity.flipAt_flipAt`.
