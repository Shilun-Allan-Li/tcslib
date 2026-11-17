<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComposition.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.prod_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Componentwise execution of product protocols

**Claim.** On paired inputs, the product protocol returns the pair of outputs obtained by running each protocol on its corresponding input components.

**Proof.** Induct on the first protocol. If it is an output node with value $a_1$, the product construction runs the second protocol on the second input components and pairs its output with $a_1$. This is exactly the claimed pair, since the first protocol always returns $a_1$. If the first protocol begins with an Alice message, the product sends that message using the first input component, then continues with the product of the selected subtree and the second protocol. The induction hypothesis gives the two component outputs for this continuation, and the message and continuation are precisely those used by the first protocol on its inputs. If the first protocol begins with a Bob message, the same reasoning uses the first component of Bob's input. Thus the product execution returns the stated pair in all cases.
