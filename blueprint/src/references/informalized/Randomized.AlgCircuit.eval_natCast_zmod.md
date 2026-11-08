<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.AlgCircuit.eval_natCast_zmod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation modulo a natural number

**Claim.** Let $C$ be an algebraic circuit on $n$ inputs, let $a$ assign a natural number to each input, and let $k$ be a natural number. Evaluating $C$ on the reductions of the inputs modulo $k$ gives the reduction modulo $k$ of its integer evaluation on $a$.

**Proof.** Apply the fact that a ring homomorphism commutes with circuit evaluation (`map_eval`) to the homomorphism from the integers to $\mathbb{Z}/k\mathbb{Z}$ and to the integer-valued inputs. It identifies the image of the integer evaluation with evaluation on the images of those inputs. Each image is precisely the corresponding natural number reduced modulo $k$, proving the stated equality.

**Key facts.** `Randomized.AlgCircuit.map_eval`.
