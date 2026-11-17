<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RandomBooleanFourierMaximum.lean :: FABL.signValue_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplicativity of sign values

**Claim.** For any signs $a$ and $b$, the real value of their product is the product of their real values.

**Proof.** The real value of a sign is obtained by viewing its underlying integer as a real number. The underlying integer of the product of two units is the product of their underlying integers, and the integer-to-real map preserves multiplication. Therefore $\operatorname{signValue}(ab)=\operatorname{signValue}(a)\operatorname{signValue}(b)$.
