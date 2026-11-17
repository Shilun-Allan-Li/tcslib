<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.IsSignValued.directProduct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Values of Direct Products

**Claim.** The direct product of two functions that are sign-valued at every input is sign-valued at every input.

**Proof.** Fix an input to the product cube and split it into its first and last coordinate blocks. By definition, the product function is the product of the values of the two given functions on these blocks. The absolute value of a product is the product of the absolute values; each factor has absolute value one by hypothesis. Thus the product has absolute value one.
