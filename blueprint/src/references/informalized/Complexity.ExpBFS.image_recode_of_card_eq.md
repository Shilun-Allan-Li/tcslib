<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.image_recode_of_card_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Image of Reachable Codes Under Recoding

**Claim.** If the reachable-code sets for windows $s$ and $s+1$ have equal cardinality, recoding the window-$s$ set has image exactly the window-$(s+1)$ reachable-code set.

**Proof.** First, every element of the image comes from some code in the window-$s$ reachable set; recoding any such code produces an element of the window-$(s+1)$ reachable set (`Complexity.ExpBFS.recode_mem`). Thus the image is a subset of that larger-window set. Recoding is injective on the window-$s$ reachable set (`Complexity.ExpBFS.recode_injOn`), so the image has the same cardinality as that set. By the assumed equality of cardinalities, the image and the larger-window set have equal cardinality; a subset of a finite set with the same cardinality is the whole set.

**Key facts.** `Complexity.ExpBFS.recode_mem`, `Complexity.ExpBFS.recode_injOn`.
