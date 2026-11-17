<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLastMarker_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a Marker

**Claim.** When a Boolean entry $b$ is appended to a word $w$, the prefix before the last true entry is $w$ if $b$ is true and otherwise is the prefix before the last true entry of $w$, with the value undefined when the relevant word has no true entry.

**Proof.** If $b$ is true, it is the last true entry of the appended word, so the prefix before it is exactly $w$. If $b$ is false, appending it adds no true entry, and the last true entry, if one exists, remains the last true entry of $w$ with the same preceding prefix. If $w$ has no true entry in this latter case, the result is undefined.
