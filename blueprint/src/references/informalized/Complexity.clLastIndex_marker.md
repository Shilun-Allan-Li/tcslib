<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLastIndex_marker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marker Scan and Last Match

**Claim.** The length of the prefix before the last true entry in the word $(P(0),\ldots,P(n-1))$, when defined, is the last index below $n$ where $P$ is true, and is undefined when there is no such index.

**Proof.** Proceed by induction on $n$. For $n=0$, the word is empty, so there is no true entry and the tracker is undefined. For the successor step, write the word of length $n+1$ as the word of length $n$ followed by $P(n)$. The marker update rule (`Complexity.clLastMarker_step`) says that if $P(n)$ is true, the prefix before the last true entry is the entire length-$n$ word, of length $n$; otherwise the prefix is unchanged from the earlier word. The tracker obeys the same alternatives by its definition: it returns $n$ when $P(n)$ is true and otherwise retains its value at $n$. The induction hypothesis identifies the unchanged values, proving the result.

**Key facts.** `Complexity.clLastMarker_step`.
