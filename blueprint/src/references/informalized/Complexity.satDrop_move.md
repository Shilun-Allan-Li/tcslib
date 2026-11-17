<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satDrop_move -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a Silent Dropper Action

**Claim.** Under the stated input-position and counter-head displacement hypotheses, applying the action with input move $m$, counter move $d$, no counter write, optional output bit $b$, and target state $q'$ to the canonical configuration produces the canonical configuration with offset $i'$, counter head $h'$, and output $o$ followed by $b$ when present.

**Proof.** The action sets the successor state to $q'$ and moves the input head according to $m$, so the input-position hypothesis gives exactly the target clamped offset $i'$. It makes no counter write, so the counter tape remains unchanged. The counter head moves from $h$ to $h+d=h'$. Finally, the output tape appends the list represented by the optional bit, giving $o\mathbin{++}b.toList$. These componentwise equalities establish equality of the two configurations.
