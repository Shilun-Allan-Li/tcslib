<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a Value to a Segment

**Claim.** If $l$ records the values of $\mu$ starting at $a$, then updating $\mu$ at $a+|l|$ to $x$ makes the updated function agree with $l$ followed by $x$, starting at $a$.

**Proof.** First, the update leaves the original segment intact: the updated point $a+|l|$ is just beyond the indices used by $l$, so the update-outside-segment property applies (Light.Seg.update_out). The append characterization says that $l$ followed by a list $r$ is a segment exactly when $l$ is a segment and $r$ is a segment starting at $a+|l|$ (Light.seg_append). Take $r$ to be the one-entry list $[x]$. By the one-entry characterization of segments (Light.seg_cons), this remaining condition is that the updated function has value $x$ at $a+|l|$; this holds by the definition of the update. Together these facts give the claimed appended segment.

**Key facts.** `Light.Seg.update_out`, `Light.seg_append`, `Light.seg_cons`.
