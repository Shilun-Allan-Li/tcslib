<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.measurable_absoluteTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of the Absolute Tail

**Claim.** For every finite measure $\nu$ on $\mathbb{R}$, the function $t\mapsto\nu(\{x\in\mathbb{R}:t<|x|\})$ is measurable.

**Proof.** If $s\le t$, then $\{x:t<|x|\}\subseteq\{x:s<|x|\}$, so the absolute tail is antitone. A real-valued antitone function on $\mathbb{R}$ is measurable. Finiteness of $\nu$ ensures that the measure-valued expression is real-valued.
