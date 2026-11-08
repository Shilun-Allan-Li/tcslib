<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_trial_verdict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Step Verdict Phase

**Claim.** From the specified configuration, the verdict phase reads the bit $b$ to the left of the designated tape head, erases it, and reaches the done state recording $b$ after two steps. It does not reach a verdict state earlier, and its work heads stay within absolute position $1$.

**Proof.** Let $\mathrm{CAP}$ be the designated tape. Its cell immediately left of the head contains $b$, as follows directly from the initial one-symbol buffer and head position. Apply the verdict trace lemma (`b2b_verdict_trace`): after one step the machine moves the head left and enters read; after two, it reads and erases $b$, enters done with value $b$, and leaves the head at that cell. The initial head position is $1$, so the left move places it at the origin, and the erased tape together with the unchanged other tapes gives the claimed endpoint configuration. The trace at times $0$ and $1$ also establishes that no done state occurs earlier; its position updates show that every work head remains within absolute position $1$ throughout.

**Key facts.** `Complexity.b2b_verdict_trace`.
