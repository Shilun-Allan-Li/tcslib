<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_body_start_guarded -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guarded body initialization

**Claim.** The body machine with stopped flag false reaches the anchor carrying $w$ false bits within the stated bound, and it is not at the anchor at any earlier time.

**Proof.** First apply body initialization with the stopped flag enabled. It supplies a time $r$ within the claimed bound and the required anchor configuration. The stopped-true and stopped-false machines have identical transitions away from the anchor, while the stopped-true machine loops at the anchor. The first-anchor principle therefore yields a time $t\le r$ at which the stopped-false machine first reaches the anchor, with the same endpoint. Its avoidance clause says that at every earlier time its state differs from the anchor state, which is exactly the required guard.

**Key facts.** `Complexity.enumCont_body_start`, `Complexity.enumCont_body_agree`, `Complexity.enumCont_first_anchor`.
