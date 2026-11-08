<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Cfg.SameOutside.keep_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank tape preserved outside an empty set

**Claim.** If two configurations agree outside a set of positions for a given tape, that set is empty, and the first tape is blank everywhere, then the second tape is blank everywhere.

**Proof.** Fix any position $q$. Since the footprint for this tape is empty, $q$ lies outside it. The configurations therefore agree at $q$, so the second tape’s value there equals the first tape’s value, which is blank by hypothesis. Since $q$ was arbitrary, the second tape is blank everywhere.
