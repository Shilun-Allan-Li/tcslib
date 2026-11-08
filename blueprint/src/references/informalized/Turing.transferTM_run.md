<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.transferTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Tape Transfer Run

**Claim.** Starting with the source word on the source tape and an empty destination tape, the transfer machine finishes after a bounded number of steps, with the word moved to the destination and all other tape words unchanged; it has not reached its done phase earlier.

**Proof.** Apply the general transfer-run result to the configuration formed from the given tape words. Its hypotheses hold: the initial state is the sweep phase, the source tape contains the source word in buffer form, and the other tape positions and contents have the required initial form. That result gives the run’s final configuration, the fact that done is not reached at any earlier time, and the tape contents after the transfer. Taking $T=2|w_{\mathrm{src}}|+2$ satisfies the requested bound, since $2n+2\leq 3n+3$ for every natural number $n$. In the final tape description, the source interval has been erased and the destination interval contains the buffered source word. The empty destination assumption and the distinctness of the two indices ensure that the nested updates produce exactly the stated source and destination words; every other tape retains its original contents.

**Key facts.** `Turing.transferTM_run_ofCfg`.
