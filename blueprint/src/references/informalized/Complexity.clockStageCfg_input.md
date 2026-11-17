<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.clockStageCfg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Input Reads

**Claim.** In the clock-stage configuration associated with $c$, replacing a nonblank input read by false and leaving a blank read blank gives the same result as applying that replacement to the input symbol read by $c$.

**Proof.** The clock-stage configuration retains $c$'s input-head position, and the embedded input has the same length as $x$. The input-symbol convention therefore gives the same read in both configurations, including the blank cases at the two boundary positions. Mapping a present read to false and leaving an absent read absent preserves that equality.
