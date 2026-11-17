<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.jeqIn_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Word Equality and Input Payload

**Claim.** The binary expansion of $oc$ equals the payload recovered from the paired input precisely when $oc=p$.

**Proof.** The pairing of the unary prefix with the binary expansion of $p$ has that binary expansion as its plain payload, by the payload-recovery fact (`Complexity.LogProg.plainWord_pairEncode`). The asserted word equality therefore becomes $\mathrm{Nat.bits}(oc)=\mathrm{Nat.bits}(p)$. Since the binary-expansion map is injective (`Complexity.LogProg.bits_injective`), this holds exactly when $oc=p$.

**Key facts.** `Complexity.LogProg.plainWord_pairEncode`, `Complexity.LogProg.bits_injective`.
