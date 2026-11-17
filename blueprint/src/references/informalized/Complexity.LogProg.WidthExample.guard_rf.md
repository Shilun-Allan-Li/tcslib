<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean :: Complexity.LogProg.WidthExample.guard_rf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Configuration Invariant

**Claim.** For any input word $x$, bound $B$, program location $l$, and natural numbers $i,p,t,u\le B$, the configuration at $l$ with registers $(i,p,t,u)$ and no answer satisfies the search program's precondition and has every register at most $B$.

**Proof.** The register bound follows coordinate by coordinate: the four values of the register function are $i,p,t,u$, each at most $B$ by hypothesis. For the precondition, inspect the instruction at each program location. The only equality test between registers is at the enumeration location, where it compares registers $3$ and $1$; these are distinct indices. The only calls use the one-element argument lists $[0]$ and $[3]$, which have no repeated entries. The input-validity conditions apply only at input equality tests, and this program has none. Thus every instruction satisfies the relevant clause of the precondition.
