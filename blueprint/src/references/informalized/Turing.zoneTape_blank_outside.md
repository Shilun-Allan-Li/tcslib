<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneTape_blank_outside -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tape Blank Outside the Zones

**Claim.** If $|c|>2b_\ell+1$, the tape content at cell $c$ is blank.

**Proof.** First, the strict bound on $|c|$ rules out the exceptional cells $0$ and $1$. If $c$ is positive, the tape uses a right-side slot with index $(c-2)/2$; the bound implies this slot index is at least $b_\ell$. If $c$ is negative, it uses a left-side slot with index $(-c-1)/2$, likewise at least $b_\ell$. Any slot at or beyond $b_\ell$ is empty: if its zone index were less than $\ell$, the zone-index characterization (`zoneIndex_eq_iff`) would put the slot below the base of zone $\ell$, a contradiction. Thus the selected slot is empty on either side, and the tape value is blank.

**Key facts.** `Turing.zoneIndex_eq_iff`.
