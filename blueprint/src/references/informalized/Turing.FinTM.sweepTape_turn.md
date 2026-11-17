<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.sweepTape_turn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflection of the Zipper Tape

**Claim.** The tape represented by frontier $z$ and stacks $l,r$ agrees at coordinate $w$ with the tape represented by frontier $-(z-1)$ and stacks $r,l$ at coordinate $-w$.

**Proof.** Fix $w$ and split according to whether $w<z$. If so, the original tape reads from $l$. The reflected coordinate lies on the right side of the reflected frontier, so the reflected tape reads from its right stack $l$; the two list indices agree because $-w+(z-1)=z-1-w$. If $w\not<z$, the original tape reads from $r$, while the reflected coordinate lies to the left of the reflected frontier and the reflected tape reads from its left stack $r$. Their indices agree by the corresponding integer identity. Thus the tape values coincide in either case.
