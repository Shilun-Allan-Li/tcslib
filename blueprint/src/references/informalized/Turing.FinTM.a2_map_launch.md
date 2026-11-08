<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_launch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Launching after decoding a paired input

**Claim.** If $x$ decodes as $(a,b)$, the forward simulator reaches the virtual configuration for $M$ initialized on $b$, with tag true, input position $|x|+1$, first buffer $a$, and output encoding $(a,[])$, within the stated time bound. Up through that time, its configurations agree with those of the non-forward simulator.

**Proof.** The setup result (`a2_map_setup`) supplies a time $t\le 5(|x|+1)$ at which the non-forward simulator is in the specified virtual configuration; the decoding hypothesis selects its successful-decoding case. Let $E(v)$ mean that the non-forward run has entered a run state with some machine state and tag. The configuration at time $t$ satisfies $E$, so the set of such times is nonempty; choose its least element $u$. Then $u\le t$, and by minimality no time strictly before $u$ satisfies $E$. The simulators agree at every time $v\le u$ by the prefix-agreement result (`a2_mapSetup_run`), since every earlier time avoids entry. At time $u$, the non-forward run remains stationary: the entered run state is one for which the non-forward simulator's transition preserves the configuration (`a2_mapSetup_stationary`). Consequently its configuration at $u$ equals its configuration at $t$, which is the virtual initialization supplied by setup. Thus $u$ obeys the same bound and has the required endpoint and prefix agreement.

**Key facts.** `Turing.FinTM.a2_map_setup`, `Turing.FinTM.a2_mapSetup_run`, `Turing.FinTM.a2_mapSetup_stationary`, `Turing.MultiTapeTM.runFrom_add`.
