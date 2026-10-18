# External audit pack — Chapter 2, epoch-3/4 fill gate, round 3

Round-3 review of the single open major from round 2
(`audits/ch2-epoch34-r2-findings.md`, attached verbatim): the kernel
public-surface certification of the six owned modules. All other
round-1/2 items are closed or frozen. Record findings in
`audits/ch2-epoch34-r3-findings.md`; the gate closes on zero
blockers/majors across all rounds' open items.

The repair (detail in the attached resolutions, round-2→3 section):
`audits/programs/ch2-epoch34-R3Axioms.lean` replaces pass 3 with exact
two-directional set equality against an embedded, reviewed 87-name
inventory — no prefix inference, no `isInternal` exemption, no
exceptions array; absent expected names and unlisted actual names both
fail the run; source publics are existence- and ownership-checked. The
inventory review binds each of the 87 names to its class and generating
declaration, and corrects round 2's undercount of the private-structure
derived-instance family (7 members, not 3 — the rest had been masked by
the rejected `isInternal` exemption). Passes 1/2/4/5 are unchanged; the
run used the same pinned snapshot, sources hash-asserted against the
round-2 manifest, and passed.

Both round-2 probes are now answered mechanically: `SurfaceProbe.a.extra`
(an unlisted public under an allowed prefix) fails check (i);
`SurfaceProbe.b` (an expected name that does not exist) fails check (ii).

## Bundle manifest — 5 attachments after this pack

The resolutions (with the round-2→3 addendum); the round-2 findings
(verbatim); the R3 program; its run log; the reviewed kernel-surface
inventory.
