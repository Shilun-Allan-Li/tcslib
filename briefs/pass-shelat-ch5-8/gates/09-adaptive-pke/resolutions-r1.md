# Gate 09 round 1 resolutions

**Closed on 2026-11-10 PST.** The auditor reports 0 blockers, 0 majors,
0 minors and 2 notes at `46e9b8b8773e5188c5b0f4732f3fff8d9092fa2d`
on [PR #284](https://github.com/Shilun-Allan-Li/tcslib/pull/284).
[Verbatim findings and checksum](findings/intake-r1.md)

| Finding | Disposition |
|---|---|
| N1 · public-key-dependent CPA choices | Carry into the CPA proof stage. Complete `SingleBitSecure.padded_cpa` through the checked handler, then use an adaptive bitwise simulation and a polynomial fresh-challenge lift for the n-bit witnesses. The current checked compositions end at `SingleBitSecure`. |
| N2 · CCA2 witness assumptions | Carry into the CCA2 construction ruling. The probe elaborates the desired witness proposition. The construction theorem will state its actual premises. The generic lift starts from the same scheme's single-challenge IND-CCA2 security. |

The source pins, all 150 replay source hashes and both native replay
result lists match the maintained evidence. The auditor independently
checked the proof text, committed bytes and evidence consistency.
The native replay and seals were run by the maintainer and are
bound to the audited head. Campaign changes after the review base
are records only. The close applies to the adaptive game and its
cap-one correspondence, the shift and probability transports, and
the RSA/Rabin width equations. [Verification evidence](verification.md)

Seyoon merges the PR.

**Clear to merge**
