Cryptographic encodings use fixed-width MSB words, while the existing binary
machines use normalized little-endian words. This draft states total conversion,
numeric width-normalization, round-trip, length and polynomial-time contracts
that let later LWE/SIS implementations reuse those machines.

The new module has 20 declarations: 3 definitions, their 3 complete rfl readers,
and 14 admitted obligations with sketches. Its statement audit must pass before
proof fill. It adds no machine/host, shared-owner API or primitive-security claim.
The sole existing-file overlap is an Encoding facade import/contents entry in a
separate commit; root exports and pins are unchanged.

Validation: a fresh serial 93-module sweep, axiom/census/invariance checks, and
scoped style checks. The earlier 263 constants are unchanged; exactly 14 new
statements use sorryAx. Nine consumed machine contracts have only standard
axioms. There are 17 inherited admission warnings and no whole-root build claim.
One required pinned Mathlib cache archive was fetched; source/manifest pins stay
unchanged. Full evidence and limits are under
`briefs/lwe-sis-constructions/gates/04-encoding-adapters/`.

Target: `cryptography/lwe-sis-constructions`, with audited dependencies #236/#237.
The user approves and merges. Source-policy and relevant landing checks remain
open; no reviewer selection, dispatch or adapter gate verdict is claimed yet.
