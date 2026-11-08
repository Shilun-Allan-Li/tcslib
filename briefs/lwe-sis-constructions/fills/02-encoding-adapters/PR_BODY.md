The fixed-width cryptographic encodings and existing little-endian arithmetic
machines now have proved total conversion adapters. All 14 audited obligations
are filled: numeric/endian equations, exact widths, normalization and round trips,
and the three polynomial-time implementations. Definitions and signatures stay
fixed to the passing statement gate at `6eec97be8f54d9990340900a5595dab32fb477f5`.

Validation: fresh serial 93-module sweep through `scripts/lean_check_tree.sh`,
complete axiom inventory, fourteen-body freeze comparison and scoped style checks.
There are zero owned admissions and 17 inherited warnings. All 284 owned constants
and nine backing machine contracts use only standard axioms. The only added
constant is a disclosed compiler arithmetic auxiliary. The statement audit passes
0/0/0/3; Codex is selected for the separate proof audit, with dispatch pending. Evidence and
execution limits are under `briefs/lwe-sis-constructions/fills/02-encoding-adapters/`.
No whole-root build or primitive-security completion is claimed.

Target: `cryptography/lwe-sis-constructions`; audited dependencies: #236/#237.
The user approves and merges. Source-policy completion and relevant landing checks
remain open. The only existing-file overlap in this PR is the earlier Encoding
facade import/contents addition, isolated in its own commit. This proof fill adds
no export, shared owner API, host, cache fetch or pin change.
