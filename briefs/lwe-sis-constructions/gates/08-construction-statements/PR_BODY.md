Add the next construction layer above the audited DLWE/SIS, representation and
dyadic arithmetic stack: exact bit sampling, encoded matrix operations, Regev PKE
algorithms and concrete bounds, direct DLWE generators, SIS raw-collision adapters,
and secret-matrix lossy/all-but-one trapdoor components for the later CCA2 PKE.

This is a **statement PR**: 19 mathematical modules, 220 source declarations and
101 explicit proof obligations. The 62 closed source proofs are complete `rfl`
readers; 40 additional non-simp projection readers and 13 compiler auxiliaries are
inventoried. It does not complete primitive-security endpoints or CCA2. SIS
hardness remains independent of LWE; no short lattice basis, Gaussian preimage
sampler or worst-case/search/decision reduction is introduced.

Target: `cryptography/lwe-sis-constructions`. This draft stacks the audited changes
from #236, #237, #238 and #239, whose integration remains user-controlled. Review the
new delta from `307cfdd1d6cadfda2ae9cca5367705ad770c5f42`; the complete PR comparison
also contains those unmerged dependencies. Mathematics is isolated in
`2bf9dd52882bcafbce9eab48a5bab796275f2094`; exports in
`17b2a282b545c6ebca3fccc88d518d18ae78f485`.

Shared-file overlap: the separate export commit changes only `TCSlib.lean` and the
Encoding, LWE, Encryption, SIS-hashing and Pseudorandom facades, plus six new
facades. Maintainers should reconcile these imports before landing. No existing
mathematical declaration, owner API, registry or toolchain/Mathlib pin changes.
The exact random-bit reader and existing-loop catalogue proposals are records
only; affected fill routes await their disposition.

Validation: fresh serial 144-module scoped sweep through
`scripts/lean_check_tree.sh`, zero errors, 101 new/17 inherited admission warnings;
575-constant axiom inventory, exactly the 101 intended admissions using `sorryAx`,
all 302 earlier constants preserved and all 48 backing contracts standard-axiom
only; style 0 FAIL/2 unchanged WARN over 41 files; independent finite models pass.
The whole library root is not elaborated. Execution/cache provenance remains
attested, and source validation/ingestion/matching and landing checks remain open.

See `briefs/lwe-sis-constructions/gates/08-construction-statements/REPORT.md` and
`audits/lwe-sis-constructions-statements-pack.md`. Codex is preselected for the
combined statement audit; the user dispatches it and approves all merges. This
draft is not clear to merge.
