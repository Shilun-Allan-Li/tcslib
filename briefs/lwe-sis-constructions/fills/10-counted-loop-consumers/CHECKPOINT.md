# Gate 15 relocation checkpoint

The proof source is pinned at `8b3187bdaf0c634c086313a727a7210dca14bfeb` on draft
[PR #250](https://github.com/Shilun-Allan-Li/tcslib/pull/250).
The Gate 14 PASS clears the registered counted loop for these consumers.
[Gate 14 disposition](../../../../audits/lwe-sis-counted-loop-registration-resolutions.md)

All five changed modules passed the serial development check with zero
errors or admissions. The nine new proof bodies depend only on the
standard Lean axioms. All 220 source declarations retain their audited
statements. The other 148 frozen files match the Gate 14 baseline.
[Checks and proof hashes](development/checks.json) · [Axiom prints](development/fill-axioms.log)

The fresh 144-module replay and its type and axiom inventory probes were
underway at checkpoint time. Gate 15 publication follows their
reconciliation. Scoped source matching and landing checks remain open.
