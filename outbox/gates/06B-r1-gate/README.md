# Gate 06B: Codex statement audit, round 1

Ready for the user to dispatch. Codex returns `gate06B-findings.md` as a Markdown file in
the audit chat (or one ZIP containing findings and required evidence); do not push to GitHub.
No audit has been dispatched or closed by preparing this input pack.

- Frozen Lean source: `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; checked comparison ancestor: `eee107e92a7db11f1f8c98a5c2867304f57ddc54`.
- Records commit: `c81baa7712ab1b43357276ef5df138d02616c9d0`; exact exchange commit: supplied in the user's dispatch prompt.
  The target library/root-export bytes equal the checked ancestor at this records pin.
- Primary input: `gate06B-source-bundle.md`, 129 raw source sections,
  SHA256 `66f3ac9e11a1100a276f3336f54ee4a6f5b3a109e5c647523575b95e828ef9ff`. `gate06B-source-manifest.json` records all raw paths/revisions/bytes/hashes and
  import edges, SHA256 `e33f8aa437668a506a31a5f7c1c2e3d2632ff999023be5d2847e324cbcd83990`. The root export is context, not an elaboration claim.
- Read `gate06B-records-bundle.md` for the issued `06B-pack.md`, current PLAN, policy/rulings,
  inventory, source-access disclosure and final evidence index. Records bundle SHA256 `1e5d62aebbb9d5197d438af67b8f4543dd264c7bc4218266782f66127beca01f`.
  `BUNDLE-FILES.txt` and the two component filelists revision-qualify every section.
- Common evidence and PS10 PDF: sibling `../06-common-r1-gate/README.md`. Its evidence ZIP
  SHA256 is `960ab0c708c9efdd9a5ef01175889afa0b97be0984e35ace25f4001265ee0749`; final evidence index SHA256 `0e011edc90d469d1b3dd1156a74f6f7856f756e15e085343486a232ea24aa73b`.
  Verify `SHA256SUMS` in both folders. Goldreich/PSV access is link-based with exact version
  limits; record the specific source comparisons you could or could not perform.

Audit the definitions/statements/docstrings/sketches against the sources using the issued
pack, including its short correctness proofs. Preserve its edge-case and adversarial-example
requirements; do not substitute historical source probes for the frozen Lean bundle. Gate
closure requires zero blockers and zero majors. The four packs may run in parallel; each
prong's substantive fills wait for its own gate closure. No campaign branch is changed.

**Not yet clear to merge — this external statement audit has not returned.**
