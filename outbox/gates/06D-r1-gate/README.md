# Gate 06D: Codex statement audit, round 1

Ready for the user to dispatch. Codex returns `gate06D-findings.md` as a Markdown file in
the audit chat (or one ZIP containing findings and required evidence); do not push to GitHub.
No audit has been dispatched or closed by preparing this input pack.

- Frozen Lean source: `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; checked comparison ancestor: `eee107e92a7db11f1f8c98a5c2867304f57ddc54`.
- Records commit: `c81baa7712ab1b43357276ef5df138d02616c9d0`; exact exchange commit: supplied in the user's dispatch prompt.
  The target library/root-export bytes equal the checked ancestor at this records pin.
- Primary input: `gate06D-source-bundle.md`, 185 raw source sections,
  SHA256 `3a167712e1748f7a121aa01455e060977a225bb98f5ea144071c087c568a64cd`. `gate06D-source-manifest.json` records all raw paths/revisions/bytes/hashes and
  import edges, SHA256 `8947c1090298d80034c616b1492792707f91016528759d0b8047478a4ef97f90`. The root export is context, not an elaboration claim.
- Read `gate06D-records-bundle.md` for the issued `06D-pack.md`, current PLAN, policy/rulings,
  inventory, source-access disclosure and final evidence index. Records bundle SHA256 `291a1edc28fac3d1b32a29109c71e8316f122dbe16891ddb0d313771c2592f2a`.
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
