# Gate 10 verification

Source 747cc18ddb53979919d107fefed450191eb31743, base e226b470e25cb08a9fe8b10f9f5dd54fc55c1808. Seven Lean sources match the pinned Git blobs.

- Ten native source checks pass, covering the six helper modules,
  Games/Efficiency, Bridges, the library root and campaign Checks. The imported
  objects are from the verified #282 tree. The 1,146 retained source inputs
  match that tree.
- All 84 older stored declarations preserve their types and metadata.
  Exactly the four intended theorem bodies differ. The source-header
  comparison is empty. All 448 declarations stored in the seven owners,
  including generated declarations, use standard Lean axioms.
- Seven whole-file seals pass. The elaborated-term collector selected all
  stored declarations and generated auxiliaries and produced 159 sealable
  foreign-definition requests. Name, owner, reducibility and instance
  metadata are checked by the existing instrumenter. Reducible exclusions
  are abbreviations, and PolyExpr.eval has its existing notation ruling.
- All six controls pass before sealing and fail at the intended six
  body-reading statements after sealing.
- The refreshed explicit inventory covers 1,031 tactic-list items and all
  five final List.cons_ne_nil argument uses. The definition heads resolve
  to their own source files. The Games style lint has zero failures or
  warnings.
- Maintainer review added eleven reader lemmas covering raw projection
  inputs, an empty polynomial family, and out-of-range length selection.
  The two affected helper files and all their consumers were checked with
  these additions.
- Review identified applications of existing proofs and generic
  generalizations in the disclosed overlap. The shared-helper requests
  remain follow-up consolidation work under the issued design.

The original 60-file Claude delivery, its manifest and reported worker head
are preserved in the [intake](../../fills/efficiency/final-r1/intake.md).
The verification archive retains the corrected telemetry and metadata
attempts and states their disposition. Source-level scope remains the four
frozen targets and their helper modules.

[Native, seal, census and scan evidence](verification.zip)
[143-module source closure at the pinned head](sources.zip)

**Ready to dispatch**
