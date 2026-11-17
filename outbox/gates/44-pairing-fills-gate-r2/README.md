# Codex audit · Gate 44 round 2 · pairing fills T1 (#340) and T4 (#346)

Re-audit draft PR #340 at 916afc25c21f5e52b4b01958186ad55d2f615fd1 (unchanged since round 1) and draft PR #346 at
98cb0e521a94e94c304c78348fb5d3033435a3ed together, using pack-r2.md. #346's new head is round 1's head
89a18a8225be1b76166af12a15179da291747783 plus one commit, the docstring landing edit LE-g44. Campaign records are pinned
at 4f4a7592a54cf82fa04f96b83645d7936672614c, the records tip at staging, which holds ruling G44-01 and ledger rows DL-55
and DL-56.

Round 1 was HOLD (0 blockers, 1 major, 1 minor, 1 note) with no mathematical gap. Its findings are findings-r1.md, and
resolutions-r1.md answers them:
- G44-01, the major: accepted by Seyoon and ledgered as DL-55 and DL-56, repaid in cleanup Stage 2. Both reports'
  "nothing for the duplication ledger" lines carry dated corrections.
- G44-02, the minor: LE-g44 attributes the bounded sampler and its bound to Candidates.statClose_sampleBelowL and keeps
  PS10 Theorem 52.3 as context only. It changes docstrings only.
- G44-03, the note: the control figures are corrected in pack-r2.md.

The round-1 pack is outbox/gates/44-pairing-fills-gate/ at exchange 30ef1257a56873489b599007782046b7dedeb7fc; pack-r1.md
here is its pack. Round 1's passes are not re-audited.

The two PRs merge cleanly with the records tip in every order. The merged tree is
T44' = bee027f0903d531b3a43511cea16bfa123210291. Its code differs from round 1's T44
(33681cb8ed893a897ca2028d5ada70ca29237978) only in the three LE-g44 files, which are byte-identical to T44's after
comment stripping. The maintainer replayed T44' on a copy of round 1's output:
- 10/10 modules rc 0 with 0 errors, and the state check OK over 1427 modules;
- admissions 196, unchanged, and an identical axioms log;
- canonical coe-A seals on Draws, Words, Handler and BonehBoyenMachine, each with 0 errors and request sets row-identical
  to round 1's;
- lint unchanged.

- pack-r2.md: the round-2 scope, the three resolutions, LE-g44 verbatim, T44', the replay and seal evidence, the known
  slips and the findings format.
- resolutions-r1.md, findings-r1.md: the round-1 dispositions and findings.
- le-g44.diff.txt: git diff 89a18a82..98cb0e52 (3 files, +22/-7).
- pr346-r2.diff.txt, source-head-r2.json: #346's diff from its merge base 7291f6b2 (equal to GitHub's three-dot view;
  8 files, +2756/-17); the pins, and the hashes, line counts and widths of the 9 files at T44'.
- sources-r2.zip: the three LE-g44 files at both commits, Candidates/DiscreteLog.lean (the cited construction) and the
  PS10 section 2.8 lines. The source closure is round 1's sources-r1.zip.
- verification-r2.zip: the git-object checks with their scripts; the replay (build logs, state, link counts, olean
  comparison, snapshot rehashes, output map, admissions, axioms, lint); the collector and the four coe-A seals with
  their comparison to round 1; and the records extracts and the three corrections as filed. MANIFEST.md gives each
  entry's provenance, and its SHA256SUMS lists every other entry.
- bundle.md: the pack, the resolutions, the findings, the corrections diff, the records extracts, the checks, LE-g44's
  diff, the three Lean files at 98cb0e52, DiscreteLog.lean, policy.md and the round-1 pack. Each section header names
  its path and source; BUNDLE-FILES.txt lists them.

Check SHA256SUMS before using the pack. Return gate44-pairing-fills-r2-findings.md as Markdown in the chat. If you have
several evidence files, return a ZIP containing that Markdown and the evidence. The user dispatches and merges.
