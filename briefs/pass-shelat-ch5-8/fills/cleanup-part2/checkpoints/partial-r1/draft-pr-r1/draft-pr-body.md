Consolidates shared block/decoder, state-loop, averaging and strategy-transition contracts, replaces named duplicates, and migrates consumer proofs to owner lemmas. This contains Claude's **partial** cleanup delivery plus a maintainer commit that removes a new whole-machine equality, uses existing operational output contracts, and repairs four unary efficiency proofs through existing BinArith/length contracts.

The 13 worker commits retain attribution; the maintainer delta is separate. There are 122 changed Lean paths (96 consumers and 26 reader-only providers), based on issued source `1aa5506f58f77c215e56d24311ec33bd931cacf1`. Bounded source review verifies that original provider declarations and all 20 owned admitted blocks remain unchanged. Head: `32b827c017bc321ea40577bc8f27131df2c35e1a`.

Validation of the eight-file maintainer delta:

- Its complete 124-module local import closure passes, one module at a time with `scripts/lean_check_tree.sh`, using an initially empty TCSlib object tree and a narrowed 72-root Mathlib import probe.
- Ten selected actual axiom sets contain only `propext`, `Classical.choice` and `Quot.sound`; all four repaired unary efficiency lemmas are included.
- Independent bounded static review reports 0 blockers, 0 majors and 0 minors. Local style comparison adds no normalized findings.
- Verified same-phase resumes, both corrected failed attempts, unique raw logs, source/object/direct-local-prerequisite hashes and all configuration revisions are retained. These checks do not constitute a full affected/root/Checks replay or complete current-source axiom census.

**Keep this PR draft.** The received measured variant still had 173/509 open keys; no refreshed closure count is claimed after the maintainer repairs. Four workflow majors remain: extra eval-helper omissions, 25 omitted changed providers in seal coverage, incomplete maps and overwritten original attempt logs. Corrected 123-owner request plans are unrun data; instance/reducible coverage, full seals, controls/census/dispositions and complete current-source replay remain outstanding. A native probe refutes blanket instance-marking impossibility for one exact instance; it grants no coverage or scope waiver.

The three original-provider proof proposals are unapplied. Continuation worker choice and provider-proof scope are awaiting the user. Gate06C/#232 remains independent at its frozen head; the received-source merge preview found 13 textual conflict paths and excludes this later maintainer delta.

[Checked repairs and complete bounded evidence](https://github.com/Shilun-Allan-Li/tcslib/blob/302d9ed57828cf901d9be3dc26c8f0ec8f8a74ab/briefs/pass-shelat-ch5-8/fills/cleanup-part2/checkpoints/partial-r1/checked-repairs-r1/README.md) · [Immutable incoming reviews and resolutions](https://github.com/Shilun-Allan-Li/tcslib/blob/51e1cf76cc542d6d5fb4e9ea2ce99d2f26a44cc7/briefs/pass-shelat-ch5-8/fills/cleanup-part2/checkpoints/partial-r1/review-r1/resolutions.md)

**Not yet clear to merge — partial cleanup, complete seals and final evidence remain open.**
