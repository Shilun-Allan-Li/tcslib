# Claude fill `seq-zk` (Theorem 175.1)

Claude is the worker (Seyoon's standing ruling, 2026-11-11). The job proves the admitted the five `seqRep` declarations in
`TCSlib/Cryptography/Composability/SequentialZK.lean` [PS10, §7.2.1, Theorem 175.1] and [Gol01, §4.3.4]. The base is `107f1e8c218733eac12d6b9bee6fece441271317` on
`cryptography/pass-shelat-ch2-4`, the records tip after #303, #305, #306, #308 and #309. #307 (dl-crh) is not merged,
and this unit touches none of its files.

**Size note.** This is the largest unit of the batch (5,000–10,000 lines are estimated). The checkpoints
deliver whole declarations, and a partial final is allowed.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 237 TCSlib modules. These are the upstream closure of the owned module, plus the owned module's downstream modules.
- [Mathlib roots](roots.txt): 76.
- [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 23 declarations in 9 modules. The only change must be the removal of
  `ZK.seqRep`, `StatZK.seqRep`, `InteractiveProof.seqRep`, `InteractiveProofErr.seqRep` and `EfficientProverProofErr.seqRep`.

Claude returns checkpoints and the final payload only at `inbox/fills/seq-zk/` on the exchange. Seyoon
dispatches.

**Ready to dispatch**
