# EF-R1 base (EF1)

**Status: PENDING.** The base does not exist yet. A worker reading this at the records pin stops with **E-BASE**.

**What fills it** (ruling Q-6BF-4 A, the maintainer):
1. EF-R2-R3 (`ef-r23-regev`, wave 1, dispatched 2026-11-18 on `iO/phase-a-base`
   `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`) delivers a head whose series 1
   (`TCSlib/Cryptography/Encoding/ModularArithmetic.lean`) the maintainer accepts: its checkpoint 1 (series 1 and 2)
   or its final, whichever is accepted first with series 1 frozen.
2. Optionally, `gsw-6b-u18-u19`'s accepted final (so EF-R1 uses `Parameters.ofFamily_columns_le`).
3. In a scratch clone with those heads: `bash tools/mkbase-ef-r1.sh <ef-r23 head> [<u18-u19 head>]`, which prints
   `BASE <commit> tree <tree>`. Record here: the inputs (full hashes, the review that accepted each), the output,
   the toolkit's public names EF-R1 must reuse (from the accepted `ModularArithmetic.lean`), and the admissions of the
   base's order (`tools/graph.py`); then set the status to **READY** and commit before filling the records pin.

**Fixed now.** `git merge-tree --write-tree 5ed465f62e4ae0f93ded1a1ba49e807591b589eb
bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` is clean (tree `1a55e8aac645cab79de85749a17299e077c8cd62`): the iO base and
the #377 merge share no conflicting path (#376/#377 change `GSW/*`, `GSW.lean`, `LWE.lean`, `LWE/{BitEncoding,Ratio}`;
the iO base changes `Asymptotic/Realization`, `CoinSampling/*`, `Foundations/Subexponential`, `Games/Closeness`,
the facades `Asymptotic`, `CoinSampling`, `Foundations`, `Games` and `TCSlib.lean`: 15 Lean paths). EF-R2-R3's six files
(`Encoding/ModularArithmetic.lean`, `Encoding.lean`, the two Regev `Asymptotic.lean` files and their facades) are
disjoint from both.

**Landing (not the worker's concern).** EF1 is stacked on unmerged PRs: #374, #378, #380, the contract PR #384, and
EF-R2-R3's own PR. EF-R1 lands after them, or as a PR stacked on EF-R2-R3's.
