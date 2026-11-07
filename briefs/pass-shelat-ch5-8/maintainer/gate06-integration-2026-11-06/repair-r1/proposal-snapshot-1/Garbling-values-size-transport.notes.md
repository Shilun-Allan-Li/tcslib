# Garbling: one simulation-bound transport and its missing owner reader

**UNAPPLIED; native elaboration and sealing pending.** Frozen Gate06 head:
`e9d64158461bfe24ddc88ab885bc4017899b4c16`. No library edit, Lean/cache, Git command,
or app was used. Both original files match their completed seal-manifest fingerprints.

The valid V3 ordinal27 INSTALL and EOF markers verify all 40 requested names (40 active,
zero already irreducible). Probe416 maps to frozen source366 in `garbledValues_getD`:
`hv : v < Cc.size` is passed to indexed simulation, which needs
`v < n + Cc.gates.length` after `hlenA`. This conversion previously read the body of
foreign `DAGCircuit.size` implicitly.

The frozen owner has `def size` at `DAGCircuit.lean:489`, but no generic public `size_eq`.
The special `constCircuit_size` at line562 is insufficient for arbitrary `Cc`; no existing
length theorem relates arbitrary opaque `Cc.size` to its number of vertices. Root expressly
authorized the separate owner-reader proposal. `DAGCircuit-size-reader.patch` inserts only:

`theorem size_eq : C.size = n + C.gates.length := rfl`

beside `def size`, with its [AB09, Def 6.1] formula docstring and without `@[simp]`.
This is an owner-local term proof of the existing definition, with no algorithm change.
The owner is original audit ordinal1; it remains within the Gate06 touched scope.

`Garbling-values-size-transport.patch` changes only the existing bound proof at source366
inside `garbledValues_getD`, replacing `rw [hlenA]; exact hv` with
`simpa only [hlenA, DAGCircuit.size_eq] using hv`. The same `hv` assumption is transported
through the public size equation. No new nested `by` block is added. All public headers,
original definitions, algorithms, other proofs and admissions are unchanged. The owner patch
must accompany the consumer patch; applying the consumer alone would reference a missing reader.

The second independent diagnostic, probe443 -> source393 in `garbledOutput_eq`, remains
unpatched here. Its `Cc.output_lt : Cc.output < n + Cc.gates.length` must be transported
in the reverse direction to `Cc.output < Cc.size` using the same owner reader. It requires
no new premise or changed output semantics, but is reserved for the next invocation.
The pre-existing admitted probabilistic correctness result and its warning are preserved.

Static checks validated both one-hunk patch applications independently in memory, the
manifest line map and markers, source/header preservation, unchanged `by`/admission counts,
and unchanged on-disk library bytes. Root retains application and serial native checking;
no passing repaired seal is claimed.

| Artifact | SHA-256 |
|---|---|
| Frozen `Garbling.lean` | `2ecb46029b8a66f043f2b71c0c5d25ab5094bd36091ccc375c0aa06033d5c076` |
| Proposed `Garbling.lean` | `4622f999101d461a8eb09efd759f8c85fea2ead3c1dbae373f01504dc04d61db` |
| Frozen `DAGCircuit.lean` | `ce83c43824fc2d37dd753aa53cf62d52787227e7a63f51bc50c5f6d1db00aef8` |
| Proposed `DAGCircuit.lean` | `27ff028f07fa93ed0d9f151ffe0d3477f942b939621c5c5ba8a14a0b3f10d83e` |
| Owner-reader patch | `7dffc286e01fc08c85b1680f9223597c712d705a3d534dfb2aa030585dc95eae` |
| Consumer patch | `1bb941b1646f496f8c72499eb9d104675c3d86af63b25f0b3139d22172f722dc` |
| Completed V3 probe log | `4d0f98d9800652edcb41098df08ad960f10c0871193dc11d20659f17d2ace20b` |
| V3 seal manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |
| Original seal manifest | `75b11d1cf5324eea8066b898e5c37a677de266513cdde4be697ef8bf8149ba73` |

Log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_027_TCSlib_Cryptography_SecureComputation_Garbling_HarnessV3.log`.
