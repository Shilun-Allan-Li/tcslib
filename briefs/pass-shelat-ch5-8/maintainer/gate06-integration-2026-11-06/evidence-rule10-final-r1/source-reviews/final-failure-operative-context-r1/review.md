# Gate 06 final failures: operative-context review

Source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; actual checked base `eee107e92a7db11f1f8c98a5c2867304f57ddc54`.
**No new home-induced foreign read identified in these 110 candidates.** No additional
migration fix is proposed. All **138 diagnostics in 110 blocks across 17 modules remain
failed evidence**; nothing is waived or relabelled as a seal pass.

Independently rechecked all raw header/body certificates, stable namespace/binder/attribute
contexts and complete error chunks. Rebuilt base/head import closures: their changed-import
union is exactly 15 paths. Read all 20 relevant complete diffs (the 15 imported sources plus
five other consumer homes). Ordinary definition changes are the probability/coin home moves
and ten exactly uniform `coinSlice` → `coinBlock` data substitutions; other changes are
public readers, proof repairs or documentation. This review uses those operative facts,
not consumer byte identity alone.

- **`FinDist.probTrue`:** moved Extractors → FinDist with its exact body and both exact public
  readers. The unchanged first two Extractors proofs explicitly use `probTrue_sub_probTrue`
  and fail at `statDist ... := rfl`; the third fails converting `hashPair` to map/prod.
  StatisticalDistance/LeftoverHash and those contracts are unchanged. Opaque probability calls
  in `EpsClose` do not unfold the moved definition. No new-home violation is identified.
- **Coin segments:** `coinBlock` and its equation move BlockEncryptor → Adversary unchanged;
  both local GI `coinSlice` copies have the same drop/take formula up to binder names. Ten
  strategy/simulator/helper bodies change by the uniform symbol substitution alone. Updated
  coin-slicing lemmas use public `coinBlock_eq`; unchanged wrappers can compare the shared
  function opaquely on both sides. The three failing BlockEncryptor blocks precede the old
  coin definition. Neither coin name occurs in any of the 110 unchanged blocks, and no coin
  or `probTrue` name occurs in any of the 138 complete diagnostic chunks. No new coin-body
  read is identified, including implicit wrapper comparisons.
- **Added import:** four GI module closures gain only Adversary. It introduces no new
  instance/simp-attribute/notation command, and its owned bare declaration names do not occur
  in any failing block in those four groups. Other failing modules keep their import sets.
- **Other contexts:** Classes/DAGCircuit/Encoding/Defs additions publish readers without
  changing existing ordinary bodies. Remaining GI changes use uniform tape contracts;
  existing graph/count/sampler, Efficient/Uniform, StatClose/Negligible, pairing/transducer and
  computability failures retain their owners. Per-module and per-block reasons, exact source
  and diagnostic hashes are in the JSON.

The **61 exact historical-key candidates and 49 no-exact-link observations remain separate**.
The initial 764 inventory is unchanged. Newly observed failure keys are not thereby new
Gate06 reads; equally, source equivalence is not a debt waiver or a base-native pass.

No helper/Lean/native/cache/build was run, and no source, main record, evidence or Git state
was changed. This source review does not enumerate every implicit kernel reduction and does
not freshly resolve parser names as Lean Names. It supplies bounded operative-context reasons
for root disposition, while retaining every original failure and provenance limit.

Input witness SHA256: `aaf398354d99b8565066bd58098d0bf15f92a62c8a0982397ae29ec320de6941`.
Review JSON SHA256: `085ca22eb3dfb6d6516bf6a8b3dc690ec63ae8ad1eea0bbcfda15fc63a1842c1`.

**Not yet clear to merge — failure disposition and external gates remain root/user decisions; no acceptance or waiver is issued here.**
