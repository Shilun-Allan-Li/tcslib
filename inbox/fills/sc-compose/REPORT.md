# Fill `sc-compose` · checkpoint 1 · `composeP_efficient`, `composeV_efficient`

**Worker** Claude. **Unit** `sc-compose` ([Gol04, §7.3.1, Theorem 7.3.3], the semi-honest composition
theorem). **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` (`cryptography/pass-shelat-ch2-4`), read from the
exchange at `2b9270ad095e993b020cb5e447d5a0043496802a` (`outbox/fills/sc-compose/`; pack 7/7 and SOURCE 152/152 verified:
`evidence/logs/inputs-check.log`). **Proof branch** `fill/sc-compose` (local), four commits over the base at this
checkpoint:

| commit | content |
|---|---|
| `a3cb219da2a068f36661608e5019086c313bc021` | the two helper modules and the two proofs |
| `2809a11828ec6eba37f8827c479231974a838676` | proof-sketch paragraphs for three polynomial-time lemmas (docstrings only) |
| `ed810c8415aba34e7dbb996be0da1e6786adfddf` | replace my duplicates of the layout helpers by the published `GI.ilayout`, `GI.efficient_of_polyTime`, `GI.argX/argZ/argM` (found by the overlap search), wrap lines |
| `32f837d9edcd5ae1991f6bef39a5ad69e1af77f5` | `padTo_poly` through the published `GI.zeros_poly` (drop my duplicate) |

## Status of the targets

| target | status |
|---|---|
| `composeP_efficient` | **proved** (axioms `propext`, `Classical.choice`, `Quot.sound`) |
| `composeV_efficient` | **proved** (same axioms) |
| `hbcSecure_compose` | open at this checkpoint (`sorry`, statement unchanged); checkpoint 2 and final |

`polyTime_compose` (proved at the base from the three) now depends only on the standard axioms. No statement
was changed; no ℓ-output PRF is built or needed.

## Changed files

| file | base | now | change |
|---|---|---|---|
| `SecureComputation/ComposeSecurity.lean` (owned) | 382 | 410 | imports the two helpers; proofs of the two targets; their `**Proof sketch.**` paragraphs rewritten to describe the delivered proofs (statement prose unchanged); module docstring: polynomial-time paragraph, new `## Contents`, `## Main results` status |
| `SecureComputation/ComposeSecurity/Machines.lean` (new) | — | 257 | polynomial-time machines on encoded histories |
| `SecureComputation/ComposeSecurity/Efficiency.lean` (new) | — | 575 | the composed parties as polynomial-time functions of the machine layout |

The module title keeps "(statement phase)" until `hbcSecure_compose` is proved (final). The docstring of
`polyTime_compose` still says "`sorry`s under their sketches" about the two efficiency theorems; it is another
declaration's statement prose, which the brief freezes, so I left it and flag it for the landing edit.

## The proof

`Strategy.Efficient S` asks for a uniform machine with `S`'s coins computing `S.next x z r hist` from the layout
`GI.ilayout x z hist r = ⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, encodeMsgs hist⟩⟩, []⟩, r⟩`. So it suffices to exhibit
`(H.composeP ρ).next` as a polynomial-time function `composePW` of that layout (`GI.efficient_of_polyTime`).

1. **Extraction** (`ComposeMachines.Efficient.exists_polyTime`, new): an efficient strategy's next-message function
   is a polynomial-time function of the layout (the output function of its uniform machine). Applied to `ρ.P`,
   `main.P` (from `G.PolyTime ρ`, `H.PolyTime F`); Alice's call-input function is the `callA` clause of
   `H.PolyTime F`.
2. **The shared pieces** (`Efficiency.lean`, generic in the strategies, used by both parties):
   - `runW`: one activation of `ρ`'s party machine in run `j` after `p` pairs, on the call input recomputed from
     the `main`-tape, the run tape `r[c₀ + j·c, c₀ + (j+1)·c)` and the run's messages read at the interleaved
     pairs `R·j + q`;
   - `ansW`: the `L(n)` run outputs, each padded to the answer length, concatenated;
   - `mainW`: one activation of the `main`-party machine on `⟨z, answers⟩`, the `main`-tape and the messages after
     the first `d` (`L·R` for Alice, `L·R + lead` for Bob);
   - `runW_ilayout`, `ansW_ilayout`, `mainW_ilayout`: on a layout they are the strategy activations; and each is
     polynomial-time (`polyTimeComputable_runW`, `_ansW`, `_mainW`).
3. **The parties** `composePW`, `composeVW`: the case distinctions of `composeP`/`composeV` on unary tests of the
   message count (`GI.msgCount`), `L·R`, `k / R`, `k % R` and the mover parity; `composeP_next_eq_composePW`,
   `composeV_next_eq_composeVW` identify them with the strategies (through `composeP_next`, `runNextA_eq`,
   `runInputA_of_lt`, `answersFromA_eq`, …), and `polyTimeComputable_composePW`/`VW` give polynomial time.
4. **The machine toolkit** (`Machines.lean`): concatenation over a data-dependent range
   (`polyTimeComputable_flatMap_range`), the iterated second projection (`iterSnd_poly`, an instance of the published
   `GI.iterUnary_poly`), the `i`-th message of an encoded history (`msgAt_encodeMsgs`), the history encoding as a
   concatenation (`encodeMsgs_append`, `encodeMsgs_eq_flatMap`), and **the interleaved-slot map**
   `polyTimeComputable_slots` with its equation `encodeMsgs_slotMsgs` (the expected new API of the brief: the
   encoded `Compose.slotMsgs sel off p hist` is polynomial-time in the encoded history for a polynomial-time
   selector and unary offset and count), zero padding `padTo` with `ofFn_padFin`.

Edge cases: `L(n) = 0` and `ρ.rounds(n) = 0` (the run branch needs `k < L·R`, so `R > 0` there and `k / R < L`),
the leading filler (Alice's `main.vF ∧ k = L·R` branch), Bob's `k − 1` at `k = 0` (then `0 − 1 = 0` as in
`composeV`), and `padFin` readback (`ofFn_padFin`) are all covered by the case analysis of the equation lemmas,
which hold for every `x, z, r, hist`.

## New declarations (checkpoint 1)

`Machines.lean` (namespace `TCSlib.Cryptography.SecureComputation.ComposeMachines`): `flatMap_range_ite`,
`polyTimeComputable_flatMap_range`, `iterSnd_poly`, `msgAt_encodeMsgs`, `encodeMsgs_append`, `encodeMsgs_eq_flatMap`,
`encodeMsgs_slotMsgs`, `polyTimeComputable_slots`, `Efficient.exists_polyTime`, `padTo` (+`padTo_eq`), `padTo_poly`,
`length_padTo`, `ofFn_padFin`.

`Efficiency.lean`: `ComposeMachines.moverW` (+`moverW_eq`), `polyTimeComputable_moverW`, `runW` (+`runW_eq`),
`runW_ilayout`, `polyTimeComputable_runW`, `ansW` (+`ansW_eq`), `ansW_ilayout`, `polyTimeComputable_ansW`, `mainW`
(+`mainW_eq`), `mainW_ilayout`, `polyTimeComputable_mainW`, `flatten_ofFn_eq_flatMap_range`;
`HybridProtocol.composePW` (+`composePW_eq`), `composeVW` (+`composeVW_eq`), `composeP_next_eq_composePW`,
`composeV_next_eq_composeVW`, `polyTimeComputable_composePW`, `polyTimeComputable_composeVW`.

Every new public `def` has its `_eq` reader beside it; every new declaration has a docstring with its formula;
no `@[simp]`.

## Overlap and reuse

Searches: `evidence/overlap/dupsearch-base.log` (tool `evidence/tools/dupsearch.sh`, run on a checkout of the
issue base). Reused rather than restated: `GI.ilayout`/`ilayout_def`, `GI.efficient_of_polyTime`,
`GI.argX/argZ/argM` with `GI.argX_ilayout`, …, `GI.inCoins_ilayout` (`GraphIsomorphism/Proofs.lean:579,594`,
`GraphIsomorphism/Efficiency.lean:290–340`), `GI.msgCount`/`msgCount_poly`/`msgCount_encodeMsgs`,
`GI.iterUnary_poly`, `GI.iterate_pairSndD_encodeMsgs`, `GI.zeros_poly`, `EncodingMachines` unary toolkit
(`unaryAdd/Mul/Sub_poly`, `divNum_poly`, `modNum_poly`, `ltTest/eqTest_poly`, `truncate_poly`), `Words.pairEncode_nil_append`.

| new declaration | nearest relative | relation, and why not reused |
|---|---|---|
| `polyTimeComputable_flatMap_range`, `flatMap_range_ite` | `ZeroKnowledge/ThreeColoring/Machines.lean:142,159` (same statements); `Complexity/FormulaKit/Emit.lean:127` (`sorry`); `EncodingMachines.flatMap_range_ite_eq:368` (Bool chunks) | **restated** (same proof). `ThreeColoring/Machines` is outside the imports the brief permits (it brings six modules and the Mathlib root `SimpleGraph.Coloring` outside the issued `order.txt`/`roots.txt`); the FormulaKit one is admitted. Promotion request below. |
| `iterSnd_poly` | `ThreeColoring/Machines.lean:190` (same statement) | restated, but proved as an instance of the published `GI.iterUnary_poly` (not a copy). |
| `msgAt_encodeMsgs` | `ThreeColoring/Machines.lean:951` `getD_eq_pairFstD_iterate` | restated (not importable, as above); two-line proof from `GI.iterate_pairSndD_encodeMsgs`. |
| `encodeMsgs_eq_flatMap`, `encodeMsgs_append` | `ThreeColoring/Machines.lean:912` `encodeMsgs_eq_flatMap` | restated / new (append form); not importable. |
| `encodeMsgs_slotMsgs`, `polyTimeComputable_slots` | none found (`slotMsgs` is only read by `Compose`/`ComposePhases`, `slotMsgs_runFst/Snd`) | **new API** asked for by the brief. |
| `Efficient.exists_polyTime` | `Interaction.lean:192` `Efficient.exists_uniform` (coins only); `GI.efficient_of_polyTime` (the converse) | new: the extraction direction (plan §2.11 "missing"). |
| `padTo`, `padTo_poly`, `length_padTo`, `ofFn_padFin` | `ThreeColoring/Machines.lean:303–327` (same); `Asymptotic/EnsemblesLemmas.lean:192–223` `padL`, `polyTimeComputable_padL`; `GI.padSq` (`n²`) | restated; neither import is permitted by the brief (EnsemblesLemmas is built in `order.txt` but is in the closure of neither the owned file nor the two permitted helper imports). |
| `moverW`, `polyTimeComputable_moverW` | `moverIsV_def` | new (the parity test as a machine). |
| `runW`, `ansW`, `mainW`, `composePW`, `composeVW` and their lemmas | `Compose.runNextA/B`, `answersFromA/B`, `composeP/V` (the strategies) | new: their machine forms on the layout. |
| `flatten_ofFn_eq_flatMap_range` | `Asymptotic/OneWayLemmas.lean:245` `flatMap_range_ite_eq_flatten_ofFn` (with an `if`) | specialization without the `if`; OneWayLemmas is not importable (as EnsemblesLemmas). |

## Scope requests

None.

## Promotion requests

- `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `msgAt_encodeMsgs`,
  `encodeMsgs_eq_flatMap`, `encodeMsgs_append`, `padTo`/`padTo_poly`/`ofFn_padFin`: generic FP and history-encoding
  facts that now exist in two places (`ThreeColoring/Machines.lean` and here); promote one copy to
  `ZeroKnowledge/EncodingMachines.lean` (the FP toolkit) and the `encodeMsgs` facts to `ZeroKnowledge/Interaction.lean`
  beside `encodeMsgs_cons`, then let both consumers import them.
- `Efficient.exists_polyTime`: to `Interaction.lean` beside `Strategy.efficient_iff`.
- `polyTimeComputable_slots`, `encodeMsgs_slotMsgs`: to `SecureComputation/Compose.lean` beside `slotMsgs_eq`, or
  to the history toolkit above.

## Checks

- **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; no cgroup memory limit, headroom = MemAvailable
  15.30 GiB; disk 14.20 GiB free on the clone's filesystem (ext4; scratch on the same filesystem). Before it I
  removed only my own finished, delivered worktrees (`/workspace/prfmac`, `/workspace/plong`; their branches keep
  their commits).
- **Packages and cache.** `.lake/packages` is a symlink to this host's populated tree at exactly the manifest's
  pins (the addendum's alternative; the manifest at `107f1e8c` is byte-identical to that tree's).
  `evidence/logs/packages-check.log`: "packages: 11 match, 0 mismatch, 4 absent". The 74 Mathlib roots computed
  from `order.txt` equal `roots.txt`; cache store before the fetch: 2,402 archives (`cache-store.log`, left by my
  earlier jobs on this host); the narrowed `lake exe cache get` (74 roots) exited 0, "No files to download",
  2,082 decompressed (`cache-get.log`; disclosed: I ran it under a `timeout 280` wrapper, which did not fire); no
  zero-size olean (`zero-oleans.log`); probe `import Mathlib.Algebra.BigOperators.Field` passed (`cache-probe.log`).
- **Bootstrap** (`evidence/logs/bootstrap.tsv`, logs `evidence/logs/bootstrap/`): 152/152 exit 0, 0 error
  diagnostics (`^\S+\.lean:\d+:\d+: error[:(]`; `evidence/base/bootstrap-errors.txt`); base sorry census 31 in 14
  modules (`evidence/base/sorry-census-base.txt`, the census of `base-sorries.txt`).
- **Order.** `evidence/cp1/order-cp1.txt` = `order.txt` with the two helpers inserted before `ComposeSecurity`
  (`reorder.log`: the helpers' imports `EncodingMachines`, `EfficiencyRep` and their closure move before them).
- **Sweep** (`evidence/cp1/`): all 154 modules, **154/154 exit 0, 0 error diagnostics** (`sweep-errors.txt`,
  `sweep.tsv`, logs `sweep/`). History, disclosed in `sweep-run.log`: the host restarted twice during the sweep
  (uptime reset; the module in progress has `START` without `END` in its first log, and was re-checked on
  resumption); I stopped it twice myself, at rows 136 and 148 (all before the helpers), to commit the two
  de-duplication commits; every module after row 148 (the helpers, `ComposeSecurity`, `YaoReal`, the facade) is
  checked at `32f837d9e`, the others are untouched by every commit.
- **Sorry census** (`evidence/cp1/sorry-census-cp1.txt`): 29 declarations in 14 modules; the only change from the
  base census is the removal of `composeP_efficient` and `composeV_efficient`.
- **Axioms** (`evidence/axioms/axioms-cp1.log`): all 66 stored constants of the owned file and the two helpers use
  only `propext`, `Classical.choice`, `Quot.sound`, except `hbcSecure_compose` (`sorryAx`, still open).
  `composeP_efficient`, `composeV_efficient`, `polyTime_compose`: `[Classical.choice, Quot.sound, propext]`.
- **Statement check** (`evidence/headers/headers-cp1.txt`, tool `headers.py`): every base declaration of the owned
  file is present in order with its header, `omit … in` lines and statement prose byte-identical (11 → 11):
  **0 differences**; control (`control-cp1.txt`): one character changed in the header of `composeP_efficient` is
  reported as exactly one difference.
- **Width and size** (`evidence/checks/widths-cp1.txt`): no line over 100 characters; files ≤ 1000 lines.
- **Sketches** (`evidence/checks/sketches-cp1.txt`): every proof of 15 lines or more has a `**Proof sketch.**`
  paragraph; the one flag is the definition `runW` (a 17-line body, not a proof).
- **Lint** (`evidence/lint/`): base 92 FAIL / 101 WARN (`lint-base.txt`, run on a checkout of the base), checkpoint
  92 / 101; line-set diff (`lintdiff-cp1.txt`): **no new FAIL, no new WARN, none gone**.
- Seals, controls and the unfold scan come with the final delivery (base and final).

## Next

Checkpoint 2: the simulators `S_A`, `S_B` (`S^H` followed by `L(n)` runs of `S^ρ` on coin blocks, assembled into a
view of `H.compose ρ`), the output clause with worst-case inputs as advice, and the statistical switch
(`2L(n)ε₁(n)`). Already written and compiling locally as working material: the probability tools, the view
assembly (`asmView` and its polynomial-time word form) and the advice-and-coins closure lemmas.

## Patches and reproduction

`patches/0001…0004-*.patch` and `patches/COMMITS.tsv`; a scratch clone at the issue base applies the series with
`git am`, the committer set from `COMMITS.tsv`, and reproduces every hash and the tree
(`evidence/amcheck/amcheck-cp1.log`).

## Evidence

`evidence/SHA256SUMS` covers every evidence file (inputs, raw logs, tools, probe sources); the top-level
`SHA256SUMS` covers every delivered file except itself; both checked against the delivered paths.
