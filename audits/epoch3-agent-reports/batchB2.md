# Epoch 3, batch B2: completion report

## Result

The live-source obligation in `Turing.universal` is closed. The original four-tape interpreter, startup, checkpoint relation, and bound are retained. No private machine construction was revised or replaced.

- Branch: `fill/epoch3-B`.
- WIP base: `f191b918220f673ffd2830ee66e8fee86689e0cb`.
- Patch/bundle baseline: `71721842a2336d5562ef831a19b0e86e063dddaa`.
- Final source: `TCSlib/Complexity/TuringMachine/Universal.lean`, **2465 lines**.
- Only that tracked file differs from the WIP commit. The historical implementation notes and proof sketches remain, with flagged completion appendices.
- All three public theorem statements are byte-identical to the WIP. The complete declarations of `universal_quadratic` and `timed_universal`, including their existing proofs/sketches, are unchanged.
- `universal`, `universal_quadratic`, and `Complexity.UC_computable_of_HALT_computable` have axiom footprint `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

## Realized cost ledger

Write `M = c.decode α`, `L = M.serialize.length`, `N = M.numStates + 1`, `h` for the old table cursor, `q` for the current state index, `q₀` for the initial state index, and `q′` for a live successor index. Let `k = 2 * (Nat.bits M.numStates).length + 2`. Let `P_g` be the serialized length of the preceding whole state groups, `P_b` the serialized length of the selected state's preceding read-offset records, and `P = P_g + P_b`.

| Phase | Proved transitions | Proof |
|---|---:|---|
| Read symbols; begin table rewind | `1` | `universal_live_block.hmain` |
| Rewind table to its start | `h + 1` | `universal_table_rewind` |
| Skip the doubled count field | `k` | `universal_count_run` |
| Skip initial-state unary field | `q₀ + 1` | `universal_initial_skip` |
| Consume the old unary state and skip its preceding groups; detect its final blank | `q + P_g + 1` | `universal_skip_groups` |
| Rewind the erased state tape to position one | `q + 2` | `universal_state_rewind`, instantiated in `universal_select` |
| Skip the read-offset records | `P_b` | `universal_skip_records`, instantiated in `universal_select` |
| Read the fixed action fields | `8` | `universal_read_fixed` |
| Halting successor: detect flag, apply | `2` | `universal_prepare_next` and `universal_apply_record` |
| Live successor: detect flag, copy index, rewind, apply | `1 + (q′ + 1) + (q′ + 2) + 1 = 2q′ + 5` | Same lemmas, using `universal_unary_copy` and `universal_state_rewind` |

The two successor rows are alternatives. Thus the exact live-source block duration is:

- Halting successor: `h + k + q₀ + 2q + P + 16`.
- Live successor: `h + k + q₀ + 2q + P + 2q′ + 19`.

`universal_live_block` constructs the duration as the sum of these phase lengths and concatenates the runs using `universal_run_join` (`MultiTapeTM.runFrom_add`). The first phase makes the duration positive. The table decomposition proves `h, k, P ≤ L` and bounds the final table cursor, which is the selected record's false terminator. The state type gives `q₀, q, q′ < N`. The original private bound therefore survives unchanged:

```lean
private def universalBlockBound (c : EffectiveMachineCode) (α : List Bool) : ℕ :=
  3 * (c.decode α).serialize.length + 5 * ((c.decode α).numStates + 1) + 20
```

Already halted source configurations still take one absorbing target transition, as in the WIP.

## Declaration inventory and obligations

All 22 additions are `private`. The obligation numbers refer to the four numbered obligations in the brief.

| New declarations | Role / obligation |
|---|---|
| `universalActionBits`, `universalNextOnes`, `universal_record_shape` | Exact fixed-bit dictionary and unary-tail grammar; obligation 1. |
| `universal_skip_fixed`, `universalSkipDone`, `universal_skip_unary`, `universal_skip_record`, `universal_skip_records` | Exact-cost scanning of one or up to nine records; obligations 1–2. |
| `universal_skip_groups`, `universal_select` | Erase one state symbol per nine-record group, rewind the erased state, then skip the finite read offset; obligations 2 and 4. |
| `universal_read_fixed` | Eight-bit register agrees with every fixed field of the selected record; obligation 1. |
| `universalNextCost`, `universal_prepare_next` | Halting flag, live successor copying, marker-directed rewind, and exact costs; obligations 3–4. |
| `universalActions`, `universalActions_lookup`, `universalHeader`, `universal_serialization_actions`, `universal_lookup_parts` | Canonical state order and input-major/work-minor enumeration, with exact prefix decomposition; obligation 2. |
| `universalActionBits_decode`, `universal_apply_record` | Optional writes (including blank), work movement, output emissions, successor state, and clamped virtual input/marker movement preserve the checkpoint; obligation 3. |
| `universal_run_join`, `universal_live_block` | Complete positive-duration block, final cursor bound, and code-only runtime bound; obligation 4 and assembly of 1–3. |

Changed existing declaration: `Turing.universal` (proof body only), which lifts `universal_live_block` through `universalCapture_interpreter_run` and supplies the missing relation witness. `universalBlockBound` has only an appended completion note; its defining expression is unchanged. No existing private definition or lemma body was revised. No other admission was edited.

## Requested shared lemmas

`universal_run_join` is a candidate convenience lemma for the raw run-algebra API: two consecutive `runFrom` equalities compose by adding their durations. It remains private here. The remaining additions describe this interpreter or its serialization and should remain private.

## Escalations

None. The accepted file-growth allowance is used: the file grows from 1668 to 2465 lines. There is no obstruction to the public statement and no change to the controller or its cost bound.

## Verification

The prescribed full **25-module sweep exited 0**, with fresh `.olean` output for every module, **zero error diagnostics** (including both `error:` and `error(...)` formats), and exactly three admission warnings. The raw output is `final-sweep.log`. The sweep command was:

```bash
( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )
```

`axioms.log` records successful prints of:

```lean
#print axioms Turing.universal
#print axioms Turing.universal_quadratic
#print axioms Complexity.UC_computable_of_HALT_computable
```

Each print is exactly `[propext, Classical.choice, Quot.sound]`; none contains `sorryAx`. The printer exited 0.

Independent source checks confirm:

- Only `Universal.lean` is modified relative to `f191b918`.
- All three public theorem headers through `:= by` are byte-identical.
- After removing comments, the only existing declaration whose body changed is `universal`.
- The sole remaining actual `sorry` token in `Universal.lean` belongs to `timed_universal`.
- `git diff --check` passes.

Toolchain: pinned Lean 4.25.0, using an existing local toolchain and dependency checkout. `lake exe cache get` was invoked exactly once and completed successfully. No `lake build` was run. No archive-ownership recovery or `TAR_OPTIONS` workaround was needed. Early module checks that overlapped cache population exited with status 135; those results were discarded, and verification was rerun after cache completion. Whole-interpreter executable smoke tests were not run.

The remaining admissions are exactly:

1. `Turing.exists_effectiveMachineCode` in `Encoding.lean`.
2. `Complexity.oblivious_of_mem_DTIME` in `Robustness/Oblivious.lean`.
3. `Turing.timed_universal` in `Universal.lean`.

## Delivery

Final local commit: `3b5a9eb086f8ab8d052c1250d138a3c6121f52b9`. Its parent is the original WIP commit, unchanged. The working tree is clean. `git bundle verify` passes against the stated baseline.

The archive contains this report, the modified source at its repository path, the full two-commit format-patch series from `71721842` (the original WIP commit included unchanged), the required Git bundle, `final-sweep.log`, `axioms.log`, and `SHA256SUMS`. Nothing was pushed and no PR was opened.

## Cost notation glossary

`M`: decoded machine; `α`: its supplied representation; `c`: supplied effective coding scheme; `L`: serialized table length; `N`: number of source states; `h`: old table cursor; `q`: current state index; `q₀`: initial state index; `q′`: live successor index; `k`: doubled count-field length; `P_g`: serialized preceding state groups; `P_b`: serialized preceding records within the selected group; `P = P_g + P_b`: total skipped-record length.
