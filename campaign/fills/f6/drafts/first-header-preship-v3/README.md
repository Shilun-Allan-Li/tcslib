# First physical header and rewind: bounded pre-ship PASS

**DRAFT — not ready to dispatch.** This is an inert check of the first physical header component,
not an F6 fill, complete prefix, universal-machine construction or target proof. No source,
admission, API, import, Git state, shared snapshot or cache was changed. `space_universal` remains
untouched. No hypothesis about an unfinished prefix or an assumed ruler presentation is used.

The authoritative inputs are **`First-header-native-v3.lean.txt`** and
**`First-header-sealed-v3.lean.txt`**. Both exit **0**, with **0 errors and 0 warnings**.

| Final input | SHA-256 | Time |
|---|---|---|
| Native v3 | `78600a2e3f646d2ddc65b93b91477703ace826c6ddae1b887c1667ff6aed613f` | 2.19 s |
| Sealed v3 | `dfd79643d87841ddeb7bba45a9f996dbff99788a0097afe31696973605ca45ea` | 2.21 s |

## Actual fixed component and result

For each **fixed** `K`, before either input word is quantified, the probe chooses

```lean
let i : Fin (K + 4) := Fin.last (K + 3)
let H := { headerRulerTM i with q₀ := Sum.inl 0 }
```

Thus the physical bank has **K+4 tapes**, with the ruler at physical index **K+3**. The row's
transition table is retained; its explicit local initial-state override avoids reading the
opaque row's initial control. A local overridden `headerScanTM` supplies the real scan initial
configuration used by the public restart identity, not a second controller or host.

For **every** `u,v : List Bool`, set `z = pairEncode u v` and `ℓ = 2*|u|+2`. The published
`pairEncode_eq` identifies this input as
`(u.flatMap fun b => [b,b]) ++ [false,true] ++ v`: doubled header, delimiter, untouched suffix.
Starting from the actual **`H.initCfg z`**, the theorem proves:

- At exactly **`2*ℓ+3 = 4*|u|+7`** steps, the full configuration is the explicit endpoint at
  live state `Sum.inr RewindPhase.done`, input position **`ℓ+1`**, ruler contents
  `bufferTape (List.replicate ℓ true)` from origin zero, every head zero, every other tape blank,
  and output `[]`.
- It separately reads the input position, every ruler cell and the ruler head, and proves
  equality of each other tape and head with **the actual initial configuration's** corresponding
  field. Blank ruler initialization is derived from `Cfg.init_workTapes`, not assumed.
- The endpoint label is **never reached earlier**, at every `t < 2*ℓ+3`.
- Output is `[]` for **all** `t ≤ 2*ℓ+3`.
- Actual accumulated space satisfies
  `H.spaceUsed (H.initCfg z) t ≤ (K+4)*(2*ℓ+4)` for every `t ≤ 2*ℓ+3`.

The time is taken directly from **`headerRulerTM_run`**, not from an estimated route polynomial.
The final space envelope is the public generic `spaceUsed_le_mul_succ` at that actual time.
It is a bound for this row only, not a bound for the whole F6 prefix.

## Published API chain

`UniversalParts.lean:795` supplies `headerRulerTM_run`, including the exact endpoint and strict
first-return cut. Its offset is instantiated at **p=0**. The inputs to that contract are discharged
from the real initialization using `MultiTapeTM.initCfg_with_q₀` and the five `Cfg.init_*`
readers. `MultiTapeTM.initCfg_eq_mapState` matches `H.initCfg z` with the scan initialization's
state relabelling; `runFrom_with_q₀` transports the actual row run. No body of either row,
`Cfg.init`, `initCfg`, `mapState` or `runFrom` is unfolded by the component proof.

The pointwise tape/head initialization equations are lifted by function extensionality to the
concrete initial field vectors before normalizing the published endpoint. `output_prefix` and
the empty final output establish silence; `spaceUsed_le_mul_succ` establishes the envelope.
The probe has no external run, input-position, blank-tape, presentation, endpoint or cut premise.
Its universal `u,v` quantifiers include empty headers and suffixes; `ℓ≥2` follows from its actual
definition. No malformed-code restriction or payload copy is introduced.

## Rule 10 and controls

The guard precedes the theorem's **docstring and complete header**. It seals **34 ordinary
definitions**, including model14/Simulation5, state maps, both header rows, the pairing, and the
previous bounded layout component's conservative operational superset. The default simp
definitions `Action.apply`, `Cfg.init` and `MultiTapeTM.initCfg` are disabled. Removing exactly
the recorded guard recovers the native v3 bytes.

The fresh compiled inventory examines the theorem's type/value and its **two compiled
descendants**. All three have only subsets of `{propext, Classical.choice, Quot.sound}`. Their
nine direct foreign ordinary definitions are all guarded; seven direct field projections are
classified as reducible abbreviations. The conservative 34 guards are not claimed to be 34
direct dependencies. Imported theorem proofs are consumed opaquely rather than re-audited.

Fresh controls cover **all 34 definitions**, independently in pointwise and abstract-function
modes. All **68** unsealed controls pass and create kernel-checked theorem constants. The sealed
counterparts exit1 with **exactly 68** expected, individually identified `rfl` failures. The checker
verifies identities/multiplicities and rejects synthetic missing, duplicate-replacing-missing,
unexpected-outcome and exit0 evidence. No unsafe reducibility or admitted failed control is used.

Manual inspection of all explicit `rw`/`simp`/`simpa`/`dsimp` arguments in v3 found only local
definitions/hypotheses or published equations and theorems. In particular local `e,ℓ` are
expanded; none of the nine foreign ordinary definitions is named as an unfolding argument.
`rfl` for the chosen initial control reads only the locally overridden record, while the foreign
header rows stay opaque. See `compiled-inventory.json`, `control-check.json`, and `verification.json`.

## Context, attempts and limits

The supplied API worktree head is `1160c18f03fd318f0dec25738790935fa61379d4`; no Git command was
run to attest that supplied identifier or current merge status. All runs used only the managed
plain wrapper against **wt-natbits / read-only complete oleans-mra2**, sequentially at local
budget three under machine budget five. `context.json` captures eleven source/compiled pins;
they remain unchanged. Only Hierarchy is imported. All inputs are `.lean.txt` here and were copied
to unique `/private/tmp` paths for elaboration; no compiled output was requested.

All **seven** attempts and raw receipts/logs are retained. Sealed v1 had two local proof-script
errors (`drop_zero`'s implicit argument and a pointwise initialization field used as a function
equality). Native v2 had two errors and sealed v2 one: the endpoint needed explicit whole-function
initial field equalities, while native reduction made a transport `rw` close before its next
tactic. V3 supplies those concrete field equalities and uses the public transport as an explicit
calculation. Failed-run `sorryAx` diagnostics are not evidence about v3; neither final output
contains `sorryAx`. The sealed-control failure is intentional and exact-checked.

**No concrete reader/type gap was found for this bounded component.** This does not establish
API sufficiency for the remaining route. The actual outer seam, hosted startup and return,
second scan/correction/rewind, full-bank final loop and complete prefix ledger remain outside
this task; see `REMAINING.md`. No screen, replay, source edit, new host/API, debt acknowledgment,
dispatch readiness or gate clearance is claimed.
