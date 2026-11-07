# Last-ruler final seam: conditional pre-ship PASS

**DRAFT — F6 is not ready to dispatch.** This bounded check applies both actual public
`startupLoopTM_runFrom` and `startupLoopTM_spaceUsed_le` contracts at the last-ruler layout.
It constructs no full physical prefix, loop ledger, universal machine or target proof.
The prefix run/cut/space and hosted-loop bound remain transparent OWN hypotheses, as allowed
by PLAN(f)/Gate112-01. The withdrawn arbitrary-machine `route_space` is absent.

The authoritative artifacts are **Final-native.lean.txt** and **Final-sealed.lean.txt**.
Both pass with **exit0, zero errors, zero warnings** (2.95s and2.92s). These contain the
same successfulv5 body plus a fresh compiled inventory; removing only the irreducible guard
from the sealed input gives the exact native bytes. The three default simp definitions
`Action.apply`, `Cfg.init` and `MultiTapeTM.initCfg` are removed in both.

## Exact conditional result

`conditional_final_seam` fixes the physical bank `N=K+4`, a prefix `A`, loop `H`, and the
state injection/entry. Its raw source is `M : MultiTapeTM 1 Bool (Fin(n+1))`; its input
alphabet is Bool. The actual H2-F initial configuration occupies the first three tapes of
a `K+3` bank. `rulerHostCfg` adds the ruler at physical tape `Fin.last(K+3)`.

The literal physical endpoint `d` has live state `finish`, input position `ℓ+1`, the
encoded table/unary state, blank remaining bank tapes, the last ruler `true^ℓ`, all work
heads zero and output empty. Its full layout equality is copied from the previously
checked `last_ruler_layout` source, with the namespace changed. The theorem does **not**
use old `suffixRulerCfg_embed`, whose ruler location differs for positive scratch size.

Explicit conditional inputs are:

- `aRun : A.runFrom (A.initCfg z) T = d`;
- `aCut : ∀u<T, (A.runFrom (A.initCfg z) u).state ≠ some finish`;
- `hB : A.spaceUsed (A.initCfg z) T ≤ B`;
- generic positivity `hS : 1≤S`;
- `hloop : ∀i, H.spaceUsedByTape c t i ≤ S`, at the exact constructed hosted
  presentation `c`, not an assumed total-space bound.

`hexit` is derived from the literal endpoint. The full endpoint-to-loop `hcfg` is derived
from the actual last-ruler layout and public full-bank embedding equality; **hcfg is not
left as an OWN hypothesis**. The inputs also explicitly include the length relation
`z.length=ℓ+x.length`, needed for the configuration's physical input bound.

For the actual zero-outer seam, the probe uses public `k:=K+2`, outer `K:=0`. It transports
`A` and `d` from `K+4` to `0+((K+2)+2)` along the explicit zero-addition equality. Both
public contracts are then applied with the transported run, state, cut, layout and space
proofs. The constructor's output machine is transported back to `K+4`. The result is
exactly:

```text
U.runFrom (U.initCfg z) (T+1+t) = (H.runFrom c t).mapState Sum.inr
U.spaceUsed (U.initCfg z) (T+1+t) ≤ B+(K+4)*S
```

The proof handles machine/configuration, initialization, run, state, state relabelling,
embedding and space transports explicitly by six scratch-private equality-induction facts.
Their proofs use `cases h`, then reflexivity of identical opaque operations or the public
`embedEmitCfg_eq` route. They introduce no machine, operational behavior or library API.
The physical zero-addition identity is supplied explicitly where a rewrite creates a
side goal. No foreign definition is opened to erase a cast.

`common_budget_positive` separately proves `1≤s+(2*D+1)+ℓ+3` by arithmetic, with no source
space premise. The generic final-seam theorem honestly retains `hS`; this positivity lemma
does not establish that the suggested budget bounds any loop tape.

`actual_bundle_consumer` freshly consumes the **implemented** `CodeTM.toFinTM_eq` under
opacity and converts both the frozen bundled computation (halt and arbitrary output) and
space premises to `M.tm`. There is no invented reader hypothesis. It is generic in every
CodeTM, hence includes `TimeHierarchy.code.decode α`. The final seam is checked for the
corresponding generic raw one-tape shape; this probe does not assemble a coded source's
forwarding computation into `H`, which remains an external OWN obligation.

## Rule10, compiled inventory and controls

The irreducible guard precedes **all headers and docstrings**, including the copied layout,
transport facts, conditional consumer, arithmetic and bundle consumer. It guards32 ordinary
TCSlib definitions conservatively. A fresh unfiltered root/descendant inventory inspects
all11 source roots (five scratch-public theorems, six scratch-private transport facts) and
all six compiler descendants:17 theorem constants total, all on standard axioms or fewer.
No actual campaign declaration is added by these scratch-public probe names.

The direct type/value inventory reaches14 ordinary foreign definitions, all guarded, and
12 reducible structure projections, explicitly listed in compiled-inventory.json. The
conservative32 guards are not claimed to be32 direct dependencies. Imported theorem proof
values are consumed opaquely, not re-audited; no global legacy seal is claimed.

Manual inspection of every final simp/rw/dsimp/show/change argument found only published
field/equation theorems, Nat/Fin theorem facts, local records/hypotheses and scratch-private
transport theorems. The inherited layout's `change` steps expose local records and Core/
Mathlib Fin structure after public field equations. Equality induction never reads a
foreign operational definition. No unsafe reducibility setting or hidden unfolding escape
is used. `argument-scan.json` retains every matching line; full multiline arguments remain
in the authoritative source.

Fresh paired controls cover **all32 guarded definitions**, pointwise and abstracted. The
64 named native control theorems pass and their printed axiom sets are standard. The sealed
pair fails with exactly64 individually mapped `rfl` errors, one per identity, no unrelated
errors or warnings. `controls-index.json` records each definition/mode/name/error line;
verify.py checks identities and multiplicities, not just a count. Native/sealed control
sources differ only by the same irreducible guard. Failed negative-control `sorryAx`
diagnostics are expected failures, never evidence about a passing proof.

## Attempts, environment and remaining scope

All **nine actual Lean invocations** retain source, request, command, raw output and receipt.
Unexpected failuresv1–v4 have respectively7,2,1,1 errors. V1 showed that simp cannot push
index casts through opaque operations;v2 retained the original dependent binder;v3 exposed
a dependent rewrite motive involving an inequality proof. V4 had one remaining explicit
zero-addition side goal. V5 and both authoritative final inputs pass after equality-induction
transport. Nothing is relabelled as a successful earlier run. One offline verification
script initially had a syntax typo before execution; its diagnostic is retained separately,
and the corrected retained verify.py passes. It was not a Lean run.

All Lean invocations were sequential through the plain managed leanelab wrapper, local
budget3/machine5, four threads and niceness10, against read-only complete **oleans-mra2**
and **wt-natbits**. The supplied API head is1160c18f03fd318f0dec25738790935fa61379d4;
this task did not independently Git-attest it or a merge. Only Hierarchy is imported.
There is no compiled-output command, cache operation, screen, source/brief edit, Git mutation
or dispatch. Context source/compiled hashes are retained and checked unchanged. The initial
13-module hash capture occurred afterv1–v5; StepBlock's additional owner hash was captured
after the final runs. This is not claimed as a before/after hash seal of those earlier runs.

This discharges the **conditional final seam/type/layout** gap left by constructor-onlyv2.
It does not prove aRun/aCut/hB/hloop, choose the actual finite universal machine, instantiate
a source halt into H5/forwarding output, construct the physical prefix, establish all-tape
space bounds, absorb the final coefficient or remove space_universal's admission. First-
header→H5 and other phase interface checks are separate. Corrected unissued brief wording,
packet preparation and #230 gate/merge remain prerequisites; this is neither dispatch
readiness, merged-tree replay, external gate closure nor a design/debt ruling.
