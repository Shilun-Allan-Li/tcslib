# F6 phase interfaces: bounded pre-ship PASS

**DRAFT — not ready to dispatch.** The seven inert phase-interface proofs pass natively and with
37 foreign definitions opaque, including complete headers and proof bodies. This checks the
prescribed public geometry and casts; it constructs no complete physical prefix, universal-machine
proof, global space ledger or target. No source, API, brief, Git, cache or shared snapshot changed.

Authoritative inputs are `Phases-v4.lean.txt` (sealed, exit0/errors0, 2.46 s) and its exact guard-
removed counterpart `Phases-native-v4.lean.txt` (exit0/errors0, 2.49 s). The machine context is the
read-only complete mra2 tree with wt-natbits; thirteen source/compiled pins remain unchanged.

## Checked connections and exact bridges

| Phase / connection | Actual bridge and premises discharged in the probe | Result |
| --- | --- | --- |
| Skip first ruler | `skipTM_run_ofCfg`, at the physical last tape and word `true^ell1`; explicit OWN entry state `.run`, last head zero, exact ruler contents. The required `[0,ell1]` read window follows from that presentation. | Actual skip takes `ell1+1` steps, has its strict done cut, preserves all other fields, and leaves selected head at `ell1+1`. |
| One-cell correction and next scan type | Reuses the previous actual fixed correction leaf, rechecked under the expanded guard: its table is `tapeAction last 0 none (-1) true`; `step_of_tapeAction_move` proves its one-step run. `skip_correction_connection` feeds it the actual skip endpoint via public `Cfg.mapState_*` fields. | A correction machine chosen before input/configuration returns the selected head to `ell1` in one step. Relabelling to `Fin 4` gives scan control zero, with every tape, native input head and output equal to the pre-skip values. |
| Nonblank second scan | `headerScanTM_run` plus `headerScanCfg_ruler(m:=ell1)`. Explicit OWN native presentation is `inputPos.val=1+ell1`, `z.drop ell1=pairEncode u v`; the old ruler is `true^ell1` and its head is `ell1`. | With `ell2=2*|u|+2`, exactly `ell2` steps yield ruler `true^(ell1+ell2)` from the same origin, both endpoint coordinates `ell1+ell2` / native `1+ell1+ell2`, strict scan cut, silence and unchanged other banks/heads. The old ruler is nonblank; no blank-ruler hypothesis is substituted. |
| Scan to rewind | Public `Cfg.mapState_*` equations, from the scan's control three and derived head/ruler fields. | Rewind entry has actual `.start`, total ruler length/head `N=ell1+ell2`, unchanged physical input/output and the same tape contents. |
| Final framed rewind | `rewindTM_run_ofCfg` at `u=true^N`, `n=N`. Its `-1≤p<N` read window follows from the full ruler equation and head `N`; `n≤|u|` is `length_replicate`. | Actual rewind takes `N+2`, strictly reaches `.done`, resets the selected head to zero, preserves all tapes/input/output and every other head at every prefix. Its public selected-head frame is `[N-N-1,N]=[-1,N]`, including the left and right boundary cells; the probe exports the endpoint and all-other-head frame. |
| Installed bank and indices | `embedEmitCfg_forwardLoop_init(k:=1,K:=K)`, with the actual `Fin.castLEEmb : Fin3 ↪ Fin(K+3)`. Public map-state fields expose the already published literal bank layout. | The bank has entry control, native head one, all heads zero/output empty, table at value-one tape, unary state at value-two tape from cell two, all other tapes blank. The earlier last-ruler layout adds the physical last tape: K+4 total, ruler K+3. |

The input-position equation needed by the second scan follows by rewriting its unchanged native
input position with the explicit OWN starting equation. The ruler equation follows similarly from
the full tape equality returned by the skip/correction connection. Control relabellings use actual
public state-map fields, not hypothetical reader lemmas. All casts/length bounds in the full
second-scan header are checked, including empty headers (`ell2=2`) and arbitrary suffixes.

Component row times above include each row's own exit behavior. A `seamCompTM` boundary adds the
separate **one dispatch step** in its published run contract. No aggregate prefix time formula or
seam-composed prefix execution is claimed here; Claude must count actual boundaries in its fixed
assembly and prove the named prefix OWN run/cut/silence/space contracts. H5 handoff and the final
conditional seam are covered by the parent's separate v5/v7 work, not duplicated here.

## Rule 10, actual checks and failures

The final guard extends the previous34 with `headerScanCfg`, `skipTM`, `rewindTM`; three default
simp definitions are disabled. The actual compiled type/value inventory sees eighteen ordinary
foreign definitions, all guarded. Seven roots and six descendants have only subsets of
`propext`, `Classical.choice`, `Quot.sound`. Imported theorem proofs are consumed opaquely.
Every final rewriting/simplifier argument was inspected: only public equations/local equalities
and local lets `ell2,e,sigma` are expanded. Literal local record projections and Core reductions
supply no foreign-definition exception.

Fresh controls cover all37 definitions in pointwise and abstracted modes: **74 kernel-checked
unsealed successes**, then **74 expected sealed rfl failures**, exactly one per definition/mode.
A same-total duplicate/drop corruption is rejected. The controls use the reviewed maintainer
reflective harness; no delivered code is executed. Source/compiled pins and all inputs/logs/receipts
are retained in `context.json`, `compiled-inventory.json`, `controls-verification.json` and the
manifest. These are isolated managed-wrapper checks, not a replay.

Unsuccessful inputs remain intact: second-scanv1 had one local ell2 Nat/Int normalization goal;
Phasesv1 had a local record-layout syntax error plus five unexpanded embedding-let rewrites;
v2 had one if-valued literal-record application goal; v3 exposed three branch-local versions of
that goal and five local skip-let rewrite goals. V4 fixes the local projection/let forms without
changing any public interface. Failed scratch `sorryAx` prints are not passing evidence.

No missing public API or type seam was found for these scoped connections. The full physical
prefix execution, strict final cut/silence/space bound, actual dispatch composition and all-tape
final simulation ledger remain explicit Claude OWN proof work. This report grants no route change,
API/debt approval, permission to fill the target internally, or dispatch readiness.
