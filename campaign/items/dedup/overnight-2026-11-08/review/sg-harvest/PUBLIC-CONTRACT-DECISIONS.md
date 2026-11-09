# Retained SG1 kinds: bounded existing-API comparison and minimal decision proposals

These are unimplemented proposals for Seyoon's decision. No new public name, import, statement, home, route or debt permission has been approved. Existing seven-kind retention and next12.2c owner/window persist. Source is the root-supplied actual merged campaign9b5dcf46408db681bcbc721930ef2203fa6bc47d; complete relevant `.lean.txt` captures and source hashes accompany this note. This is candidate enumeration plus contract inspection, not whole-library absence.

## 1. Uniform clean contract and install/emit/stop lifting

Current exact clients are SatClean/satClean_stop/satClean_install/satClean_emit and CLA5Clean/clA5Clean_stop/clA5Clean_install/clA5Clean_emit. Their common physical contract is:

`0 < M.k ∧ ∀ nativeInput argument, ∃ t, 0<t ∧ t≤B(|argument|) ∧ (∀v<t, ¬Halted(runFrom(M, ofWords(q₀,stateWord(argument)),v))) ∧ runFrom(...,t) = {ofWords(q₀,stateWord(result(argument))) with state:=none, output:=emit(argument)}`.

The native input is arbitrary and untouched; the start/returned argument bank is canonical and all other tapes/heads are blank/zero. The entire endpoint matters. Public `FinTM.callTM_run` and exists_installCallTM/exists_emitCallTM already provide canonical positive LIVE-return calls and resource budgets, but do not directly state this HALTED-q₀ replacement/emission contract. Private install/emit already consume those public call APIs; their remaining common work is the release-stop conversion and scalar normalization. `redirectTM` is a last-emitted-verdict redirect with suppressed output, not a control-exit-to-halt adapter.

Minimal decision: choose whether to publish this unchanged contract and its `_iff` reader beside the existing call constructors in Build/Loop, or in a new small clean-call module importing that owner. Publish the existing stop/install/emit lifting contracts there; place class-level PolyTimeComputable corollaries in an explicitly chosen ClassNP home if needed to avoid a construction-to-class dependency. Keep physical and class contracts separate. Clients map by exact Sat↔CLA5 prefix substitution; no premise may be weakened to “computes f” without clean tape/output restoration. No source change is made here.

## 2. Positive-release stop adapter

Current clients are four declarations per file: StopTM, StopCfg, Stop_step, Stop_clean. The existing private machine uses Bool×State. From `(false,entry)` it executes a source action even when entry=exit; once released, reaching `(true,exit)` causes one silent stationary halt. The exact completed clean call takes `t+1`, preserves every physical field, and retains any emission on the source's final action.

`seamReleaseTM` is the closest public comparison: Unit⊕State fresh entry and exact positive-time lockstep, with first LIVE return at t and unchanged visited sets. It does not supply the private Bool×State identity or the final t+1 halt. `phaseHostTM` dispatches LIVE exits and `redirectTM` tests output verdicts; neither is a literal replacement for these frozen headers/definitions. Combining these interfaces would be an assembly/representation route decision, not an exact body citation.

Minimal decision: publish the existing positive-exit-to-halt transformer, configuration transport equations, positive-time lockstep and t+1 whole-endpoint contract in the selected call/adapter owner, with per-tape head/visited-set clauses. If instead reusing the sum-state release representation, approve a full state-transport route and its client statement implications first. Do not silently change entry=exit behavior, time, output or state representation.

## 3. Bank padding

Six exact paired clients per file: PadAction, PadTM, PadCfg, Pad_apply, Pad_run, Pad_seam. They pad initial source coordinates, preserve old tapes/heads and make added tapes blank/zero/stationary. PadAction/PadCfg/Pad_apply have arbitrary k,K with NO k≤K hypothesis; they still describe a truncated host when K<k. Only PadTM/run require k≤K, and the canonical state-word seam requires k>0.

Existing public `EmitIterEmbed.padAction/embedCfg/padAction_apply/embed_run` are close but require a supplied m≤k proof and map state through an injection/map. `Build.Embed.embedEmitTM_runFrom` is more general for selected injective slots and ambient frames, but still needs an actual injection and public configuration/table identifications. Neither directly matches every current no-inequality helper header. Merely choosing initial slots does not supply a k≤K proof when K<k.

Minimal decision: publish the existing arbitrary-dimension action/configuration padding equations and application theorem, then a run theorem under k≤K and the positive-bank canonical seam theorem. Natural owner choices are Build/Embed (the canonical embedding home) or harmonization with EmitIterEmbed's padding layer; select one before changing clients. No new truncation hypothesis may be added to old private headers. This mismatch is a concrete premise obstruction to a direct all-member repoint, not proof that public embedding cannot support a longer approved assembly.

## 4. Finite one-way transducers

Seven paired clients per file: MapWord, MapTM, MapCfg, Map_run, Map_poly, pt_tail, pt_head. General semantics emit zero/one bit on each input bit AND an optional `finish finalState` bit on the right boundary, with exact n+1 runtime, zero work tapes, arbitrary already-emitted prefix and empty-input behavior.

Existing ClassNP/Transducer publishes transduce_nil/cons/append, transducer_run, transducerTM_computes and polyTimeComputable_transduce. It emits nothing on empty input and has no final emission. It is outside both current client import closures. A general private finish may emit on empty input, so substituting that public transducer directly would be false. InputFoldTM returns its accumulator after a rewind and emits nothing; its duration/endpoint also differ. An encoded-sentinel or postprocessing construction might use current public primitives, but that is a route choice and was not implemented or declared necessary.

Minimal decision: extend/generalize the existing Transducer owner with an optional final-output function, its empty/cons/readers, exact run contract including final emission, and class closure; decide how to retain current public rows as specializations. Import decisions for the clients follow that home. No general transducer implementation is repaired here.

There are narrower existing matches: Hardness imports PolyTimeBlockLoop, whose polyTimeComputable_take1 is EXACTLY clA5_pt_head's statement, and polyTimeComputable_tail is drop1, definitionally equal to List.tail by funext/cases/rfl. Those can be separate mechanical repairs, leaving the general host untouched. SAT imports neither BlockLoop nor Prefix; stop its corresponding two leaves at the import decision rather than adding one silently. Public headD is not take1: its singleton false default on [] differs from empty output.

## 5. Polynomial bridge overhead

The two clients sat_bridge_bound/clA5_bridge_bound share the literal natural-number statement:

`len ≤ A*(n+1)^d → c*(A*(n+1)^d+n+len+1)+1 ≤ (c*(2*A+1)+1)*(n+1)^(d+1)`.

Bounded searches find those private twins and their uses; public call budgets supply the unnormalized premise but no exact named public scalar envelope was identified. General pow monotonicity/arithmetic APIs can prove it, as the current proofs already do; repeating them is not a mechanical citation to the same complete fact.

Minimal decision: publish this unchanged scalar envelope once in the class-level clean-call budget home (or another approved shared arithmetic home below both clients), with no extra positivity on A,c,d,n. Then both bodies become direct references. This is a new public declaration/home decision, not authority to create it overnight.

## 6. Finite-family shared-bank dispatcher

Seven generic members per file: HostState notation, HostEntry, HostRet, HostTM, Host_seam, Host_call, Host_clean. HostNext concrete routing tables are data and excluded from the acknowledged generic kind. SAT uses four modules, Hardness five; both expose Unit⊕Σi.State(i), pad onto a shared K-bank, preserve a complete canonical seam and output prefix, forward the source halting action's emission, then choose the parameterized continuation.

Existing public phaseHostTM/run_le/run is over LIVE phase states with an explicit extra silent dispatch step at a redirect. The current private dispatcher instead consumes a HALTING module action via emitAction, forwarding that action's output and changing control on that action. A phase-indexed host name does not identify these representations or their timings. Seam composition supports fixed left/right phases but not the entire dependent finite family and routing contract by direct citation.

Minimal decision: choose a shared Build/Seam-adjacent dispatcher contract or a separate dispatcher module. Parameterize family index, K/padding evidence, initial phase, anchor continuation and next:I→Option I; retain the existing Unit⊕Σ shape if literal private compatibility is wanted. Publish whole-configuration call/run/frame/clean contracts, with output-prefix/halting-emission semantics and no invented extra dispatch overhead. Concrete HostNext functions remain client data. Generalizing module count/routing is approved retained-kind scope, not approval of a particular new API or representation.

## 7. Unary-clock clean-call host and actual-orbit wrappers

The14 current Hardness names are12clRepeat* declarations plus clA5Iter_native and clA5Iter_shrinking. A protected unary tape is advanced once before each positive clean call. `clRepeat_complete` concludes an exact full seam with clock head N and payload f^[N]s at some time≤N*(B+2)+1, using only the N actual calls. Output computation additionally includes native load/replay and the complete budget recorded in clRepeatOutput_compute; final polynomial wrappers permit a computed arbitrary N(x) and only actual-orbit bounds.

Existing Loop emission/decision/find hosts have different payload/assembly obligations. CounterLoop interprets a binary counter; a unary word of N true bits represents2^N−1 in that API, not N. BlockLoop.emitIter requires all-word/all-iterate envelopes and fixed monomial iteration counts. BinArith.polyTimeComputable_iterate permits actual-orbit bounds but still fixes N(x)=a*(|x|+1)^k. The current arbitrary native unary N(x) and quadratic bound only over starts s(x), j≤N(x), do not syntactically imply those different premises. No unavoidable new API is proved; a guarded/countdown majorant assembly would be another route requiring explicit invariants and approval.

Minimal decision: publish the existing physical protected-unary clean-call host, full seam/frame/call/round/complete/output contracts and head envelopes in an approved Loop-adjacent owner. Publish the exact class wrapper separately in an approved ClassNP home if desired:

`FP(f) → FP(s) → FP(x↦1^(N x)) → (∀x,j≤N x, |f^[j](s x)|≤K*(|s x|+N x+1)^2) → FP(x↦f^[N x](s x))`.

Retain the precise arbitrary clock and actual-orbit premises. A shared resource/head-envelope contract and statement gate are required before consumers or a fill are commissioned; this note neither implements nor gates that interface.

## Other scoped source candidates and exclusions

EmitIterEmbed.SafeRun zero/cons/trans also match the already-imported Segment specialization with forbidden singleton and True head predicate. They are source-only candidates recorded for root; no new bridge/API is needed if written inline through segment_iff. The current assigned native tranche is the five run facts plus three separate FH-1 None selectors. Hardness5/XR2 LIVE-stop first-entry work belongs exclusively to the other agent and is not duplicated here. Current merged SG1 F4 forwarders remain already repaired; Catalog's removed old host is not reintroduced. Class-level clNative_image retains its distinct actual-image premise and separate bounded residual status.
