# One state-threaded committed-key induction

Headers/probe targets only. No helper proof, tactic block, Lean, lake, Git,
live edit, sampler or machine construction is supplied in this invocation.
Both headers remain unvalidated until root's isolated native statement and reuse
checks. Existing frozen real/ideal run-law and game-law headers are unchanged.
The concrete 118-line real candidate remains a candidate, not an additional
induction to integrate alongside the generic one.

## Main proposed theorem

StatefulKeyLoopProbeHeader.lean states TwoStage.simulate_saKeys_stateful.
It has abstract callback state sigma, handler state tau, an arbitrary stateMap,
an existing QueryImpl, and a function-description-to-StateT key callback.
The only interface hypothesis is the exact public one-key-query equation hkey.
The conclusion preserves the complete pair of adversary output and final encoded
handler state; wrappers can project it afterwards. This is stronger and more
useful than discarding the state inside the induction.

There is no injection hypothesis on stateMap, no finiteness/inhabitation hypothesis
on either state, and no claim that callbacks use fixed draw types or independent
coins. Callback randomness and its dependence on the previous state remain inside
its existing ProbComp. Only oracle one needs a correspondence law: saNext_cons
and the fixed successful challenge payload guarantee that this continuation
requests keys until it returns, never oracle zero. Existing arbitrary history
payloads are retained exactly and the call budget is q minus es.length.

The prior concrete real induction can be adapted ONCE: replace its concrete
hcall with hkey, generalize the current abstract st in the induction, and retain
the new state in the result. At the key step destruct the callback's pair ks,
append its successful answer to history, and apply the IH at ks.2. The suffix,
wire-payload and final-view list arguments are exactly shared. StateT.run_pure
and StateT.run_bind expose the standard mapM state recurrence; no second history
induction is needed for ideal simulation.

## Real specialization

For fixed accepted challenge ch, choose:

- sigma = Unit; tau = S.SAState kappa;
- stateMap = fun _ => some ch;
- impl = S.realSAImpl kappa pp pk msk;
- key = fun f => StateT.lift (S.keyGen kappa pp msk f);
- initial abstract state = ().

The hkey premise follows from realSAImpl_eq, saImpl_one_onSpec,
saKeyFunction_eq, realSAKey_some and the published StateT.run_lift law. The final
encoded state is the same some ch. Map Prod.fst over the generic joint equality,
then use the separate traversal identity below to remove the unchanged abstract
state. This yields exactly the previously searched simulate_saKeys_real header,
without integrating its standalone 118-line history proof.

## Ideal specialization

Let a = A.saCommitment C q kappa r and ch = (a.publicInput, a.privateInput).
Choose:

- sigma = Sim.St kappa pp; tau = S.SAIdealState Sim kappa pp;
- stateMap = fun st => (st, some ch);
- impl = S.idealSAImpl Sim kappa pp;
- key f st = Sim.key kappa pp st a.publicInput f
    (C.eval kappa (S.cprm kappa pp) f a.publicInput a.privateInput).

The hkey premise is exactly idealSAImpl_eq, saImpl_one_onSpec,
saKeyFunction_eq and idealSAKey_some. The StateT.mapM conclusion is already the
state-threaded list law in simulate_toSA_ideal. Its order, allowed scalar and
retained final state match verbatim. Thus only the first challenge wrapper and
projection are concrete; there is no duplicated key-history induction.

## Small additional logical traversal probe for the real wrapper

StateLiftTraversalProbeHeader.lean states stateT_mapM_lift for an arbitrary
existing ProbComp callback and arbitrary list. Its left side is the existing
StateT.lift callback traversed by List.mapM, evaluated at st; its right side is
the existing base List.mapM with the unchanged state paired afterwards. This is
a theorem about published operations, not a new traversal/host/runtime interface.
No proof is supplied. Root should typecheck and run exact?/apply? before any
proof, and prefer a found public result if the native searches locate one.

Focused full-name and conclusion searches found no direct List.mapM/StateT.lift
transport theorem. The nearest general result is LawfulTraversable.naturality /
List.naturality, but it concerns List.traverse; no published identification with
the tail-recursive core List.mapM was found, so claiming direct applicability
would hide another missing bridge. If no native match exists, a short induction
on xs using only List.mapM_nil/cons, StateT.run_pure/run_bind/run_lift and existing
host bind laws suffices. That separate list induction contains none of the
protocol/history reasoning and is shared abstract algebra, not a duplicated
118-line simulation proof. A possible lower home is the existing FE.Run logical
glue file, subject to parent's scope/import judgment; do not modify frozen host
files or introduce a new runtime definition.

## Correction to prior source notes

StateT.run_pure, run_bind and run_lift DO exist in the actual v4.25 toolchain,
at Init/Control/Lawful/Instances.lean:299, :301 and :317; run_bind_lift is :320.
Our earlier narrower search in Init/Control/State.lean missed that separate
lawful-instances file. These exact public readers should be used, rather than
reducing StateT definitions or inventing reader names. This correction was
messaged to root immediately when found. Full precise search notes are saved
in stateful-key-loop.searches.txt.

## Native isolation and size

For the protocol target, use the same verified source prefix as the previous
key-loop probes, ending after proved coinBlocks and excluding concrete
simulate_toSA_real/ideal and the later game/advantage laws. The import in the
standalone convenience file is for header visibility only; the actual isolated
probe must substitute that source prefix as root already did for earlier probes.
Run the traversal target separately using only its precise lower import.
Each statement is a term-admitted probe placeholder; root can replace its body
with each of the native exact?/apply? probes, without executing any proof here.

This replaces two protocol inductions with one estimated 110-150-line generic
proof plus small concrete specializations and a short traversal identity.
FromTwoStage should remain comfortably below 1000 lines. No mathematical
obstruction is known; the only new proof obligations are the two explicitly
listed logical headers, which require native probes before drafting proofs.
