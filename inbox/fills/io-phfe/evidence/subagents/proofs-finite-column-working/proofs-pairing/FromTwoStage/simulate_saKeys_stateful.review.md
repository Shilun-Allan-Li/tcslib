# simulate_saKeys_stateful proof candidate

The declaration header is byte-for-byte the natively searched generic header in
StatefulKeyLoopProbeHeader.lean. The new logical helper receives a factual
proof-oriented docstring. The candidate has one tactic block, no admissions and
no new helper declaration. No lift proof is included or changed. No Lean, lake,
Git, live edit or checker was run. Native validation remains pending.

Root authorized this proof from evidence/search/stateful-committed-key-loop/run:
both generic and lift targets typechecked cleanly; exact? could not close and
apply? had no relevant lemmas, with one expected search error per target and no
other errors. The protocol search environment excludes future concrete run
endpoints and game laws. No downstream result is used in this candidate.

## One shared history induction

The prior concrete real candidate supplies the suffix and wire-history pattern;
its 118-line independent history proof should not be integrated alongside this
one. Here a single induction generalizes BOTH es and the callback state st.
The simulation retains its full Bool × tau output, rather than projecting early.
The only handler fact used is the supplied hkey, for oracle one at stateMap st.
There is no assumed law for oracle zero, no injectivity/finiteness requirement
on stateMap/sigma/tau and no independence assumption on stateful key draws.

At the terminal branch, the same natural-subtraction bound gives es.length = q.
The builder reads its final verdict at budget zero. StateT.run_pure applied to
List.mapM_nil supplies exactly the unchanged abstract state st, and its image
stateMap st matches the handler's retained state in simulate_pure.

At a positive branch, saNext_cons, hct, the guard and saKeyMove_eq expose the
same query. The hkey equation replaces the one implementation call with its
existing stateful callback, including the successful wire answer and represented
new state. List.mapM_cons, StateT.run_bind and StateT.run_pure give the exact
callback/state recurrence on the right. Congruence over that callback reduces
the goal for every actual pair (sk, st'). The IH is applied from st' and the
extended history, carrying the predecessor budget.

The list argument reuses the existing drop/finRange/mapM/filterMap laws exactly
as the concrete candidate did. No traversal, state host, optional-answer sampler,
implementation or adversary is constructed. The final payload calculation uses
map_cons and append laws; the final state is stateMap keys.2 on both sides
without a separate argument or early projection.

## Published state readers

StateT.run_pure and StateT.run_bind are the public core equations at actual
Lean4.25 Init/Control/Lawful/Instances.lean:299 and :301. They are used by name,
rather than passing StateT definitions to simp/unfold. run_lift at :317 is not
needed in this generic proof; it belongs to the later real-wrapper specialization.
Local call j abbreviates key (a.functions j); matching (call j).run st against
key (a.functions j) st uses only the local abbreviation and the core StateT.run
projection. No TCSlib definition is reduced by a rewrite/change/simp body.

## Native-check risks to inspect

This remains an unvalidated full candidate. Root should check the following
elaboration points before calling it complete:

- Whether induction preserves the generalized binder names es, st, hlen and
  hremaining used in the named IH application. The names are explicit to avoid
  dependence on proof-argument order; adjust only proof arguments if needed.
- Eta normalization in hn after saNext_cons and the local aliases next/a.
- Rewriting hkey after simulate_query, then normalizing the RHS StateT mapM_cons
  with run_bind/run_pure and the host bind readers. If the callback application
  is printed as key (...) st instead of (call j).run st, local/core reduction
  should identify them; no TCSlib unfolding is needed.
- Local side-goal order: each placeholder uses swap before its proving bullet,
  matching the parent's established one-block convention.
- Fin/getElem proof-index inference and the terminal drop length bound, already
  isolated as local proof terms using published laws.

No mathematical gap or new helper need was found. The generic statement covers
q = 0, zero-width wires, noninjective represented states and arbitrary existing
history payloads. It replaces duplicated real/ideal history reasoning; later
wrappers should only establish hkey and project this joint equality. The separate
lift/traversal target remains untouched and unproved in this invocation.
