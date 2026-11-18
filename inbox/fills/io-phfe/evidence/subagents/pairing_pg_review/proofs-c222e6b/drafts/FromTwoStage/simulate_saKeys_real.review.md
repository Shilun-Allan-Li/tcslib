# simulate_saKeys_real proof candidate

The declaration header is byte-for-byte the isolated native-searched target in
RealKeyLoopProbeHeader.lean. The fragment provides the new logical helper's
factual docstring and proof sketch. It contains one tactic block, no admissions,
no new helper declaration and no sampler/machine construction. This is an
unvalidated proof candidate, not a claim of native success. No Lean, lake, Git,
live edit or checker was run by this agent.

Root's native authorization is recorded at
evidence/search/real-committed-key-loop/run: the prefix includes proved
coinBlocks_ofFn_append and excludes both endpoint run-law helpers and game laws.
The exact? and apply? probes each had exactly one expected no-proof/no-relevant-
lemma error, with no typing errors and no complete match. Thus this helper is
proved without reference to the endpoint theorem it is intended to support.

## Structure and exact semantics

Four local lets abbreviate the existing commitment, next function, honest key
computation and wire-payload reader. The initial change only expands those local
abbreviations and the statement's local let binder; no TCSlib definition is
unfolded. Generalizing q.eval kappa - es.length retains its equality as hremaining,
and induction generalizes the existing history es and its dependent bounds.

At zero, Nat.sub_eq_zero_iff_le and hlen imply es.length = q.eval kappa.
saNext_cons, hct and the false guard expose the final return. The builder reads
that return at budget zero, exactly as required. drop_of_length_le and mapM_nil
identify the empty suffix, and map/bind readers remove the projected state.

At a positive count, Nat.lt_of_sub_eq_succ gives the guard directly. saNext_cons
and saKeyMove_eq give key index es.length. The local hcall follows only from
realSAImpl_eq, saImpl_one_onSpec, saKeyFunction_eq and realSAKey_some: an honest
key is sampled and the same accepted challenge state is retained. No condition
is imposed on the stored challenge beyond being some ch, which is sufficient
for the real key handler.

The exact next suffix element is read with List.drop_eq_getElem_cons,
List.length_finRange and List.getElem_finRange; Fin.ext uses only the equality
of natural coordinates to identify its guard proof. mapM_cons supplies the
host traversal recurrence. After sampling a key, es' appends exactly the query
and its successful encoded optional answer. length_append and Nat.sub_succ
prove that its remaining budget is the induction predecessor. saSKPayload_one,
saSKAnswer_eq, Option.map_some, decAnswer_some, Fin.cons_zero and Fin.tail_cons
read the successful payload, while filterMap_append/cons_some preserve all
previous payloads. The induction hypothesis then consumes the same tail.
map_cons, append_assoc and cons_append align the final ordered wire view.

## Root native validation points

The candidate uses the source-prefix native-searched target, but the proof body
has not been elaborated. In particular, check:

- The order of generalized IH arguments. Expected order is es, hlen, hremaining;
  if Lean orders the reverted dependent hypotheses differently, only the hstep
  application needs its arguments reordered or named.
- Local side-goal ordering. Each placeholder is followed by swap and a bullet,
  matching the established parent-validated one-block proof pattern.
- Eta normalization after the public saNext_cons reader and saKeyMove_eq.
- The bind_eq_bind/pure_eq_pure normalization after mapM_cons. Those readers are
  deliberately explicit because the core law uses do-notation/HBind while the
  target uses OracleComp.bind.
- List.length_finRange implicit n inference in the terminal drop bound, and
  Fin.ext rfl for the explicitly proof-indexed getElem_finRange coordinate.

All of these are elaboration/proof-script risks, not known mathematical gaps.
No further unsearched helper is introduced. Empty q and arbitrary prior history
payloads are covered, and the exact q-minus-prefix budget is unchanged.

The 120-line candidate keeps the anticipated FromTwoStage module below 1000
lines when combined with the real wrapper, an analogous ideal stateful loop and
the sampling endpoint. If root needs a diagnostic partial variant, preserve
this candidate and work from a separate path so the original remains reviewable.
