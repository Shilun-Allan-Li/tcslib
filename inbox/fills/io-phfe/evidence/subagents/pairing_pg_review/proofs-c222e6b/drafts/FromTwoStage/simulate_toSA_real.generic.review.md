# simulate_toSA_real proof through the shared generic loop

The complete current live docstring and theorem header are preserved unchanged.
The new full candidate has one tactic block and no admissions, no helper
declarations and no duplicated history induction. The older structured skeleton
and standalone 118-line real-loop candidate remain untouched as drafting history;
this generic wrapper is the intended replacement, not an additional induction.
No Lean, lake, Git, live edit or checker was run. The wrapper remains unvalidated.

simulate_saKeys_stateful is now integrated and native PASS on the first attempt,
without repairs, per root. stateT_mapM_lift now also has a root-confirmed native PASS. Its proof uses the
explicit OracleComp bind/pure readers alongside the StateT readers. Both shared
dependencies are available; the wrapper itself still needs native validation
before any standard-only claim.

## Specialization without new runtime machinery

The local commitment a and accepted challenge ch are the original scripted data.
Abstract state is Unit. stateMap ignores its argument and retains some ch.
The local key callback is exactly StateT.lift of the existing honest keyGen.
No new sampler, host, implementation, adversary or algorithmic interface is
defined, and no group encoding is inverted.

The hkey law follows from realSAImpl_eq, saImpl_one_onSpec,
saKeyFunction_eq and realSAKey_some. StateT.run_lift is its published scalar
state-transformer law: the honest key is returned paired with unchanged Unit
state. The existing bind readers identify this with the honest handler's actual
encoded optional key and unchanged accepted challenge. Unit is never sampled,
and no separate subsingleton argument is required because stateMap is constant.

The first challenge uses saNext_nil/saChallengeMove_eq, the zero adapter reader,
public challenge splitting/concatenation readers and realSAChallenge_none.
The result is honest encryption, its successful wire answer and some ch.
toSA_run, buildComp_succ_of_query and simulate_query consume exactly the first
call, leaving q. Congruence over honest encryption reduces the proof at each
actual ciphertext, whose singleton successful entry supplies the generic loop's
accepted payload premise through the CT answer/payload readers.

The generic loop is applied with empty existing key history and initial Unit
state (). The zero-prefix equations expose the entire finRange q. The existing
stateT_mapM_lift identity then rewrites its stateful traversal into the original
ordered List.mapM keyGen, pairing only its unchanged Unit state. Finally,
congrArg maps Prod.fst over the joint simulation equality; map_eq_bind,
bind_assoc and pure_bind remove both bookkeeping states. The typed/wire
viewWord_eq_viewWordBits equation identifies the exact second-stage word.

## Root native-check points

- Both shared helpers are now native PASS. The wrapper still needs its own
  native check and stored-declaration axiom audit.
- hkey uses the public StateT.run_lift reader explicitly. The initial change
  expands only local aliases and the core StateT.run projection, never a
  TCSlib definition body.
- The hlift rewrite must match the local key callback under mapM; it is a
  local alias of StateT.lift, and the base callback is stated explicitly to
  avoid higher-order inference ambiguity.
- Verify hkey/hcall and payload placeholder goal ordering under the established
  swap/bullet pattern. The exact frozen header is unchanged.
- Final simpa uses local stateMap/key/a/ch aliases and public map/bind/view
  equations. If native printing exposes a tuple eta mismatch, use an explicit
  local change rather than unfolding implementation/view definitions.

No mathematical obstruction found. q = 0 consumes exactly its one challenge
then returns through the generic loop at budget zero. Arbitrary composite tape
strings and total parser defaults remain covered, and all original committed
function words are retained exactly.
