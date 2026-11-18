# simulate_toSA_ideal proof candidate

The complete live docstring and exact theorem header are unchanged. The candidate
has one tactic block, no admissions and no new helper declaration or history
induction. No Lean, lake, Git, live edit or checker was run. The wrapper's body
remains unvalidated. Root has now integrated simulate_saKeys_stateful and reported
native PASS on its first attempt (rc0, no errors, no repairs). The wrapper's own
axiom/declaration check remains pending; no standard-only claim is made for it yet.
No lift/traversal proof was drafted or modified in this invocation.

## Exact specialization of the generic loop

The local commitment a is the original saCommitment. The retained challenger
pair ch contains exactly its public/private inputs. Abstract callback state is
Sim.St kappa pp; represented handler state is (state, some ch). The local key
callback is an alias for the existing Sim.key with a.publicInput, the original
queried function f, and exactly
C.eval kappa (S.cprm kappa pp) f a.publicInput a.privateInput.

The hkey premise is proved through idealSAImpl_eq, saImpl_one_onSpec,
saKeyFunction_eq and idealSAKey_some. The optional answer encodes the actual
simulated key, and the new state is the actual returned simulator state paired
with the unchanged hidden challenge. No key independence, fixed Cartesian tape,
state equality or scalar-encoding assumption is inserted. All previous group
and source/output dimensions remain opaque at this generic interface.

## First accepted challenge

saNext_nil and saChallengeMove_eq expose oracle zero's committed input pair.
The local hcall uses only idealSAImpl_eq, saImpl_zero_onSpec,
saSplitChallenge_fst/snd, saChallengeQuery_eq, Fin.append_left/right and
idealSAChallenge_none. Its input to Sim.enc is only the allowed public word.
The actual returned ciphertext is encoded in a successful answer; its actual
returned simulator state is stored alongside the hidden pair ch.

The existing toSA_run, builder query reader and simulate_query consume exactly
one challenge call, leaving q calls. The host map/bind laws and congruence over
Sim.enc reduce the wrapper to each actual ciphertext/state result (ct, st').
The singleton accepted-challenge entry retains the precise query and wire answer.
Its successful payload premise follows from the published CT payload/answer
readers, Option.map_some, decAnswer_some, Fin.cons_zero and Fin.tail_cons.

## Shared continuation and final projection

The generic loop is instantiated at that singleton entry, empty existing key
history, abstract state st', and the exact encoded ciphertext. Its bound is
Nat.zero_le _. Existing length/drop/filterMap/nil and subtraction equations
identify the full ordered key range, with no extra call allowance.
The generic conclusion retains simulator state through all adaptive key draws.
Only after that complete equality does congrArg map Prod.fst over both sides.
map_eq_bind, bind_assoc and pure_bind eliminate the final state projection, and
viewWord_eq_viewWordBits identifies the wire view with the typed public view.
Thus the result matches the exact state-threaded mapM law in the frozen header.

## Root native-check points

- The source dependency simulate_saKeys_stateful is now integrated and native
  PASS, with no repairs. This wrapper remains the next native-check target.
- Verify inference of sigma/tau from stateMap and key in the generic call.
- hkey/hcall local aliases reduce only local functions/records after public
  readers. Their final simp may need an explicit change for tuple projections;
  no TCSlib definition unfolding should be introduced.
- The two placeholder side goals use swap before the proving bullet, matching
  the established one-block convention; hct uses the same pattern.
- The final simpa relies only on local aliases plus core StateT.run evaluation
  to match the generic .run st' against the header's function application st'.
  Published state run laws are available if native elaboration prints a
  nontrivial state operation; no StateT body belongs in simp/unfold.

No mathematical obstruction found. The q = 0 path still accepts its one
challenge and then uses the generic loop's final return at budget zero.
Arbitrary r and malformed first-stage outputs remain covered by the same total
commitment parser. No machine, sampler, traversal or group-to-scalar map is
constructed by this proof.
