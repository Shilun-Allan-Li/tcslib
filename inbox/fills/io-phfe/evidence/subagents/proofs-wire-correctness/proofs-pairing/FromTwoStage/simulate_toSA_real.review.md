# simulate_toSA_real: accepted challenge plus remaining key-loop obligation

The complete live docstring and declaration header are preserved unchanged.
simulate_toSA_real.skeleton.lean.inc is explicitly incomplete: its one final
admission is the fixed-tape ordered-key continuation law. There is one tactic
block, and no new helper proof or declaration in this existing-theorem fragment.
No Lean, lake, Git, live edit or checker was run; even the proved prefix tactics
still require root native checking.

Root's isolated native searches already authorized the existing helper header:
all three committed-run headers typed; exact? found no complete match and apply?
had no relevant lemma for the real/ideal run goals. The source-prefix probe
excluded the later expectation and simAdv theorems, preventing circular reuse.

## Prefix completed in the skeleton

The local a is only an abbreviation for the published saCommitment value.
saNext_nil followed by saChallengeMove_eq gives the actual first query. The
local hcall is a direct composition of existing handler readers, not a new
public/general helper: realSAImpl_eq, saImpl_zero_onSpec, saSplitChallenge_fst/snd,
saChallengeQuery_eq and Fin.append_left/right identify its input. The first
challenge case realSAChallenge_none and published bind laws give honest
ciphertext sampling, its encoded optional answer and the stored challenge pair.

The main proof uses toSA_run, buildComp_succ_of_query and simulate_query to
consume exactly the one challenge call. map_eq_bind, bind_assoc and pure_bind
move the result projection into the continuation; nil_append reads the now
singleton history. Congruence over honest encryption leaves one goal for each
actual ciphertext ct. viewWord_eq_viewWordBits identifies the target wire view.
No honest setup/encryption/key sampler is constructed or changed.

The hcall side goal uses the established one-block pattern: placeholder, swap,
then a bullet proving the reader consequence. Root should check that local goal
ordering as well as eta simplification of the two split challenge functions.

## Proposed separate logical continuation lemma: native probe first

RealKeyLoopProbeHeader.lean proposes exactly one new theorem,
TwoStage.simulate_saKeys_real, with a term-admitted header solely for isolated
native typing, exact? and apply? probes. No proof has been attempted. Search found
no matching name or conclusion shape in the repository or Mathlib.

It starts after an arbitrary successful challenge entry e, whose payload is
ctBits, with an arbitrary existing history es of length at most q. Its current
real challenger state is some ch. The stored ch need not equal the scripted
commitment: realSAKey_some uses only the master key, and the adversary reads its
own commitment, so this slight generality is valid. Existing prefix payloads
are retained exactly using es.filterMap; no assumption that arbitrary prior
history entries were canonical or successful is needed. The conclusion samples
only drop es.length (finRange q), appends their encSK words to those prior
payloads, and runs the second machine on that represented view.

The exact remaining budget is q.eval kappa - es.length. The terminal branch
es.length = q.eval kappa returns the final verdict even at budget zero, using
buildComp_zero_of_ret or buildComp_of_ret. In the positive branch the next key
is functions at index es.length, the new key entry extends the history by one,
and the recursive suffix is drop (es.length+1). This handles q = 0 as a terminal
case and never adds a timeout allowance.

The intended induction is on that remaining budget, generalizing es (or via
Nat.strong_induction_on with arithmetic equality recorded). Use saNext_cons and
hct, the appropriate guard, saKeyMove_eq, buildComp case readers, simulate_query,
realSAImpl_eq, saImpl_one_onSpec, saKeyFunction_eq and realSAKey_some. Each new
successful answer contributes encSK to filterMap using saSKAnswer_eq,
saSKPayload_one, Option.map_some, FixedLengthScheme.decAnswer_some,
Fin.cons_zero and Fin.tail_cons. The host bind laws handle sequencing.

For the ordered suffix, consume existing List.drop_eq_getElem_cons,
List.length_finRange, List.getElem_finRange and List.mapM_cons/nil. The published
drop_of_length_le handles the terminal suffix; Fin proof irrelevance identifies
its next index with the guard's index. List.filterMap_append and the singleton
payload readers preserve the prefix invariant, while mapM_cons and list append
associativity align the returned wire keys. Do not write a new list traversal,
prove generic drop/finRange/mapM facts, or assume independent setup/key draws.

After this helper passes, instantiate it with es = [],
e = the singleton accepted challenge entry,
ctBits = S.encCT kappa pp ct, and ch = the stored committed challenge.
The payload premise follows directly from saCTPayload_zero, saCTAnswer_eq,
Option.map_some, decAnswer_some, Fin.cons_zero and Fin.tail_cons. The length
premise is Nat.zero_le _. Then simp only with the existing map_eq_bind,
Nat.sub_zero, List.drop_zero, List.filterMap_nil and List.nil_append closes the
one remaining skeleton goal.

## Modularity and status

The live file has about 345 lines after insertion of the initial three skeletons.
One additional key-loop statement/proof is estimated at 120-180 lines; the real
wrapper adds about 30 proof lines, the ideal counterpart/state loop about
150-220, and expectation algebra about 100. The projected file is about 750-900
lines, still below 1000. If an actual proof approaches that margin, report the
exact lower-level invariant before adding further helpers or moving definitions.

No mathematical obstruction found. All Layered correctness/privacy and the
previous toSAAdv_run bridge are now native PASS per root, but this existing real
wrapper and the proposed continuation lemma remain unvalidated. No new theorem
or its downstream endpoint should yet be called standard-axiom-only.
