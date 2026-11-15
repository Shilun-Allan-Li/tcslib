# seq-zk-b search and reuse record

No Lean or Lake has been run. Instructions read: issued brief, host addendum, policy.md.
Worktree: seq-zk-b, branch fill/seq-zk-b, issue base 107f1e8c218733eac12d6b9bee6fece441271317.

Searches (2026-11-15):
- `rg` for Strategy Efficient, efficient_iff, ofNUPPT_efficient in ZeroKnowledge/Interaction.
- `rg` for runAtL polynomial-time and uniform machine readers in Randomized/{PPT,Closure,NonUniform}.
- `rg` for encodeMsgs take/append, iterated pairSndD, history counts in TCSlib.
- `rg` for unary division/remainder and coinBlock polynomial-time functions in TCSlib.
- `rg` for take/append/subtraction shapes in pinned Mathlib/Data/List/{TakeDrop,Basic}.lean,
  read-only through the derand package checkout while seq-zk cache fetch waits.
- Checked GI/ColMachines imports for SequentialZK/Composability cycles: none.

Planned reuse (no copied private lemma):
- Strategy.efficient_iff, Interaction.lean:183.
- GI.efficient_of_polyTime, GraphIsomorphism/Proofs.lean:594.
- GI.msgCount_poly / msgCount_encodeMsgs, GraphIsomorphism/EfficiencyRep.lean:247 / 238.
- GI.iterate_pairSndD_encodeMsgs, GraphIsomorphism/EfficiencyRep.lean:101.
- GI.coinSlice_poly, GraphIsomorphism/EfficiencyRep.lean:376.
- ColMachines.iterSnd_poly, ThreeColoring/Machines.lean:190.
- EncodingMachines unary toolkit, EncodingMachines.lean:81--174, :653, :674.

New declaration overlap:
- take_encodeMsgs: derives a new encoded-history prefix reader from public
  CommitmentLemmas.encodeMsgs_append (CommitmentLemmas.lean:233), public
  GI.iterate_pairSndD_encodeMsgs (:101), and Mathlib/core List.take_left.
  These give concatenation and suffix separately, rather than this bit-cut formula.
  The search also found pairEncode_nil_append (Asymptotic/BlockEncryptor.lean:160),
  pairEncode_append_right (Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean:150),
  and ColMachines.encodeMsgs_eq_flatMap (ThreeColoring/Machines.lean:912).
  No re-proof of these relatives is used: the public encodeMsgs_append is reused directly.

- takeMsgs_poly: new composition of EncodingMachines.truncate_poly (:459),
  unarySub_poly (:102), unaryLength_poly (:117), and ColMachines.iterSnd_poly (:190).
  Searches for takeMsgs/prefixMsgs and take of iterated pairSndD found no existing counterpart.
  Generic / and % unary PT wrappers will not be added: existing divNum_poly/modNum_poly with
  divNum_eq/modNum_eq suffice directly (see ThreeColoring/Parties.lean:184, :393).

- phase_poly: no prior generic sequential phase efficiency theorem found by searches
  `phase.*(poly|efficient)`, `efficient.*phase`, and `seqProver/seqVerifier.*efficient`.
  It combines existing public readers and machines; nearest consumer constructions are
  ThreeColoring.Parties.proverRepStr_poly (:393) and GI.gniVerifierRep_efficient
  (GraphIsomorphism/EfficiencyRep.lean:609). Their concrete phase lengths and graph messages
  prevent direct reuse; their generic constituent lemmas are reused instead.

- phase_efficient specializes the newly proved phase_poly through the existing public
  GI.efficient_of_polyTime (GraphIsomorphism/Proofs.lean:594); it introduces the bridge
  hypothesis on arbitrary strategies rather than a concrete graph strategy.

- verdict_poly: generic all-phase verifier verdict, constructed via existing
  EncodingMachines.polyTimeComputable_firstIdx (:326) and firstIdx_eq_iff (:277),
  generic encoded slices, and original strategy machine output.
  Nearest concrete counterpart GI.gniScan_poly (EfficiencyRep.lean:567) scans fixed graph
  challenges and is not directly reusable for arbitrary strategies/round polynomials.
  Existing first-index host is reused; no private host or transition machine is added.

- verifier_efficient combines phase_poly/verdict_poly through GI.efficient_of_polyTime
  and existing unary equality/product; no equivalent generic repeated-verifier theorem found.
  Target-specific seqVerifier/proverMoves readers remain the lead's bridge in SequentialZK.lean.
