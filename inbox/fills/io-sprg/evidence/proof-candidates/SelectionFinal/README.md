# Finite first-success selection: final candidates — NOT RUN

The actual existing theorem is Params.firstGood_some_minimal at Correctness.lean:72
(parent's firstGood_minimal shorthand). Candidate01 replaces only its body.
It reuses an EXACT existing Mathlib minimum theorem rather than proving a generic
sorted-list/prefix search result. No new theorem/definition/import is necessary.

No Lean/lake/build/cache, source edits, git mutations or agent spawn. All proof
strings are untested; no exact?/apply?, tactic, kernel or seal success claimed.
Each fragment contains exactly one outer tactic block and no nested opener.

## Exact public theorem that closes the missing existing body

Mathlib/Data/List/OfFn.lean:151 declares:
  List.find?_ofFn_eq_some_of_injective
    {n} {f : Fin n -> alpha} {p : alpha -> Bool} {i : Fin n}
    (h : Function.Injective f) :
    (List.ofFn f).find? p = some (f i) <->
      p (f i) = true AND forall j < i, NOT(p (f j) = true).

Mathlib/Data/List/FinRange.lean:84 declares:
  List.ofFn_id (n) : List.ofFn id = List.finRange n.

Candidate01 reads firstGood through Params.firstGood_eq, rewrites finRange as
ofFn id using the latter public equation, instantiates the exact theorem with
f=id/p=flags/i=k and public Function.injective_id, and takes the q<hk component.
Bool.eq_false_iff converts NOT(flags q=true) to flags q=false. There is no
induction, new minimum theorem, arbitrary finite enumeration, prefix parsing,
choice or additional positivity/nonempty assumption.

The existing source proof sketch's append/ordered-search route is subsumed by
this public theorem: find?_ofFn_eq_some_of_injective uses find?_ofFn_eq_some,
which uses Core find?_eq_some_iff_getElem, itself proved via the append theorem.
No existing theorem header or statement prose change is requested.

## Selection completion and M1 fill order

| Existing source body | Candidate | Dependency |
|---|---|---|
|firstGood_none_iff :56|../Correctness/01-firstGood_none_iff.proof|firstGood_eq, Core find?_eq_none, mem_finRange, Bool.eq_false_iff|
|firstGood_some_flag :64|../Correctness/02-firstGood_some_flag.proof|firstGood_eq, Core find?_some|
|firstGood_some_minimal :72|01-firstGood_some_minimal.proof HERE|firstGood_eq, ofFn_id, find?_ofFn_eq_some_of_injective, injective_id, Bool.eq_false_iff|
|packSeed_public_block/error/flag/unscaled/scaled|../Correctness/03 through07|only packSeed_fst/snd and Equiv.symm_apply_apply|
|oneFlag_bounds|../Correctness/08-oneFlag_bounds.proof|oneFlag_eq, of_decide_eq_true, cap_eq, pow_two, Buckets.overfull_iff|

Thus the original eight simple snippets plus this missing minimum body cover
all nine elementary selection/packing/bounds stubs before the algebraic
correctness theorems. Other M1 algebra proofs remain separately assigned; this
packet does not claim they are closed. No further existing selection stub was
found in Correctness/Samplers. Minimality is a direct public-API application;
none/flag are independent of it and may be checked first in source order.

## Optional LOCAL proof steps for downstream selection transport

These are fragments for local haves, not proposed new source declarations.

02-local-sdCore_error_iff.proof expects context P,kappa,pp,I,d and goal:
  (P.sdCore kappa pp I d).err = true <->
    forall k, (P.oneSd kappa pp I d.1 (d.2 k).1 (d.2 k).2).flag = false.
It uses sdCore_err, Option.isNone_iff_eq_none and existing firstGood_none_iff.
This supplies the selection part of the later error decomposition exactly.

03-local-selected_instance_flag.proof expects the same context, k:Fin kappa,
  hfirst : (P.sdCore kappa pp I d).first = some k,
and goal
  ((P.sdCore kappa pp I d).instances k).flag = true.
It reads sdCore_first/sdCore_instances and uses existing firstGood_some_flag.
This is the selection step for the G4 selected-summand case, without unfolding
a foreign deterministic core.

At kappa=0, none_iff has a vacuous universal RHS and still proves the actual
search is none; the local error iff gives err=true. The some/minimal claims
quantify an impossible Fin0 selected index and require no added kappa>0 premise.
The canonical minimum property is therefore not weakened at the boundary.

## Public reuse searches and exact import status

Searches covered firstGood/minimal, find?/minimum/append/getElem, sorted
finRange, and ofFn finite-search APIs throughout Core/TCSlib/Mathlib. The stronger
public ofFn theorem makes the proposed append/sorted-prefix proof unnecessary.
Do NOT introduce/reprove a generic finite-search minimum helper. Public
pairwise_lt_finRange exists, but is unnecessary after this direct theorem match.

Fresh comment/string-aware closure confirms Mathlib.Data.List.FinRange and
Mathlib.Data.List.OfFn already reachable from current Correctness. FinRange
itself imports OfFn. Bool/Function/Option facts are in Lean Core. No new import,
including no heavy List search/minimum module, is proposed.

Only the named firstGood/core owner readers inspect foreign TCSlib algorithms.
Public Mathlib/Core equations and theorem APIs handle every generic search fact.
Remaining uncertainty is elaboration under the pinned environment: implicit
ofFn/type parameters, Boolean coercion in the Option local iff, and reader
rewriting under projections. Root owns actual probes/seals. Source binding,
static checks and SHA256SUMS report textual facts only.
