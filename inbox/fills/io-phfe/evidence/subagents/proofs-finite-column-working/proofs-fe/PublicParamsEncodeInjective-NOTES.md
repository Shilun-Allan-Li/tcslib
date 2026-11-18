# PublicParams.encode_injective candidate after native reuse searches

Status: scratch full proof candidate checked by inspection only; proof native verification
pending. No Lean/lake/build/Git/live edit/extra agent was run. Exact supplied helper docstring
and header byte-preserved; one tactic block, no remaining holes/sorry, all lines ≤100 columns.
No consumer refactor or diagonal helper proof was written in this invocation.

## Completed native reuse search (run by root, read by this agent)

Evidence: evidence/search/diagonal-and-parameter-codec/run/results.jsonl and scope-note.txt.
Read both PublicParamsCodec{Exact,Apply}.lean.txt sources. They import ONLY Parameters (plus
LibrarySearch); no proposed shared injection theorem existed and no consumer admissions were
loaded. The exact goal is Function.Injective(PublicParams.encode (G:=G)(κ:=κ)).

* PublicParamsCodecExact: rc 1, exactly one expected no-proof error, zero sorry/warnings.
* PublicParamsCodecApply: rc 0, only partial suggestion, one sorry and one warning.
* Parent confirmed both targets typed cleanly with no complete match. This authorizes drafting
  this new helper proof; these search records are not claimed as proof verification.

## Proof and API use

Destructure the actual PublicParams and reachable-description subtype records. encode_eq
reads the existing serialization; Turing.pairEncode_injective and Prod.mk.inj recover the two
word equalities. Substitute equal description WORDS first, aligning the generator group types.
List.ofFn_injective and the common group's encG_injective recover the generator. Constructor
reflexivity then uses proof irrelevance for reachability and nonidentity witnesses.

No generator coins are selected/recovered by an algorithm; the reachability proof fields are
not inspected or compared. No group point gets a scalar witness, inverse encoding, or DLOG.
No representation, sampler, machine, or public algorithm changes. All explicit simp/rewrite
items are public equation/injectivity readers; record/subtype/equality elimination uses
primitive constructors rather than foreign defining equations. GroupDescription is the
existing reducible subtype abbreviation.

## Actual source searches/reads this invocation

* Read the exact supplied target file, Parameters.lean:46-98 and Group.lean:127-134.
* Re-ran targeted encode_injective/encode_eq/ofFn_injective/pairEncode_injective searches
  in Parameters, Mathlib/List/OfFn and shared TuringMachine/Encoding.
* Read TuringMachine/Encoding.lean:165-178 (pairEncode_injective at 173),
  Mathlib/Data/List/OfFn.lean:192 (ofFn_injective), Group.lean:132 (encG_injective).
* Read Parameters import list and native probe scope notes to confirm the helper is placed
  in the shared lower-level module rather than depending on Linear or MDDH consumer games.

The exact source-level component readers already exist. Native integration should confirm
List.ofFn_injective is exposed by the Parameters import closure; if not, its precise import
is Mathlib.Data.List.OfFn (no new mathematical helper). No new import has been edited here.

## Dependency / modularity status

This proof depends on existing proved codec readers and group fields only; no pending matrix
codec, length, correctness, DLIN game, or diagonal-gap admission is used. Root will integrate
and check it before separate consumer refactor invocations. Revised consumer dependency plan
is already in PublicParamsEncodeInjective-DEPENDENCIES.md; old manual scratch candidates
remain evidence only and should be replaced by shared-reader consumers later.
