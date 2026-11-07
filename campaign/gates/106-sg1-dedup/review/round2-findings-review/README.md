# Gate106 round2: independent F2 review

**Not yet clear to merge: #215.** The received F2 major is substantively confirmed for its six
named generic polynomial-closure reproofs. They are outside the five accepted adapter kinds
and separate dispatcher kind. No acknowledgment, gate closure or SG1 source change is made
here. The bounded follow-up finds additional mechanical members, and identifies separate
candidates without clearing them. Root/user own the disposition.

Verbatim received findings match16,970 bytes / SHA256
5a8031c24faace90a0e4d5b1bc11cc0414057e21a016712485473ccdbde25d28.
They are preserved as data; their proposed dispositions are not instructions. This review
focuses F2/scope rather than independently re-running the other audit notes, whole replay or
source screen. Existing successful replay is not a debt acknowledgment.

## Exact existing-reader result

The owner's authored source has no explicitly written pairMapSnd_eq and only the visible
pairMapSnd_pairEncode valid-input reader. That initially suggested a total-reader gap. Actual
compiled-interface checking corrects that assessment:

- **Complexity.pairMapSnd.eq_1 already exists before any query**, is public, belongs to
  ClassNP.PolyTimePairing and has AX[]. It states the full match, including malformed input.
- `.eq_def` is absent from the environment before and after #check, although its reserved
  elaboration form prints the same equation. This review does not materialize or publish it.
- Prefer the already present `.eq_1`: explicit function equality avoids the eta issue that
  defeated the initial bare simp attempt. The successful map body is:

```lean
  have he : Complexity.pairMapSnd g = (fun z => match pairDecode z with
      | some (a,b) => pairEncode a (g b)
      | none => []) := funext (Complexity.pairMapSnd.eq_1 g)
  rw [← he]
  exact PolyTimeComputable.pairMapSnd hg
```

This passes with pairMapSnd, PolyTimeComputable, pairEncode and pairDecode opaque **before
its header**. It uses a theorem equation, not simp[Def]/change/rfl to read a foreign body.
No additional reader API or debt acknowledgment is needed for this observed route. This is
an explicit assessment of this actual generated public theorem, not a blanket auxiliary-name
exemption. Other generated equations remain outside this check.

## Confirmed mechanical proof-only repoints

All imports/headers/private names can remain unchanged. PolyTimePairing is imported by NP,
which SAT directly imports; Hardness imports SAT. The source import graph verifies that
closure in each actual file. Body changes may also need concise proof-sketch corrections to
cite the public result rather than describe the removed local reconstruction.

| Consumer source and line | Existing public proof body/bridge |
| --- | --- |
| SAT2731 sat_pt_mapSnd; Hardness634 clNative_map | eq_1/funext body above, then PolyTimeComputable.pairMapSnd |
| SAT2754 sat_pt_pair; Hardness659 clNative_pair | exact PolyTimeComputable.pairEncode hf hg |
| SAT2761 sat_pt_append; Hardness679 clNative_append | exact PolyTimeComputable.append hf hg |
| SAT2714 sat_pt_pair_input | exact PolyTimeComputable.pairEncode hf polyTimeComputable_id |
| SAT2844 sat_pt_unaryLength | exact polyTimeComputable_unary |
| Hardness687 clNative_unary | exact polyTimeComputable_polyUnary C e |
| Hardness626 clNative_linear | exact polyTimeComputable_of_linear h |
| Hardness6654 clA5_pt_const | exact polyTimeComputable_const w |
| Hardness6663 clA5_pt_cond | exact polyTimeComputable_ite hp hf hg |
| Hardness6688 clA5_pt_and | exact polyTimeComputable_and hp hq |

That is **13 distinct private reproofs**: the audit6; five additional generic closures
(pair_input, unaryLength, polyUnary, conditional, conjunction); one linear lift and one
constant lift. Nine representative consumer shapes (all except the straightforward already
visible linear-lift adapter) pass in the expanded sealed v3 probe, with standardAX. Three
of those shapes cover two files. These are scratch consumers, not actual-file repairs or a
full seal of thirteen changed production bodies. Root must validate the actual repairs.

The existing scopes are narrower: ledger663–695 names clean/release/padding/transducer/
overhead plus dispatcher, not general FP pairing/concatenation/Boolean/unary closure. PL-1
(824–851) concerns the specified linear/constant and fixed-word lifts; QF-1 (1160–1162) is
specified in-file endpoint/clock factoring. Neither grants a new generic-closure debt
acknowledgment. Repointing the linear/constant members now avoids any need to infer a broad
PL-1 extension. SAT's existing linear/const/cond/and and comp-on-image wrappers already cite
public rows directly; they are not retained implementations of those closures.

## Source-inclusive census and bounded limits

Independently enumerated110 source headers mentioning PolyTimeComputable: SAT34,
Hardness76. Their complete headers/source spans/hashes are retained; this is a candidate
inventory, not110 confirmed duplications. Thirteen confirmed rows are separate. Same-line
attribute parsing independently gives26 authored declarations in PolyTimePairing.

The canonical source theorem union for these findings plus PL-1's two originals is now
**9/26 (34.6%)** in PolyTimePairing: of_linear, const, pairMapSnd, pairEncode, append, unary,
polyUnary, ite, and. This is an unrepaired source-inclusive **lower bound crossing one fifth**,
not acknowledged debt or an exhaustive census. Earlier audit5/26 covered only its named
subset; the later preliminary7/26 omitted the subsequently confirmed conditional/conjunction
sources. Mechanical retirement in the actual branch should be recorded transparently, not
called accepted debt. Do not add raw screen edges or compiled generated constants to these
source-declaration counts. No un-deduplicated cumulative SAT/Hardness union is asserted here.

Remaining bounded candidates are **not cleared or acknowledged**:

- clNative_image5186 has only-on-image correctness for its second machine; the public
  PolyTimeComputable.comp premise is total correctness. No exact class-level matching row
  was found in the bounded ClassNP search. This does not prove a new API necessary or accept
  its reconstruction. Keep this separate from the proved13 mechanical repoints.
- clNative_fill740 is a bit-parametric length-preserving scan. Its true specialization is
  unary length, but no exact arbitrary-bit public FP contract was identified here.
- clA5Iter_native6817 is a generic iteration candidate. Public PolyTimeBlockLoop contracts
  exist, but that module is not imported by either actual source; no exact statement match,
  new import, host change or permission is inferred. It needs separate bounded assessment.
- Many other candidates mention private client encodings, fields and arithmetic. They are
  retained in the catalogue for inspection rather than silently classified as harmless.

By contrast SAT's satMap_poly/head/tail and matching Hardness transducer proofs are explicitly
inside the accepted transducer kind (ledger675–677; retained exact22 list). That is a quoted
scope boundary, not an inferred exemption for all generic closures. PL-1's fixed-word tests
sat_pt_eq/clA5_pt_eq also retain their separately named status.

## Check receipts and controls

Managed plain wrapper only, complete msg4 input, local3/machine5; no compiled output,
source/cache/snapshot/Git change, screen or replay. Every Python command used -I. Final
Generated-readerv3 passes with9 standardAX roots. Its source uses the same four-def guard;
all8 final controls pass unsealed and fail sealed with exact identities/multiplicities.
For the recursive decoder, controls are a concrete nil equation and an abstracted function
on arbitrary separator suffixes; its whole symbolic List.brecOn body did not reduce in the
initial positive harness. That failed attempt is retained, together with local quotation/
metavariable instrumentation failures and the final corrected controls. No unsafe override
was used. Development-attempts.md distinguishes failures from expected negatives.

No source changes, acknowledgment, reader/API proposal, audit closure or merge permission is
produced by this review. The public existing eq_1 removes the initially suspected reader gap;
actual thirteen-site repair and unresolved broader candidates remain root/user work.
