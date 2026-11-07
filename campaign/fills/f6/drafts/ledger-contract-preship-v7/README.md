# F6 conditional ledger/arithmetic pre-ship v7

**Bounded conditional checks PASS; F6 remains unissued.** This checks types, finite indices,
public source conversion and coefficient arithmetic. It constructs no hosted-loop ledger,
physical prefix, universal machine or target proof; it makes no API/debt/dispatch decision.
All actual source, admission, brief, Git, snapshot and cache contents were untouched.

## Checked contracts

`Final-sealed.lean.txt` and its exact guard-removed `Final-native.lean.txt` both elaborate with
zero errors/warnings, importing only `TCSlib.Complexity.SpaceComplexity.Hierarchy` in the pinned
API1160 / complete mra2 context. This is the implemented prerequisite reader context, not a
claim that its PR has merged. Source and snapshot hashes were checked before and after.

1. **`source_bundle_budget`, line13.** The actual `CodeTM.toFinTM_eq` and
   `FinTM.computesInTime_iff` convert the bundled premise into the native coded machine's halt,
   exact arbitrary output and space bound. `CodeTM.one_le_spaceUsed` plus the given budget
   proves `1≤s`. No wellformed/canonical-code, output, input-length or time restriction appears.
2. **`conditional_ledger`, line30.** Takes explicit OWN source-first-halt and hosted-loop
   first-halt/output contracts, plus the four tape-case premises below. It retains those
   source/host halt/live/output facts and derives the full per-tape bound. Those facts are
   passed through as hypotheses; this check does not produce them for the actual chosen loop.
3. **`coefficient_handoff`, line91.** Uses the target's exact
   `Complexity.TimeHierarchy.code.decode α` source. Quantification is
   `K,D,p,q → ∀α, ∃C, 0<C ∧ ∀s,x,output,t, ...`. Thus the positive coefficient is chosen
   before every run parameter. The computation premise retains arbitrary output/time, although
   the numerical calculation needs only the source space premise.
4. **`physical_index_transport`, line125.** The actual `Fin.castLEEmb` of first3 tapes into
   `Fin(K+3)`, followed by H5's `.castSucc`, gives physical indices0,1,2. Every idle bank index
   with value≥3 lies outside that image and its castSucc differs from the last ruler. Ruler
   index is `Fin.last(K+3)` with valueK+3. Here `(K+3)+1`, `(K+2)+2` and `K+4` have the same
   Lean type. This matches the actual outer-K=0 seam tape count. No old index3-ruler layout
   is substituted for last-ruler geometry.

## Explicit OWN boundary and numerical handoff

Let `M=(TimeHierarchy.code.decode α)`, `ℓ=2|bits s|+2|α|+4`, with physical N=K+4.
The following are **hypotheses, not supplied actual-loop proofs**:

| Tape/contract | Exact OWN premise | Derived count |
| --- | --- | --- |
| Source first halt | `t0≤t`, source at t0 has state none, is live at every earlier u, and has exact output `output` | no first-halt extraction is supplied here |
| Hosted loop | from its presented `c`, at r state none, earlier states live, exact same `output` | no host run/first-halt/output transport is supplied here |
| Mirror, physical0 | visited set equals source tape0's visits through t0 | ≤s, by public membership/cardinality/tape≤total facts and t0≤t |
| Auxiliaries, physical1 and2 | every head position through r is in integer `[-Dα,Dα]` | ≤2Dα+1 each |
| All idle bank tapes3..K+2 | each full visited set is exactly `{0}` | 1 each; vacuous when K=0 |
| Last ruler, physicalK+3 | every position through r is in integer `[-1,ℓ]` | ≤ℓ+2, including BOTH -1 and ℓ boundaries |
| Physical prefix | actual startup space B satisfies `B≤pα+qα*ℓ` | still OWN, with p,q fixed per code before all run parameters |

Both auxiliaries use one common per-code radius Dα; if concrete rows initially yield two
radii, supplying a common dominating D is an OWN ledger choice, not established by this probe.
The idle singleton `{0}` requires actual initial idle heads0 and framing; it is not inferred
from tape count or blank contents. Prefix constants pα,qα are named external OWN constants;
no bound for the actual physical prefix is smuggled into the arithmetic.

Choose the conservative common row

```
S = s + (2Dα+1) + ℓ + 3
Aα = 2|α|+6
Eα = 2Dα+4
Cα = pα + qα*Aα + (K+4)*(1+Eα+Aα) + 1.
```

Public `length_bits_le_self` and `s≥1` prove `ℓ≤Aα*s`, then
`S≤(1+Eα+Aα)*s` and **`B+(K+4)*S≤Cα*s`**, with Cα>0.
No planning time polynomial or unspecified physical-prefix constant is asserted as proved.
`1≤S` is immediate from `s≥1`; the public seam still separately needs its actual run,
exit, strict live-exit cut and complete mapped endpoint identity.

The tape/count/arithmetic contracts are separate proved local probes. This task does not
reinstantiate the public final seam or construct its actual prefix/loop witnesses. Those
remaining consumers are distinct from this numerical handoff; the existing v5 work is not
claimed as a new run here.

## Evidence and controls

- Seven managed-wrapper runs are retained: v1 fails at a proof-dependent Fin substitution;
  v2 fails where a sealed cardinality conversion needed the published equation; v3 passes;
  final native/sealed pass; positive/negative controls behave exactly. Both failed attempts
  remain unchanged with full outputs and requests/receipts.
- Strong guard37 ordinary definitions is placed before every theorem docstring/header.
  Default simp entries for Action.apply, Cfg.init and initCfg are removed in both contexts.
  All8 directly cited ordinary TCSlib definitions in root/descendant types and values are
  guarded; Nat.bits is additionally guarded. Public projections/abbreviations are identified
  separately in `metadata.json`. Imported theorem proof bodies are not recursively rescanned.
- Fresh74 paired controls (point and abstract for each37) pass unsealed and fail under the
  exact seal. Checker verifies exact identities/multiplicities and rejects four corrupted
  diagnostic/exit cases. Controls add no proof to the four tested theorem roots.
- All4 roots plus16 compiled descendants use only propext/Classical.choice/Quot.sound.
  Native/sealed metadata output bytes match. No target theorem's axiom closure is claimed.
- Named constructor fields, simp/rw/dsimp arguments and direct imported definitions were
  inspected; no explicit foreign-definition unfolding escapes the guard. Only local
  coefficient names and public arithmetic facts occur in simp/dsimp brackets.
- `verify.py`, `metadata.json`, `source-scan.json`, `verification.json`, input hashes and all
  raw receipts are retained. An initial Python scan accidentally matched the required
  `attribute [-simp]` setup; `verification-attempts.json` records its correction. No Lean
  source changed for that check. All Python ran with `python3 -I`; all Lean used sequential
  plain leanelab managed wrappers, local3/machine5 and authorized scratch lock access.

No fresh reader/type gap appeared in these **conditional** contracts. That does not establish
that the actual OWN prefix, first-halt/output, per-tape bounds or full F6 route have been built.
The readiness review's unissued-brief/supplied-prefix HOLD remains untouched.
