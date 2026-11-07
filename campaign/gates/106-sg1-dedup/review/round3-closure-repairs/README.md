# Gate106 round3: thirteen canonical closure repoints

**Authorized implementation and bounded checks PASS. Not yet clear to merge: #215.**
Only ClassNP/SAT.lean and CookLevin/Hardness.lean in the assigned detached SG1 worktree were
edited. No commit/push/rebase/branch mutation, screen, compiled output, shared cache or snapshot
write occurred. Root owns the detached commit, campaign integration, fresh replay, source
screen/ledger/pack and user-selected Codex round3 audit.

## Source scope and exact freeze

Starting HEAD was verified read-only as478cd3a8dfb46094b9d8b971662f2ddadb1eccdb, with commit
object present. The before files match round2's immutable audited head-source archive exactly.
Five SAT proofs and eight Hardness proofs are the exact13 names authorized from the frozen
round2 review. Seven adjacent obsolete construction/sketch descriptions now cite their
canonical public results. There are no added/removed declarations, helpers, public names,
imports, attributes, statements, executable definitions/tables or ordering changes.

- SAT: sat_pt_pair_input, sat_pt_mapSnd, sat_pt_pair, sat_pt_append, sat_pt_unaryLength.
- Hardness: clNative_linear, clNative_map, clNative_pair, clNative_append, clNative_unary,
  clA5_pt_const, clA5_pt_cond, clA5_pt_and.

Both mapping proofs use actual serialized Complexity.pairMapSnd.eq_1 through an explicit
funext function equality, then PolyTimeComputable.pairMapSnd. They never use eq_def, a
hypothetical reader, or a foreign definition body. The other eleven proofs directly cite
pairEncode/append/id/unary/polyUnary/of_linear/const/ite/and public closures as appropriate.
All old full headers, including private binders and return types, remain literal.

Reverse only the13 exact proof-body replacements and7 documented docstring replacements,
and the entire original two files are recovered byte-for-byte. `source-freeze.json` and
`changes.json` retain this check, all old/new bodies/docs and exact headers. Source sorry
counts stay0→0 in both files. Guard instrumentation exists only in inert copies.

Final actual source hashes:

- SAT:682df0cd83abed16dac1e44768bee40a1691030eaeab1cf56373fa0677dbc6ba.
- Hardness:34e1353242bcfa3aafbb19eaea2087d0e62860dfebbb545dd3bfd6d0b0fb716d.

## Actual full-module checks

Each final native/sealed input contains the complete exact repaired source plus read-only
metadata instrumentation. All four final runs pass with zero errors on complete read-only
oleans-msg4, using plain leanelab, local3/machine5 and sequential managed wrappers. SAT takes
about16seconds; Hardness about143–145seconds. No olean/overlay was produced. The isolated
Hardness run imports msg4's SAT olean; the repaired SAT public headers/imports/attributes are
unchanged, but this is explicitly **not** a freshly compiled integrated two-module chain or
merged-campaign replay. Root will run that chain/replay separately.

Full-module existing warnings are83 SAT and66 Hardness. **No warning belongs to any of the
thirteen changed sections.** Raw logs retain all warnings; these are not claimed globally
warning-free files. No owner admission or global axiom audit is inferred from source counts.

Each actual new proof section is independently wrapped with the full guard **before its
docstring and header**. Eighteen ordinary definitions are opaque, covering the fourteen-model
inventory plus PolyTimeComputable, pairMapSnd, pairEncode and pairDecode. Action.apply,
Cfg.init and MultiTapeTM.initCfg default simp attributes are disabled inside every section.
Removing exactly these13 scratch sections/attributes reconstructs native source byte-for-byte.
Unchanged legacy proofs outside those sections retain their original context.

Compiled results cover **13 private proof roots plus5 descendants, all18 standardAX**:
SAT5+1; Hardness8+4. The matcher definitions/equations remain included. Native/sealed
name/kind/AX sets agree. Direct imported ordinary definitions are exactly PolyTimeComputable,
pairMapSnd, FinTM.ComputesFunInTime, pairDecode and pairEncode; all are guarded. Public
structure projections are listed as abbrev exceptions. Every direct imported TCSlib citation
is public; no foreign private declaration is read. Imported theorem proof bodies are consumed
through their public theorem types; AX collection is transitive.

The compiled CITED source homes are ClassNP/PolyTime, ClassNP/PolyTimePairing,
TuringMachine/Encoding and TuringMachine/Finite. Guard/model controls additionally cite
Configuration/Deterministic. Round3's cited-source screen population must reflect the final
pack's actual references; the old nine-file screen is not rerun or broadened here.

Fresh controls cover all18 definitions in point/abstract modes: **36 kernel-checked positive
successes and36 exact sealed failures**. Each identity occurs once; four diagnostic/exit
corruptions are rejected. Both calibration contexts disable default3 simps. For recursive
pairDecode, point is decode[] = none and abstract is the function on arbitrary separator
suffixes, rather than its stuck symbolic brecOn body. This scope is explicit in the retained
harness. Other definitions use the complete point/abstract defining-function controls. No
unsafe reducibility override appears. New proof bodies contain no simp/unfold/change and
only the local equality he is passed to rw; full body/argument inspection is archived.

## Preserved development failure and kernel metadata correction

Initial SAT-native passed. Initial Hardness-native elaborated its whole actual source and
printed all8 standard root AX sets, then the appended metadata failed lookup of a lazy private
matcher equation selected from env.constants. That command remains exit1; it is not called a
PASS. All initial sources/requests/logs are retained.

Lean4.25 env.constants enumerates the kernel environment, while env.find? uses the asynchronous
elaborator lookup path. The final instrumentation consistently reads ConstantInfo from that
same public env.toKernelEnv.find? kernel map. No constant is inserted, materialized, filtered
or dropped. All generated descendants are checked, including the problematic matcher equation.
Both full final native and sealed copies pass. Production source never changed for this fix.
The initial host-script quote error occurred before source mutation/Lean and is separately
recorded. There is no failed production proof attempt or weakened guard hidden in the receipts.

## Remaining candidates and gate boundary

`remaining-assessment.md` gives bounded source/API/kind comparisons without additional edits.
The fixed-bit clFillTM/run/native family literally specializes the already acknowledged
one-way transducer parameters (Unit state, constant emission b, no finish emission). This is
an existing-kind accounting conclusion for those3 inspected declarations, not a new debt
acknowledgment. Image-only composition and actual-orbit unary iteration are not automatically
covered by dispatcher/transducer acknowledgments; no exact direct FP closure repair is proved
for them. Imported operational image/loop interfaces are identified, while the unimported
ClassNP prefix/block-loop contracts do not authorize new imports. Client field packing now
uses the canonical pair closure transitively, but no global client-scaffold clearance is made.

The13 local implementations retire only when their actual repairs land; the campaign is not
yet changed. Earlier source-inclusive9/26 canonical-source findings and other watch/scope
statuses must be reconciled in the parent records, not converted silently into acknowledged
debt. Gate106 remains the user's external audit; no closure or merge approval is granted here.
