from pathlib import Path
import json,hashlib,datetime
P=Path('/private/tmp/mig-post234-final-head-accounting');ctx=json.loads((P/'context.json').read_text());s=json.loads((P/'metadata-summary.json').read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
rows=[]
B=Path(ctx['baseline_frozen_folder'])
for label,folder,file in [('BASE inventory',B,'Base-run.json'),('BASE CI/attrs',B,'Base-ciattrs-run.json'),('HEAD inventory',P,'Head-inventory-run.json'),('HEAD CI/attrs',P,'Head-ciattrs-run.json'),('HEAD roots',P,'Head-roots-run.json'),('BASE ordinary matchers v2',P,'Base-type-matchers-v2-run.json'),('HEAD kernel type transport v4',P,'Head-type-transport-kernel-v4-run.json')]:
 r=json.loads((folder/file).read_text());rows.append('| '+label+' | '+f"{r['seconds_including_slot_wait']:.3f}"+' | '+str(r['raw_bytes'])+' |')
report='''# Final post234 MIG compiled accounting

The fresh final HEAD compiled accounting, selected axiom checks and bounded public-type transport validation pass. No unexplained authored public type change remains within this accounting. This evidence does not close gate118 or clear PR #233 to merge; external review and the root's current replay/merge checks remain separate.

## Pinned inputs and scope

Actual source is `eaecd6b2afd992ead0844fa5f351eaf143fd1d1c`; current compiled BASE is `bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c`. The fresh current BASE was frozen earlier in sibling `baseline-current/` (66files), manifest `3c1a508ba5f2d62d8f45a27b86bcfa285bf748b0fdaf725a256994506f23f84f`. Its entire manifest, all66 physical hashes, exact toolchain/probe/wrapper/context and complete895 MAC5 objects were checked before reuse and are unchanged after this task. Initial unexecuted e3ae source/probe material in that frozen checkpoint remains labelled historical/preparation; it is not final HEAD evidence.

HEAD is the whole immutable895-object `oleans-mig-post234-native3`, authorized only after the root observed actual PASS12. Its frozen `post234-native3/` manifest is `c41b9a7636785a40a4fbce7934c85b203abc0cf75e42aa21e483396216f077fa`. Every payload, twelve ordered source hashes against GitHEAD, twelve effective `-j4` launches, successful native rows and all895 input/output hashes were independently reconciled. Only the three unchanged WordSize admissions appear in native logs. This is a twelve-owner native pass, not the root's separate full394 replay. The unfinished MMIG3 output tree was never read/imported.

The exact same twelve primary owner modules and separate Finite API context as BASE are queried. Every private, internal and compiler-generated constant is included. `source-pins.json` binds all thirteen source captures to GitHEAD blobs. The final source QA folder is frozen93files, manifest `5ce146529d1c3128f6ced9001ca53c757a26800ac18d7eef12ea3e28fb7763e0`; all its payloads, our six captured QA data files and all twelve HEAD captures were verified. QA output is used as data, never executed.

## Complete constant and axiom census

Primary twelve-owner counts are **5701→4416**: private4405→3171; nonprivate1296→1245. Separate Finite is59→59 (3private/56nonprivate), with every type/metadata/CI/reflected-attribute/axiom field exact. Combined imported selected populations are5760→4475; ALLAX covers all constants and PUBLICAX exactly all nonprivate constants (1352→1301 combined).

There are **399 additions/1684 removals**,4076 shared exact kernel names. Additions classify as3 authored nonprivate exports,62 authored private declarations (including the written named instance),334 generated/synthesized constants. Removals classify as6 authored nonprivate exports,376 authored private declarations (including named instances),1302 generated/synthesized constants. Every exact identity/kind/owner/privacy/internal flag/type reference is retained in `delta-classification-current.json` and the full classified censuses. No private-name normalization is used.

Of128 added nonprivate kernel names,3 are the authored pairMapSndTM exports,71 are DecidableEq-generated constants for the private FwdMapState,52 are proof/matcher auxiliaries and2 are generated eq_def equations. The125 generated names are not125 new written APIs. Of179 removed nonprivate names,6 are the approved old runtime aliases and173 are generated. Independently enumerated source declarations agree with final QA: public386→383 and private1080→766; the exact +3/−6 authored public names appear in `source-named-delta.json`.

All shared kind, privacy, internal flag, universe parameters, value-presence/safety/partial flags, kernel hints, reducibility, reflected attributes and structural ConstantInfo fields are exact. The sole shared owner change is generated `Turing.splitAtLastTrue.eq_1`, Catalog→Primitives. Primary effective simp rules are112→89 (11added/34removed, no changed shared rule); Finite's two are exact. Effective simp metadata records declaration heads/used constant names, not expanded theorem values. Arbitrary reverse membership of every possible attribute extension is not claimed.

Only three HEAD nonstandard axiom closures remain, exactly inherited from BASE: WordSizeComputable.mono, wordSizeComputable_logSpace and wordSizeComputable_of_spaceConstructible. BASE has26 sorry-dependent closures; HEAD has3. All other HEAD constants are standard-or-subset. The34 shared axiom changes and every closure are retained explicitly. Dependency-closure counts are not direct-admission counts; the separate native receipt records exactly three unchanged WordSize admissions.

## Every shared type difference

Raw complete type hashes change for94 shared constants:5 authored nonprivate,31 generated nonprivate,8 authored private and50 generated private. None is silently called byte equal. `all94-shared-type-change-dispositions.json` supplies each classification/disposition; `all94-exact-type-expression-differences.json` retains exact line differences and `all-shared-type-changes-classified.json` binds complete raw hashes. Exact Name parsing distinguishes constant/projection references from binder labels. Seventeen differ only after binder-name representation is erased;17 differ only in constant references after that canonicalization;60 change structure beyond those names. These syntactic categories do not assert blanket semantic equality for generated/private changes.

The five authored public differences are computesFunInTime_pairConcat_spaceUsed, pairLenCheck_spaceUsed, pairMapSnd_spaceUsed, splitSolve_spaceUsed and stripLast_spaceUsed. Their complete expressions differ only at six occurrences of three deleted private Catalog ordinary matchers, replaced by current proof-generated matchers. We freshly export exactly those three **safe ordinary definition** types/values from BASE (empty axiom closures), reconstruct their exact literal metadata in a private current probe with reprStr identity checks and kernel-checked safe defnDecls, then submit ordinary Eq.refl terms to the kernel. All three matcher-function equalities and all five complete BASE/HEAD public-type equalities pass. The exact input hashes, source and full raw receipts are in `type-transport-input-identities.json`, `TypeTransport-HeadKernel-v4.lean.txt` and the v4 run/archive. No theorem proof value is read or rendered, and no unsafe flag or transparency override is used. Equality is validated under the exact conservative reconstruction of those BASE ordinary matcher definitions; original rawtype bytes remain unequal.

Thus among380 shared authored nonprivate primary source declarations,375 complete raw types are byte exact and5 have the specific fresh kernel-validated matcher transports. This is not a claim that all shared nonprivate/generated types are byte equal. The eight authored-private differences include the five approved header exceptions (counter_count, loopHost_contracts, loopHost_prepare, condTM_start, timed_start), two loopFrame proof-identity references and one loopHost_payload_scan matcher reference. The first three approved exceptions strengthen private statements; the two newly approved carrier transports retain their exact separate sourceQA approval/equality evidence. No additional design decision or header exception is introduced here.

## Current source roots and descendants

Independent comment-aware enumeration agrees exactly with final QA's **153 changed source proof roots (66public/87private)**. Union with original17 targets, historical144 references, fourteen consumers, current reader/body changes and five approved private headers resolves to154 unique actual kernel roots (67nonprivate/87private). The only additional conservative root is the existing upstream redirectTM_spaceUsedByTape reference in its uniquely resolved Wrappers home. The old Catalog root is not counted as a second declaration.

Fresh native enumeration covers234 generated descendants in addition to those154 roots, **388 distinct constants**, all standard-or-subset:209 with the standard three,160 with propext/Quot.sound,14 with propext and5 empty. Every original17 target is included and standard-or-subset. Complete exact root/name/owner/privacy, descendant and AX maps are retained. The5749 direct cited-constant records inspect only names from source-owned types/values; imported theorem values are not traversed. This is not a global Rule10 seal, an import/body-closure screen, proof-value equality or whole-environment absence claim. Other agents own the current consumer/reader scopes and source screens.

The old4413 census stays historical. Exact current name comparison is +5/−2: two upstream public APIs and three private auxiliaries added; two private auxiliaries removed. No old run is relabelled current.

## Native runs, preservation and limits

| Run | Seconds including slot wait | Complete raw bytes |
| --- | ---: | ---: |
'''+ '\n'.join(rows)+'''

All successful jobs have zero errors/warnings/sorries and use pinned4.25 through the managed wrapper, one own Lean job at a time, local3/machine5 cap, `-j4`/nice10. Every complete raw output is retained as deterministic gzip plus its exact UTF8 Base64 companion, including all diagnostic attempts. The full BASE153,575,104-byte and HEAD131,767,332-byte inventory streams are lossless; full type expressions are not truncated. The first baseline matcher-export preparation lacked Repr ReducibilityHints; subsequent private type-literal preparations exposed raw hygiene-name syntax and do-layout issues. Those three preparation failures remain intact. A fourth diagnostic reconstructed and kernel-checked all three matcher equalities, but default MetaM refl stopped on the first deeply embedded type. It remains a failed MetaM diagnostic; it is not relabelled PASS. Final v4 instead passes direct ordinary kernel Eq.refl checking for all eight equalities. This changes no source proof and uses no transparency override.

`archive-verification.json` verifies all nine raw gzip/Base64 pairs. `final-verification.json` binds the final successful results. All895 BASE and HEAD object hashes, frozen baseline66 files and historical compiled50 files remain byte unchanged after all jobs. No source, Git, canonical, snapshot or cache mutation, screen, replay, merge, debt acceptance, design ruling or gate action was performed. Root retains packet adoption, external audit and final PR clearance.
'''
(P/'REVIEW.md').write_text(report)
# Freeze a complete, uncapped UTF8 index and physical manifest. Actual .lean remains private.
for q in P.rglob('*'):
 if q.is_file():assert q.suffix not in ['.lean','.pyc']and'__pycache__'not in q.parts,q
files=[q for q in sorted(P.rglob('*'))if q.is_file()and q.name not in ['UTF8-files.txt','MANIFEST.json','SHA256SUMS.txt']];utf=[]
for q in files:
 try:q.read_bytes().decode('utf8');utf.append(str(q.relative_to(P)))
 except UnicodeDecodeError:assert q.name.endswith('.out.gz')and q.with_name(q.name+'.base64.txt').exists(),q
(P/'UTF8-files.txt').write_text('\n'.join(utf+['UTF8-files.txt','MANIFEST.json','SHA256SUMS.txt'])+'\n');files=[q for q in sorted(P.rglob('*'))if q.is_file()and q.name not in ['MANIFEST.json','SHA256SUMS.txt']];manifest={'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':ctx['source'],'compiled_BASE':ctx['base'],'status':'FROZEN final current metadata/AX/type-transport evidence; external gate remains open','files':[{'path':str(q.relative_to(P)),'bytes':q.stat().st_size,'sha256':sha(q.read_bytes())}for q in files],'excluded_self_and_SHA256SUMS':True,'all_binary_outputs_have_complete_UTF8_Base64_companions':True};(P/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');files=[q for q in sorted(P.rglob('*'))if q.is_file()and q.name!='SHA256SUMS.txt'];(P/'SHA256SUMS.txt').write_text(''.join(sha(q.read_bytes())+'  '+str(q.relative_to(P))+'\n'for q in files));print(json.dumps({'physical_files':len(files)+1,'UTF8_files':len(utf)+3,'bytes':sum(q.stat().st_size for q in P.rglob('*')if q.is_file()),'manifest_sha256':sha((P/'MANIFEST.json').read_bytes())},indent=2))
