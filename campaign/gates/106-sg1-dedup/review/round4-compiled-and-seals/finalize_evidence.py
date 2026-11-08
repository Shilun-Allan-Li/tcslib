from pathlib import Path
import json,hashlib,gzip,base64,collections,datetime,re
P=Path('/private/tmp/g106-r4-compiled-and-seals')
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
old=R/'campaign/gates/106-sg1-dedup/review/round3-final-compiled'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,d):(P/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
ctx=json.loads((P/'context.json').read_text());delta=json.loads((P/'delta-base-head.json').read_text());prior=json.loads((old/'delta-classification.json').read_text())
classification={'method':'Fresh current BASE/HEAD kernel census determines all identities. Historical category associations reused only after exact identity, owner, kind, privacy, internal flag and axiom checks. Authored names are checked in current endpoint source; all remaining exact names are generated auxiliaries. No private-ID normalization.','source':ctx['source'],'base':ctx['base'],'historical_classification_sha256':sha((old/'delta-classification.json').read_bytes()),'historical_execution_not_relabelled_current':True}
for side,sourceSide in [('added','Head'),('removed','Base')]:
 priorRows={r['name']:r for r in prior[side]};assert set(priorRows)==set(delta[side]);rows=[]
 for name,meta in delta[side].items():
  r=priorRows[name]
  for k in ['owner','kind','private','internal','axioms']:assert r[k]==meta[k],(name,k)
  if r['source_name']:
   txt=(P/'source'/sourceSide/(r['owner'].replace('.','/')+'.lean.txt')).read_text();last=r['source_name'].split('.')[-1]
   assert re.search(r'\b(?:lemma|theorem|def|abbrev)\s+'+re.escape(last)+r'\b',txt),name
  rows.append(r|{'current_full_type_ref':meta['type_repr'],'current_ci':meta['ci'],'current_attributes':meta['attributes']})
 classification[side]=rows
 classification[side+'_categories']=dict(collections.Counter(r['category']for r in rows))
classification['shared_field_changes']=delta['shared_field_changes'];classification['shared_type_changes']=delta['shared_type_changes'];classification['no_public_name_or_field_or_type_change']=delta['no_public_name_or_field_or_type_change']
save('delta-classification-current.json',classification)
# Archive checks include failed scratch preparations, without altering their original receipts.
archives=[]
for z in sorted(P.rglob('*.out.gz')):
 b=z.read_bytes();c=z.with_name(z.name+'.base64.txt');assert base64.decodebytes(c.read_bytes())==b;raw=gzip.decompress(b);stem=z.name[:-7];rp=z.with_name(stem+'-run.json');r=json.loads(rp.read_text());assert(len(raw),sha(raw),len(b),sha(b))==(r['raw_bytes'],r['raw_sha256'],r['gzip_bytes'],r['gzip_sha256'])
 errors=sum(bool(re.search(rb': error(?:\([^\n)]*\))?:',line))for line in raw.splitlines());row={'gzip':str(z.relative_to(P)),'gzip_bytes':len(b),'gzip_sha256':sha(b),'base64':str(c.relative_to(P)),'base64_bytes':c.stat().st_size,'base64_sha256':sha(c.read_bytes()),'raw_bytes':len(raw),'raw_sha256':sha(raw),'receipt':str(rp.relative_to(P)),'exit':r['exit'],'fresh_recount_errors':errors,'original_receipt_errors':r['errors'],'lossless_roundtrip':True}
 if errors!=r['errors']:assert str(z.relative_to(P))=='attempts/namespace-append/Base-census.out.gz'and errors==3 and r['errors']==1;row['explained_initial_generic_only_counter']=True
 archives.append(row)
save('archive-verification.json',{'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'all_lossless':True,'archives':archives,'failed_preparation_receipts_preserved_as_recorded':True,'no_theorem_proof_values_rendered':True})
ms=json.loads((P/'metadata-summary.json').read_text());nv=json.loads((P/'final-native-verification.json').read_text())
# Record historical/current differences for names only; historical runs remain historical.
history=[]
for side in ['Base','Head']:
 prev=json.loads((old/('map-'+side+'.json')).read_text());prev=prev.get('census',prev)
 now=json.loads((P/('map-'+side.lower()+'.json')).read_text())['census']
 history.append({'endpoint':side,'historical_map':str((old/('map-'+side+'.json')).relative_to(R)),'added_current_names':sorted(set(now)-set(prev)),'left_nine_owner_population':sorted(set(prev)-set(now)),'interpretation':'Population differences caused by upstream current context. Names outside the selected nine owners are not claimed globally removed.'})
save('historical-context-name-delta.json',history)
# Replace only the initial pending relay with the now independently validated frozen receipt.
ctx['root_MSG8_relay']='Validated frozen replay-msg8 manifest19199930c6b65de22c7b941edd82a63654971e750aafcff43e0c3caa2a642314:329 actual rows/effective-j4,0errors,static0/66; all895 input/output hashes linked and unchanged'
save('context.json',ctx)
rows=[]
for n in ['Base-census','Base-types','Base-ciattrs','Head-census','Head-types','Head-ciattrs','Head-roots','F4-SAT-native','F4-SAT-sealed','F4-SAT-controls-native','F4-SAT-controls-sealed','F4-Hardness-native','F4-Hardness-sealed','F4-Hardness-controls-native','F4-Hardness-controls-sealed']:
 d=json.loads((P/(n+'-run.json')).read_text());rows.append('| '+n+' | '+f"{d['seconds_including_slot_wait']:.3f}"+' | '+str(d['exit'])+' | '+str(d['errors'])+' | '+str(d['raw_bytes'])+' |')
report='''# Current SG1 round4 compiled accounting and F4 seals

The fresh compiled accounting and the two current F4 forwarder scopes pass. This folder is evidence for the maintainer and external round4 review; it does not close the gate or clear PR #215 to merge.

## Exact current inputs

HEAD is `078263a74fe90b92aa6228cf20e43726138afbe6`; compiled BASE is `bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c`. The source comparison parent `750987d674899d97db3c73c7278c891fa8772b40` has all1003 Lean blobs identical to the compiled BASE. The complete read-only MAC5 and MSG8 snapshots each contain895 objects. `mixed-pin-source-bindings.json` binds all25 full HEAD source captures in the frozen round4 screen directly to Git078 blobs, byte counts and SHA256; it is suitable for records/source mixed-pin assembly. The18 endpoint source captures here are exact nine-owner source, with pins in `source-pins.json`.

The frozen root replay is `campaign/gates/106-sg1-dedup/evidence/replay-msg8/`, manifest SHA256 `19199930c6b65de22c7b941edd82a63654971e750aafcff43e0c3caa2a642314`. Its17 payloads,329 ordered module rows,329 effective `-j4` launches, zero failed/error rows, static0/66, complete895 input/output object maps and unchanged outside-scope objects were independently reconciled with our snapshot maps. This reviewer did not run or relabel that replay.

## Complete selected-owner accounting

The exact original nine owners are SAT, Tautology, Hardness, Machines.Frag, Build.Catalog, Build.Contract.Basic, Build.CounterLoop, Build.Primitives and Robustness.SingleTape. Both endpoints were freshly queried, without name/privacy/internal/auxiliary filters: **7101→7063**, private5750→5712, nonprivate1351→1351. This counts the selected owners, not the entire imported environment. Complete full type expression representations, structural ConstantInfo including recursor data, reflected attributes/reducibility, effective simp theorem declaration references, ALLAX and PUBLICAX are retained in raw lossless archives and indexed maps.

There are six additions and44 removals, all private: three authored private bridges plus three generated auxiliaries added, three authored old private concatenation lemmas plus41 generated auxiliaries removed. `delta-classification-current.json` gives every exact identity and metadata. Its historical category association is reused only after exact current name/kind/owner/privacy/internal/AX checks and source declaration checks; the current execution is fresh. All1351 nonprivate names, complete types, structural ConstantInfo, attributes, owner/kind/privacy/internal flags and axiom closures are equal. All168 owned effective simp references are equal. Across7057 shared constants, ten private generated types change; the only axiom closure change drops `Classical.choice` from private `clA5Pair_sizes`. Shared other metadata/CI/attributes are equal. Type and metadata equality does not assert equality of theorem proof values.

All nine inherited nonstandard axiom closures are exactly preserved, with no new nonstandard dependency. They include `sorryAx` through existing Primitives dependencies; nine dependency closures do not mean nine direct admissions. The full census lists every such name. Upstream current-context name changes relative to historical round3 are recorded separately and are not treated as new SG1 API changes.

## Conservative current proof-root coverage

The prior43 conservative source roots and two current F4 roots resolve to45 distinct actual kernel roots (40private/5public). Fresh generated-descendant enumeration selects93 additional identities,138 total; every selected identity has only a subset of `{propext, Classical.choice, Quot.sound}`. Distribution:71 with propext/Quot.sound,58 with allthree,5 empty,4 propext only. `current45-selected-AX.json`, exact requests, full native records and the root probe preserve every mapping/owner/privacy/descendant/AX result.

The optional1969 direct cited-constant records are a names-only diagnostic. Imported theorem proof values were neither traversed nor printed. This diagnostic includes inherited Simulation and Sweep owners outside the current25-file source screen; it does not establish a whole imported API/body closure, and the pack must not describe the25-file screen that way. Every newly added F4 guard/citation is within the existing25 population. No extra broad semantic or numerical sweep was performed.

## Two current F4 scopes and controls

The exact current `sat_live_prefix` and `clA5_live_prefix` complete documentation/header/body chunks are each re-elaborated in their original imports (plus Lean metaprogramming support), both natively and under a fresh scope placed **before the entire chunk**. Their unchanged private headers and direct public `runFrom_state_ne_none_of_le` forwarding bodies are preserved verbatim. Each native and sealed run passes with exactly `{propext, Quot.sound}`.

Fresh reachable-definition inspection finds six foreign ordinary definitions: `Turing.moveInputPos`, `Turing.Action.apply`, `Turing.Cfg.inputSymbol`, `Turing.Cfg.workTapeSymbols`, `Turing.MultiTapeTM.runFrom`, `Turing.MultiTapeTM.step`. The guarded union covers both contexts. Twelve reachable projection/kernel-abbreviation identities are explicitly classified and excluded from regular function opacity controls; they are not silently called guarded. The three default simp equations for runFrom/step are removed on both sides. Removing the six local irreducibility attributes recovers each native source byte for byte. No Core/Mathlib definition is supplied as an explicit simp/rw/unfold argument in the copied proof bodies.

For each of the six guards in each actual import context, an equation goal and an abstract delta goal pass unsealed via default MetaM `refl`, and each positive value is added as a theorem declaration for kernel checking. All12 fail sealed with the exact expected `rfl` failure identities. Across the two contexts this is **24 positive kernel checks and24 exact negative failures**, not twelve total. Negative exit1 is expected and checked; there is no unsafe or transparency override. Full controls, identities, instrumentation and compressed diagnostics are retained. This is a fresh seal of the two changed F4 chunks, not a global opacity or imported-proof audit.

All17 previously repaired complete proof chunks are byte identical from source79 to078 (`prior17-source-byte-identity.json`). Their older seal records retain their actual historical source/context. This work does not claim to have rerun every legacy seal in the new context.

## Executions and lossless retention

All entries below use the pinned4.25 wrapper, one own Lean job at a time, managed local3/machine5 cap, effective `-j4`/nice10. Successful jobs have zero warnings/sorries. The two sealed control jobs deliberately exit1 with12 checked failures each.

| Run | Seconds including slot wait | Exit | Errors | Raw bytes |
| --- | ---: | ---: | ---: | ---: |
'''+ '\n'.join(rows)+'''

Every complete output has deterministic gzip plus a Base64 UTF8 companion; `archive-verification.json` verifies all18 archives including preparation attempts, exact raw hashes, gzip hashes and roundtrips. The full type raw streams are retained without truncation. No theorem proof values are rendered. Reflected effective simp entries are exact constant/level references, not expanded theorem proof expressions.

Four scratch preparation issues are preserved under `attempts/`: a missing namespace on an appended census command (three actual errors, with the original generic-only counter honestly retained), two reserved local identifiers, a projection-query namespace/type correction, and an offline Python whitespace SyntaxError before any Lean payload/run. They are reviewer probe preparation failures; none is an owner-source proof failure. Corrected complete fresh runs above passed. No attempt or failed log is overwritten or relabelled.

After all jobs, both complete895 snapshot maps and the complete frozen round3 accounting folder are byte unchanged. Source/Git/canonical records, caches and frozen evidence were not modified. No screen, replay, merge, debt acknowledgment, design choice or gate action was taken. Root retains responsibility for packet adoption, external review and current PR clearance.
'''
(P/'REVIEW.md').write_text(report)
# Every archived source is text; every binary has its exact UTF8 companion.
files=[q for q in sorted(P.rglob('*'))if q.is_file()and q.name not in {'MANIFEST.json','SHA256SUMS.txt','UTF8-files.txt'}]
assert not any(q.suffix=='.lean'or'__pycache__'in q.parts or q.suffix=='.pyc'for q in files)
utf=[]
for q in files:
 try:q.read_bytes().decode('utf-8');utf.append(str(q.relative_to(P)))
 except UnicodeDecodeError:assert q.name.endswith('.out.gz')and q.with_name(q.name+'.base64.txt').is_file(),q
(P/'UTF8-files.txt').write_text('\n'.join(utf+['UTF8-files.txt','SHA256SUMS.txt','MANIFEST.json'])+'\n')
files=[q for q in sorted(P.rglob('*'))if q.is_file()and q.name not in {'MANIFEST.json','SHA256SUMS.txt'}]
manifest={'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':ctx['source'],'compiled_BASE':ctx['base'],'status':'FROZEN complete reviewer evidence; external gate remains open','files':[{'path':str(q.relative_to(P)),'bytes':q.stat().st_size,'sha256':sha(q.read_bytes())}for q in files],'excluded_self_and_SHA256SUMS':True,'all_binary_outputs_have_lossless_UTF8_Base64':True}
save('MANIFEST.json',manifest)
files=[q for q in sorted(P.rglob('*'))if q.is_file()and q.name!='SHA256SUMS.txt'];(P/'SHA256SUMS.txt').write_text(''.join(sha(q.read_bytes())+'  '+str(q.relative_to(P))+'\n'for q in files))
print(json.dumps({'files':len(files)+1,'utf8':len(utf)+3,'bytes':sum(q.stat().st_size for q in P.rglob('*')if q.is_file()),'manifest_sha256':sha((P/'MANIFEST.json').read_bytes()),'archives':len(archives),'classifications':{s:classification[s+'_categories']for s in ['added','removed']}},indent=2))
