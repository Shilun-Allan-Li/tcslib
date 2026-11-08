from pathlib import Path
import json,hashlib,subprocess,os,datetime
D=Path('/private/tmp/ab34-fe9-gate-draft');O=Path('/private/tmp/ab34-fe9-draft-peer/chunk-binding-addendum');assert not O.exists();O.mkdir();h=lambda b:hashlib.sha256(b).hexdigest();manifest=json.loads((D/'MANIFEST.json').read_text());index={r['path']:r for r in manifest['files']};sf=json.loads((D/'source-freeze/SOURCE-FREEZE.json').read_text());repo='/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4';env=dict(os.environ);env['GIT_OPTIONAL_LOCKS']='0';sources={};rows=[]
for t in sf['targets']:
 for phase in ['BASE','HEAD']:
  ref=sf[phase];key=(phase,t['path'])
  if key not in sources:sources[key]=subprocess.check_output(['git','-C',repo,'show',ref+':'+t['path']],env=env)
  source=sources[key];export=(D/'qa/exports'/phase/t['path']).read_bytes();assert source==export;text=source.decode('utf-8');r=t[phase];slice_text=text[r['source_start_offset']:r['source_end_offset']];slice_bytes=slice_text.encode('utf-8');capture=(D/r['full_chunk_capture']).read_bytes();mi=index[r['full_chunk_capture']];assert h(slice_bytes)==r['full_chunk_SHA256'];assert h(capture)==mi['sha256'] and len(capture)==mi['bytes'];assert capture==slice_bytes+b'\n';blob=hashlib.sha1(('blob '+str(len(source))+'\0').encode()+source).hexdigest();assert json.loads((D/'bindings'/(phase+'-all1003-Lean-map.json')).read_text())[t['path']]==blob
  rows.append({'row':len(rows)+1,'target':t['name'],'phase':phase,'source_commit':ref,'source_path':t['path'],'source_git_blob':blob,'source_file_SHA256':h(source),'source_range_offset_kind':'Unicode code-point offsets in UTF-8-decoded actual Git source','source_start_offset':r['source_start_offset'],'source_end_offset':r['source_end_offset'],'source_start_line':r['source_start_line'],'source_slice_declared_SHA256':r['full_chunk_SHA256'],'source_slice_actual_SHA256':h(slice_bytes),'source_slice_bytes':len(slice_bytes),'capture_path':r['full_chunk_capture'],'capture_manifest_SHA256':mi['sha256'],'capture_actual_SHA256':h(capture),'capture_bytes':len(capture),'capture_equals_exact_Git_source_slice_plus_one_LF':True})
assert len(rows)==18
meta={'format':'fe9-source-slice-capture-byte-binding-addendum-v1','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'input_manifest_SHA256':h((D/'MANIFEST.json').read_bytes()),'BASE':sf['BASE'],'HEAD':sf['HEAD'],'normalization':'No source change: full_chunk_SHA256 hashes the source slice without its final newline; each saved capture appends exactly one LF. Manifest SHA256 hashes actual capture bytes. Both identities are recorded separately for all18 rows.','all_actual_Git_source_files_equal_frozen_exports':True,'all18_source_slice_and_capture_manifest_identities_exact':True,'no_Lean_screen_source_Git_or_canonical_mutation':True,'rows':rows};(O/'bindings18.json').write_text(json.dumps(meta,indent=2,ensure_ascii=False)+'\n')
md='''# FE9 source-slice and capture-byte binding addendum

This clarifies two exact byte identities without changing the frozen2837-file
packet. `SOURCE-FREEZE.json`\'s `full_chunk_SHA256` hashes the actual source slice
without a terminal newline. Every saved chunk capture is that exact slice plus
ONE LF; `MANIFEST.json` hashes the complete saved capture bytes. All18 cases
below match actual Git source at BASE9b5 or HEADd64, and the original source
ranges. Offsets are Unicode code-point positions, not UTF-8 byte offsets.

| # | Phase · declaration | Slice bytes | Capture bytes | Exact source-slice SHA256 | Actual capture-byte SHA256 |
|---|---|---:|---:|---|---|
'''
for r in rows:md+=f"| {r['row']} | {r['phase']} · `{r['target']}` | {r['source_slice_bytes']} | {r['capture_bytes']} | `{r['source_slice_actual_SHA256']}` | `{r['capture_actual_SHA256']}` |\n"
md+='\n`bindings18.json` supplies all exact commits, source/Git blobs, paths, ranges,\nmanifest identities and per-row assertions. Input manifest SHA256:\n`'+meta['input_manifest_SHA256']+'`. No source or frozen input was altered;\nno Lean, screen, mathematical or gate-clearance result is newly claimed.\n';(O/'addendum.md').write_text(md)
files=[{'path':p.relative_to(O).as_posix(),'bytes':p.stat().st_size,'sha256':h(p.read_bytes())} for p in sorted(O.rglob('*')) if p.is_file()];(O/'MANIFEST.json').write_text(json.dumps({'status':'FROZEN_READ_ONLY_FE9_18_ROW_BINDING_ADDENDUM','payload_count':len(files),'input_manifest_SHA256':meta['input_manifest_SHA256'],'files':files},indent=2)+'\n');print(json.dumps({'path':str(O),'rows':18,'MANIFEST_SHA256':h((O/'MANIFEST.json').read_bytes()),'bindings18_SHA256':h((O/'bindings18.json').read_bytes()),'addendum_SHA256':h((O/'addendum.md').read_bytes())}))
