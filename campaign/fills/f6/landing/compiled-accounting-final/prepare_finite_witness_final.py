from pathlib import Path
import json,hashlib,re,difflib,datetime
O=Path('/private/tmp/f6-compiled-accounting-final');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');L=R/'campaign/fills/f6/landing';D=O/'finite-witness-diagnostic-final';assert not D.exists();D.mkdir();c=json.loads((O/'context.json').read_bytes());old=L/'finite-witness-diagnostic-v1'
def sha(b):return hashlib.sha256(b).hexdigest()
freeze=[]
for p in sorted(old.iterdir()):
 assert p.is_file();b=p.read_bytes();freeze.append({'path':p.name,'bytes':len(b),'sha256':sha(b)})
for ln in (old/'SHA256SUMS').read_text().splitlines():
 h,n=ln.split(None,1);assert sha((old/n.lstrip('* ')).read_bytes())==h
(D/'original-frozen-before.json').write_text(json.dumps(freeze,indent=2)+'\n')
# Exact existing reviewed diagnostic: two local class binders and two reflexive inference equations only.
block=b'\nvariable [hF6Rewind : Fintype RewindPhase] [hF6Seek : Fintype SeekPhase]\ninclude hF6Rewind hF6Seek\n\nexample : (inferInstance : Fintype RewindPhase) = hF6Rewind := rfl\nexample : (inferInstance : Fintype SeekPhase) = hF6Seek := rfl\n'
append=b'\n#check @Complexity.f6_prefix\n#print axioms Complexity.space_universal\n'
legacy=(old/'ArbitraryFiniteness.lean.txt').read_bytes();legacybase=(L/'scoped-seals-v1/Owner-sealed.lean.txt').read_bytes();assert legacy.count(block)==1 and legacy.endswith(append);assert legacy[:-len(append)].replace(block,b'',1)==legacybase
current=(L/'seam-step-repoint-preflight/Owner-sealed.lean.txt').read_bytes();meta=json.loads((O/'scoped-seals-final/source-equivalence.json').read_bytes())
line=b'attribute [local irreducible] '+' '.join(meta['guards']).encode()+b'\n';nosimp=b'attribute [-simp] '+' '.join(meta['nosimp']).encode()+b'\n';prefix=b'section F6LandingSeal09\n'+line+nosimp;assert current.count(prefix)==1
instrumented=current.replace(prefix,prefix+block,1)+append;assert instrumented[:-len(append)].replace(block,b'',1)==current
recover=current
for i in range(1,20):
 name=f'F6LandingSeal{i:02d}'.encode();pre=b'section '+name+b'\n'+line+nosimp+b'\n';post=b'end '+name+b'\n';assert recover.count(pre)==recover.count(post)==1;recover=recover.replace(pre,b'',1).replace(post,b'',1)
assert recover==(O/'Hierarchy-head.lean.txt').read_bytes()
assert b'reprStr' not in instrumented and b'valueExpr' not in instrumented and b'allowUnsafeReducibility' not in instrumented
(D/'ArbitraryFiniteness.lean.txt').write_bytes(instrumented);(D/'instrumentation-block.lean.txt').write_bytes(block);(D/'source-since-previous-diagnostic.diff').write_text(''.join(difflib.unified_diff(legacy.decode().splitlines(keepends=True),instrumented.decode().splitlines(keepends=True),fromfile='f72-diagnostic',tofile='0d-diagnostic')))
(D/'instrumentation.json').write_text(json.dumps({'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_head':c['candidate_head'],'source_sha256':c['source_sha256'],'snapshot':c['snapshot'],'original_diagnostic_source':str((old/'ArbitraryFiniteness.lean.txt').relative_to(R)),'original_diagnostic_sha256':sha(legacy),'new_diagnostic_sha256':sha(instrumented),'instrumentation_block_sha256':sha(block),'exact_original_instrumentation_reused':True,'extra_diagnostic_class_binders':['hF6Rewind : Fintype RewindPhase','hF6Seek : Fintype SeekPhase'],'reflexive_inference_equations':2,'scope09_only_instrumentation':True,'all19_ordinary_guard_sections_retained':True,'stripping_diagnostic_and_scopes_exact_current_source':True,'all_other_source_bytes_unchanged':True,'no_actual_source_public_API_or_header_change':True,'no_expanded_guard_population':True,'no_proof_value_prettyprint':True,'limits':'Conditional scratch witness test only; ineffective actual-instance opacity controls remain ineffective; no theorem-value equivalence/global seal implied'},indent=2)+'\n')
print('Prepared fresh0d arbitrary-witness diagnostic with exact old instrumentation and19guard scopes')
