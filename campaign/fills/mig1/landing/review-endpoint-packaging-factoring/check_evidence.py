"""Verify the bounded proposal, exact guard restoration and 90 isolated controls."""
from pathlib import Path
import collections, hashlib, json, os, re
p=Path(__file__).resolve().parent
root=p.parents[4]
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
labels=['helper-sealed-v1','transfer-sealed-v1','complete-sealed-v2','complete-native-v2',
        'controls-unsealed-current2','controls-sealed-current2']
expected={label:(0,0) for label in labels};expected['controls-sealed-current2']=(1,90)
receipts=[]
for label in labels:
 r=json.loads((p/(label+'.json')).read_text());command=r['command'];source=Path(command[-1])
 assert (r['exit'],r['errors'])==expected[label]
 assert sha(source)==r['input_sha256'] and sha(p/(label+'.out'))==r['output_sha256']
 assert r['actual_catalog_before_sha256']==r['actual_catalog_after_sha256']=='cfc4365531fade3b5f5e358f0285d4792b239412bc2f1ac662673fdc5f54fb73'
 text=(p/(label+'.out')).read_text()
 assert len(re.findall(r'^.*:\d+:\d+: error(?:\([^)]*\))?:',text,re.M))==r['errors']
 receipts.append({'label':label,'exit':r['exit'],'errors':r['errors'],'seconds':r['seconds']})

mapping=json.loads((root/'campaign/fills/mig1/landing/review-catalog/Catalog-controls-checked-map.json').read_text())
assert len(mapping)==45 and all(row['isolated_seal'] for row in mapping)
expected_lines=collections.Counter(line for row in mapping for line in [row['pointwise_error_line'],row['abstracted_error_line']])
def validate_negative(text):
 rows=re.findall(r'^.*:(\d+):\d+: error(?:\([^)]*\))?: (.*)$',text,re.M)
 assert len(rows)==90
 assert collections.Counter(int(line) for line,_ in rows)==expected_lines
 assert all(message.startswith('Tactic `rfl` failed:') for _,message in rows)
negative=(p/'controls-sealed-current2.out').read_text()
validate_negative(negative)
diagnostics=re.findall(r'^.*:\d+:\d+: error(?:\([^)]*\))?: .*$',negative,re.M)
for corrupt in ['\n'.join(diagnostics[1:]+diagnostics[:1]+diagnostics[:1]),
                '\n'.join(diagnostics[:-1]+diagnostics[:1]),
                negative.replace('Tactic `rfl` failed:','unexpected failure',1)]:
 try:validate_negative(corrupt)
 except AssertionError:pass
 else:raise AssertionError('corrupted negative evidence accepted')
(p/'controls-checked-map.json').write_text(json.dumps(mapping,indent=2)+'\n')

source=(p/'Catalog-proposed-v2.lean.txt').read_text()
seal=json.loads((p/'seal-v2.json').read_text());guarded=(p/'Catalog-sealed-v2.lean.txt').read_text()
for piece in seal['inserted_pieces']:
 assert guarded.count(piece)==1
 guarded=guarded.replace(piece,'',1)
assert guarded==source
assert seal['definitions']==45 and seal['defaults_removed']==3 and seal['before_each_doc_and_header']
log=(p/'complete-sealed-v2.out').read_text()
assert 'sorryAx' not in log
assert "Turing.catalog_ofWords_with_tapes' depends on axioms: [propext, Quot.sound]" in log
for name in ['transfer','copy']:
 assert "'Turing.Cfg.ofWords_"+name+"_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]" in log

# Exact byte reconstruction is stronger than only comparing parsed headers.
code=(root/'devtools/seyoon/declfreeze.py').read_text();ns={}
exec(compile(code.split('a = chunks(')[0],'<reviewed-freeze-parser>','exec'),ns)
A={n:t for n,_,t in ns['chunks']((p/'Catalog-before.lean.txt').read_text())}
B={n:t for n,_,t in ns['chunks'](source)}
restored=source.replace(B['Turing.catalog_ofWords_with_tapes']+'\n\n','',1)
for name in ['Turing.Cfg.ofWords_transfer_endpoint','Turing.Cfg.ofWords_copy_endpoint']:
 assert restored.count(B[name])==1
 restored=restored.replace(B[name],A[name],1)
assert restored==(p/'Catalog-before.lean.txt').read_text()

inputs=json.loads((p/'inputs.json').read_text())
snapshot=Path(inputs['snapshot'])
assert all(sha(snapshot/(m+'.olean'))==h for m,h in inputs['snapshot_hashes'].items())
actual=Path(inputs['actual_catalog'])
assert sha(actual)==inputs['actual_catalog_sha256']
screen=root/'campaign/fills/mig1/landing/screen-current25-draft'
for line in (screen/'SHA256SUMS').read_text().splitlines():
 h,name=line.split('  ',1);assert sha(screen/name)==h
assert len((screen/'SHA256SUMS').read_text().splitlines())==120
warning_regions=[]
for name in ['Turing.catalog_ofWords_with_tapes','Turing.Cfg.ofWords_transfer_endpoint','Turing.Cfg.ofWords_copy_endpoint']:
 chunk=B[name];start=source.index(chunk);first=source.count('\n',0,start)+1
 warning_regions.append({'name':name,'first_line':first,'last_line':first+chunk.count('\n')})
warnings=[]
for match in re.finditer(r'^.*:(\d+):(\d+): warning: (.*)$',(p/'complete-native-v2.out').read_text(),re.M):
 line=int(match[1]);affected=any(r['first_line']<=line<=r['last_line'] for r in warning_regions)
 warnings.append({'line':line,'column':int(match[2]),'message':match[3],'in_three_affected_declarations':affected})
assert len(warnings)==28 and not any(r['in_three_affected_declarations'] for r in warnings)
(p/'warnings.json').write_text(json.dumps({'target_regions':warning_regions,'warnings':warnings},indent=2)+'\n')
line_of=lambda text,name:text[:text.index('theorem '+name)].count('\n')+1
pointer={'referenced_row':'Turing.FinTM.computesFunInTime_lengthBits_spaceUsed',
         'lengthBits_row_before_line':line_of((p/'Catalog-before.lean.txt').read_text(),'computesFunInTime_lengthBits_spaceUsed'),
         'lengthBits_row_proposed_line':line_of(source,'computesFunInTime_lengthBits_spaceUsed'),
         'actual_WordSize_edited':False,'parent_refreshes_pointer_after_all_adoptions':True}
(p/'line-pointer-note.json').write_text(json.dumps(pointer,indent=2)+'\n')
result={'actual_lean_invocations':len(labels),'receipts':receipts,
 'full_exact_native_proposal_passed':True,'three_before_header_doc_seals_45defs_defaults3_passed':True,
 'controls_source_reused_verbatim_but_execution_fresh_current2':True,
 'unsealed_examples_passed':90,'sealed_exact_line_mapped_rfl_failures':90,
 'negative_validator_rejects_three_corrupt_variants':True,
 'exact_proposal_undo_restores_all_original_source_bytes':True,
 'actual_catalog_unchanged':True,'watched_snapshot_oleans_unchanged':True,
 'raw_screen_120_entry_manifest_untouched':True,'native_warning_count':len(warnings),'new_region_warning_count':0,
 'proposal_sha256':sha(p/'Catalog-proposed-v2.lean.txt'),'patch_sha256':sha(p/'proposal-v2.diff'),
 'scope':'One private proof helper plus two body repoints; not adopted, no replay/screen/global seal/API/hold closure claimed.'}
(p/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2));print(json.dumps(pointer,indent=2))
