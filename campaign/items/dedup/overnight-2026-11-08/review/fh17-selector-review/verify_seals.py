from pathlib import Path
import json,re,hashlib,collections
O=Path(__file__).parent
T=json.loads((O/'TASK.json').read_text())
W=Path(T['source_worktree'])
inputs=json.loads((O/'SEAL-INPUTS-v3.json').read_text())
results=json.loads((O/'SEAL-RESULTS-v3.json').read_text())
I={(r['label'],r['kind']):r for r in inputs}
R={(r['label'],r['kind']):r for r in results}
sha=lambda b:hashlib.sha256(b).hexdigest()
scopes=[]
controls=[]
for label in sorted({r['label'] for r in inputs}):
    d=I[label,'full_target_scopes']
    actual=R[label,'full_target_scopes']
    assert actual['exit']==0 and actual['errors']==0 and actual['sorry_warnings']==0
    text=(O/d['input_evidence']).read_text()
    assert sha(text.encode())==d['input_sha256']==actual['input_sha256']
    assert sha((O/actual['output_file']).read_bytes())==actual['output_sha256']
    recovered=text
    for idx in d['targets']:
        pre='section FH1Seal_'+str(idx)+'\nattribute [local irreducible] '+' '.join(d['guards'])+'\n'
        post='end FH1Seal_'+str(idx)+'\n'
        assert recovered.count(pre)==recovered.count(post)==1
        recovered=recovered.replace(pre,'').replace(post,'')
    assert recovered==(W/d['path']).read_text()
    scopes.append({'label':label,'path':d['path'],'targets':d['targets'],'guards':d['guards'],'guard_applications':d['guard_applications'],'complete_docstring_header_body_and_scoped_open':True,'whole_final_source_roundtrip_exact':True,'exact_actual_input_and_output_hashes':True,'exit':0,'errors':0,'actual_input_reuse':actual['reused_actual_prior_input_code_exact'],'actual_source':actual['input_evidence'],'final_source':d['input_evidence']})
    nd=I[label,'controls_native']; sd=I[label,'controls_sealed']
    nr=R[label,'controls_native']; sr=R[label,'controls_sealed']
    native=(O/nd['input_evidence']).read_text(); sealed=(O/sd['input_evidence']).read_text()
    attr='attribute [local irreducible] '+' '.join(sd['guards'])+'\n'
    assert sealed.count(attr)==1 and sealed.replace(attr,'')==native
    assert sha(native.encode())==nd['input_sha256']==nr['input_sha256']
    assert sha(sealed.encode())==sd['input_sha256']==sr['input_sha256']
    nraw=(O/nr['output_file']).read_text(); sraw=(O/sr['output_file']).read_text()
    assert sha(nraw.encode())==nr['output_sha256'] and sha(sraw.encode())==sr['output_sha256']
    identities=nd['identities']
    names=re.findall(r'^theorem (\S+) ',native,re.M)
    assert len(names)==identities and all(n in nraw for n in names)
    assert nr['exit']==0 and nr['errors']==0 and nr['sorry_warnings']==0
    expected=[i for i,line in enumerate(sealed.splitlines(),1) if ':= by rfl' in line]
    actual_lines=[int(x) for x in re.findall(r'\.lean:(\d+):\d+: error(?:\([^\n]*?\))?:',sraw)]
    assert len(expected)==identities and expected==actual_lines,(label,expected,actual_lines)
    assert sr['exit']!=0 and sr['errors']==identities and sraw.count('rfl')>=identities
    controls.append({'context':label,'guards':sd['guards'],'paired_identities':identities,'positive_kernel_checked_named_declarations':names,'native_exit':nr['exit'],'native_errors':nr['errors'],'negative_exit':sr['exit'],'negative_errors':sr['errors'],'exact_negative_rfl_source_goal_lines':expected,'literal_source_pair_after_single_guard_line_removal':True,'actual_input_SHA_correspondence':True})
res={'PASS':True,'full_target_declarations':sum(len(r['targets']) for r in scopes),'owner_import_contexts':len(scopes),'guard_applications':sum(r['guard_applications'] for r in scopes),'paired_identities':sum(r['paired_identities'] for r in controls),'all_full_scopes_exit0_errors0':True,'all_positive_controls_kernel_error_free':True,'all_negative_errors_exact_matching_rfl_goal_lines':True,'no_failed_input_counted_as_pass':True,'named_guard_scope_only_not_all_foreign_definition_closure':True,'scopes':scopes,'controls':controls}
(O/'SEAL-VERIFICATION.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:v for k,v in res.items() if k not in ['scopes','controls']},indent=2))
