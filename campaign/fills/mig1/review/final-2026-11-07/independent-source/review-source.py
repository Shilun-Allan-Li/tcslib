"""Independent read-only final source/freeze and saved-screen review. No payload tool execution."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import sys
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[5]
REVIEW=OUT.parent
DELIVERY=REVIEW/'extracted/fill-mig1-mega'
CP07=REVIEW.parent/'checkpoint07-2026-11-07'
FILES=(ROOT/'campaign/fills/mig1/inputs/owned-files.txt').read_text().splitlines()
PARSER=ROOT/'campaign/gates/106-sg1-dedup/review/round2-current/source_tools.py'
spec=importlib.util.spec_from_file_location('source_tools',PARSER)
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
def sha(data):return hashlib.sha256(data).hexdigest()
def save(name,obj):(OUT/name).write_text(json.dumps(obj,indent=2)+'\n')
def pairs(path):
    text=path.read_text()
    h=re.match(r'declarations screened: (\d+); copy pairs \(target reproduces >= half of source\): (\d+); reproduced text: ([\d,]+) chars',text)
    assert h,path
    rows=[dict(target=m[1],source=m[2],common=int(m[3]),source_length=int(m[4]),percent=int(m[5])) for m in re.finditer(r'^\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%$',text,re.M)]
    edges={(r['target'],r['source']):r for r in rows}
    assert len(rows)==len(edges)==int(h[2])
    assert sum(r['common'] for r in rows)==int(h[3].replace(',',''))
    return dict(declarations=int(h[1]),pairs=int(h[2]),characters=int(h[3].replace(',',''))),edges

def main():
    git_receipt=REVIEW.parent/'checkpoint07-git-objects/receipt.json'
    g=json.loads(git_receipt.read_text());gm={r['path']:r for r in g['source_population']}
    assert g['git_bundle_verify_exit']==0 and g['all_eleven_snapshots_equal_git_blobs']
    assert (DELIVERY/'HEAD.txt').read_text().strip()==g['head']=='cbfdba8102e6a5d956a1fdd2be7518b490a5abac'
    assert (DELIVERY/'BASE.txt').read_text().strip()==g['base']=='83ac315ed9e7089466bd16a32f3b71fbadc556d2'
    inventory=[];versions={};comparisons={}
    for file in FILES:
        data=(DELIVERY/'source'/(file+'.txt')).read_bytes()
        prior=(CP07/'extracted/fill-mig1-mega-cp07/source'/(file+'.txt')).read_bytes()
        base=(CP07/'base-source'/(file+'.txt')).read_text()
        assert data==prior
        assert sha(data)==gm[file]['sha256'] and len(data)==gm[file]['bytes']
        blob=hashlib.sha1(('blob '+str(len(data))+'\0').encode()+data).hexdigest()
        assert blob==gm[file]['git_blob']
        inventory.append(dict(path=file,bytes=len(data),sha256=sha(data),git_blob_sha1=blob,identical_to_cp07=True,identical_to_prior_actual_git_object_receipt=True))
        text=data.decode();versions[file]=(base,text);r=s.compare(base,text)
        assert not any(r[k] for k in ['visibility_changes','public_header_changes','public_definition_changes'])
        assert r['public_order_unchanged']
        allowed_add=['Turing.FinTM.pairMapSndTM','Turing.FinTM.pairMapSndTM_computes','Turing.FinTM.pairMapSndTM_spaceUsed'] if file.endswith('/Primitives.lean') else []
        allowed_del=['Turing.transferTM_run','Turing.copyTM_run','Turing.clearTM_run','Turing.compareTM_run','Turing.incrementTM_run_succ','Turing.incrementTM_run_overflow'] if file.endswith('/Catalog.lean') else []
        assert r['public_added']==allowed_add and r['public_removed']==allowed_del
        additions=[i for i in r['imports_after'] if i not in r['imports_before']]
        expected=['import Mathlib.Algebra.BigOperators.Fin'] if file.endswith('/Simulation.lean') else ['import TCSlib.Complexity.TuringMachine.Build.Primitives'] if file.endswith('/Catalog.lean') else []
        assert additions==expected and all(i in r['imports_after'] for i in r['imports_before'])
        comparisons[file]=r
    assert len(inventory)==11 and sum(r['public_counts'][0] for r in comparisons.values())==357 and sum(r['public_counts'][1] for r in comparisons.values())==354
    targets=[]
    for t in json.loads((ROOT/'campaign/fills/mig1/inputs/target-admissions.json').read_text()):
        base,final=versions[t['path']]
        a,b=({d['name']:d for d in s.decls(v)}[t['name']] for v in [base,final])
        assert a['header']==b['header'] and re.search(r'\bsorry\b',a['code']) and not re.search(r'\b(?:sorry|admit)\b',b['code'])
        targets.append(dict(name=t['name'],path=t['path'],line=b['start'],complete_header_unchanged=True,source_proof_filled=True))
    assert len(targets)==17
    source_admissions=[dict(path=f,**a) for f,r in comparisons.items() for a in r['admissions']]
    assert [a['name'] for a in source_admissions]==['WordRAM.WordSizeComputable.mono','WordRAM.wordSizeComputable_logSpace','WordRAM.wordSizeComputable_of_spaceConstructible']
    forwarding=s.decls((ROOT/'campaign/fills/mig1/inputs/forwarding-map-contract.lean.txt').read_text())
    primitive=versions['TCSlib/Complexity/TuringMachine/Build/Primitives.lean'][1]
    pm={d['name']:d for d in s.decls(primitive)}
    forward_results=[]
    for d in forwarding:
        a=pm[d['name']]
        assert d['header']==a['header']
        if a['kind']=='def':assert s.norm(d['code'])==s.norm(a['code'])
        else:assert not re.search(r'\b(?:sorry|admit)\b',a['code'])
        forward_results.append(dict(name=a['name'],line=a['start'],header_matches_gate=True,definition_matches_gate=(True if a['kind']=='def' else None),source_proof_filled=(True if a['kind']!='def' else None)))
    catalog=versions['TCSlib/Complexity/TuringMachine/Build/Catalog.lean'][1]
    removed=[n for r in comparisons.values() for n in r['public_removed']]
    retired_hits=[]
    for file,(base,text) in versions.items():
        for name in removed:
            if re.search(r'(?<![A-Za-z0-9_])'+re.escape(name.split('.')[-1])+r'(?![A-Za-z0-9_])',s.clean(text)):
                retired_hits.append((file,name))
    assert not retired_hits
    word='TCSlib/Complexity/RAMSimulation/WordSize.lean'
    assert s.clean(versions[word][0])==s.clean(versions[word][1])
    record=dict(base=g['base'],head=g['head'],scope='Independent source/headers/tables and saved-screen consistency only; no Git/Lean/screen or delivered scripts executed.',
        parser_path=str(PARSER.relative_to(ROOT)),parser_sha256=sha(PARSER.read_bytes()),
        prior_git_object_receipt=str(git_receipt.relative_to(ROOT)),prior_git_object_receipt_sha256=sha(git_receipt.read_bytes()),
        git_object_check_attribution='Root maintainer previously verified cp07 actual Git objects; this review independently matches all final source bytes and recomputed blob hashes to that immutable receipt.',
        inventory=inventory,source_freeze=comparisons,source_public_before_after=[357,354],existing_public_proof_changes=sum(len(r['public_proof_changes']) for r in comparisons.values()),targets=targets,forwarding=forward_results,remaining_source_admissions=source_admissions,retired_names_absent_in_all_eleven_snapshots=True,wordsize_code_unchanged=True)
    save('source-freeze.json',record)
    screens=DELIVERY/'evidence/screens'
    population=(screens/'screen-population.txt').read_text().splitlines()
    assert population==(ROOT/'campaign/fills/mig1/inputs/screen-population.txt').read_text().splitlines() and len(population)==16
    base_meta,base_pairs=pairs(screens/'screen-base.txt');head_meta,head_pairs=pairs(screens/'screen-final.txt')
    new={k:v for k,v in head_pairs.items() if k not in base_pairs};gone={k:v for k,v in base_pairs.items() if k not in head_pairs}
    assert base_meta==dict(declarations=1279,pairs=1589,characters=636810)
    assert head_meta==dict(declarations=1002,pairs=627,characters=210586)
    assert len(new)==95 and len(gone)==1057
    classified=(screens/'new-pairs-classified.txt').read_text()
    moved=[]
    for m in re.finditer(r'^MOVED (\S+) ~ (\S+) \(base: (\S+) ~ (\S+)\) (\d+)/(\d+)$',classified,re.M):
        target,source,oldtarget,oldsource=m.groups()[:4]
        assert (target,source) in new and (oldtarget,oldsource) in base_pairs
        assert new[target,source]['common']==int(m[5]) and new[target,source]['source_length']==int(m[6])
        moved.append(dict(target=target,source=source,baseline_target=oldtarget,baseline_source=oldsource))
    fresh=[]
    for m in re.finditer(r'^NEW  (\S+) reproduces (\S+): (\d+)/(\d+) = (\d+)%$',classified,re.M):
        key=m[1],m[2]
        assert key in new and new[key]['common']==int(m[3]) and new[key]['source_length']==int(m[4]) and new[key]['percent']==int(m[5])
        fresh.append(new[key])
    assert len(moved)==50 and len(fresh)==45 and len({(r['target'],r['source']) for r in moved+fresh})==95
    save('saved-screen-crosscheck.json',dict(base=base_meta,head=head_meta,head_only=95,base_only=1057,moved_labels_consistent=50,new_labels_consistent=45,population=population,raw_headers_and_edge_sums_consistent=True,raw_inputs_not_reexecuted=True,moved=moved,fresh=fresh,
        limitation='Moved-label membership and numeric consistency are checked here. Semantic review and residual factoring obligations are in REVIEW.md; short text length is not an exemption.'))
    q=[]
    requests={
        'TCSlib/Complexity/TuringMachine/Build/Primitives.lean':['catalogRewind','extract_replay','rawStrip_replay','emitter_first_entry','emitterP2_body_erase_left','emitterP2_body_erase_right','lenParse_first','lenSuffix_run','emitterToken_double','emitterToken_separator'],
        'TCSlib/Complexity/TuringMachine/Build/Loop.lean':['emCall_first_entry','emCall_bank_initial','emCall_bank_final'],
        'TCSlib/Complexity/TuringMachine/Build/Catalog.lean':['copyMapTM','transferMapTM','Cfg.ofWords_copy_endpoint','Cfg.ofWords_transfer_endpoint','incrementTM_run_succ_ofCfg','incrementTM_run_overflow_ofCfg']}
    for file,names in requests.items():
        text=versions[file][1];dm={d['name']:d for d in s.decls(text)}
        for short in names:
            found=[d for n,d in dm.items() if n.endswith('.'+short)]
            assert len(found)==1,(file,short)
            d=found[0];last=d['start']-1+max(i+1 for i,line in enumerate(d['code'].splitlines()) if line.strip())
            raw=''.join(text.splitlines(keepends=True)[d['start']-1:last])
            q.append('## '+file+':'+str(d['start'])+' — '+d['name']+'\n\n```lean\n'+raw+'```\n')
    (OUT/'source-quotes.md').write_text('# Relevant final-source quotations (data only)\n\n'+'\n'.join(q))
    print(json.dumps(dict(all_eleven_final_sources_equal_cp07_and_verified_object_receipt=True,public_before_after=[357,354],targets_source_filled=len(targets),forwarding_declarations=len(forward_results),residual_source_admissions=source_admissions,public_proof_changes=record['existing_public_proof_changes'],screens=dict(base=base_meta,head=head_meta,new=95,moved_labels=50,other_labels=45)),indent=2))

if __name__=='__main__':main()
