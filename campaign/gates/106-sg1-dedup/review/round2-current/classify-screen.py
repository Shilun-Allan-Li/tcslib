"""Offline fresh-screen parsing and current-versus-historical candidate accounting."""
from pathlib import Path
import hashlib
import json
import re
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
GATE=ROOT/'campaign/gates/106-sg1-dedup'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,obj):(OUT/n).write_text(json.dumps(obj,indent=2)+'\n')
def parse(path):
    text=path.read_text()
    header=re.match(r'declarations screened: (\d+); copy pairs \(target reproduces >= half of source\): (\d+); reproduced text: ([\d,]+) chars',text)
    assert header,path
    matches=list(re.finditer(r'^\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%$',text,re.M))
    pairs={(m[1],m[2]):dict(target=m[1],source=m[2],common=int(m[3]),source_length=int(m[4]),percent=int(m[5])) for m in matches}
    assert len(matches)==len(pairs)==int(header[2])
    assert sum(r['common'] for r in pairs.values())==int(header[3].replace(',',''))
    return dict(declarations=int(header[1]),pairs=int(header[2]),characters=int(header[3].replace(',',''))),pairs
def compare(a,b):
    return dict(new=[b[k] for k in sorted(b.keys()-a.keys())],gone=[a[k] for k in sorted(a.keys()-b.keys())],retained=len(a.keys()&b.keys()),metric_changed=[dict(before=a[k],after=b[k]) for k in sorted(a.keys()&b.keys()) if a[k]!=b[k]])

def main():
    current={};meta={};receipts={}
    for label in ['base','head']:
        path=OUT/'screen'/(label+'.txt')
        meta[label],current[label]=parse(path)
        r=json.loads((OUT/'screen'/(label+'-run.json')).read_text())
        assert r['exit']==0 and sha(path)==r['output_sha256']
        assert (OUT/'screen'/(label+'.stderr.txt')).read_text()==''
        assert r['population']==(OUT/'population.txt').read_text().splitlines()
        assert sha(ROOT/'scripts/copy-text-screen-v3.py')==r['screen_script_sha256']
        receipts[label]=dict(seconds=r['seconds'],output_sha256=r['output_sha256'],start_utc=r['start_utc'],shared_screen_lock=r['shared_screen_lock'])
    old_meta,old_head=parse(GATE/'evidence/current/screen/screen-head.txt')
    old_base_meta,old_base=parse(GATE/'evidence/current/screen/screen-base.txt')
    delta=compare(current['base'],current['head'])
    historical=compare(old_head,current['head'])
    result=dict(population=receipts and (OUT/'population.txt').read_text().splitlines(),fresh=meta,actual_screen_receipts=receipts,current_base_to_head=delta,
        original_audited_head=old_meta,original_audited_head_to_current_head=historical,
        original_base_to_current_base=compare(old_base,current['base']),
        all_raw_headers_edge_counts_and_character_sums_match=True,
        limitation='Candidate enumeration, not an exhaustive semantic theorem or debt census. Per-edge source classification is separate.')
    save('screen-delta.json',result)
    family=json.loads((GATE/'review-incoming/2026-11-07-sg1-f6263c50/family-accounting.json').read_text())
    old_labels={(r['target'],r['source']):r for r in family['directed_candidates_classified']}
    sat_hard=[]
    for key,r in current['head'].items():
        if {x.split('::')[0] for x in key}!={'SAT.lean','Hardness.lean'}:continue
        old=old_labels.get(key)
        status=old['family_classification'] if old else 'NEW CANDIDATE — inspect source before disposition'
        if any(n.endswith(('::sat_guard_add','::clA5_guard_add')) for n in key):
            status='F1 repaired: exact existing private adapters now construct/read public Segment premises and call Segment.trans; no time-splitting composition proof remains.'
        elif status.startswith('F2 five exact'):
            status='Five generic adapter kinds acknowledged by Seyoon, including companion proofs; repeated edges count each declaration once.'
        elif status.startswith('additional finite-family'):
            status='Separate finite-family shared-bank dispatcher kind acknowledged by Seyoon; concrete HostNext tables remain client data.'
        sat_hard.append(dict(**r,current_disposition=status,historical_edge_present=old is not None))
    save('current-sat-hardness-candidates.json',dict(count=len(sat_hard),historical_classified_edges=86,current_edges=sat_hard,
        missing_historical=[old_labels[k] for k in sorted(old_labels.keys()-{(r['target'],r['source']) for r in sat_hard})],
        count_is_directional_candidate_edges_not_debt_members=True,
        known_named_lower_bounds=dict(SAT='34/270',Hardness='32/544'),
        watches_and_wider_semantic_candidates_not_upgraded_to_acknowledgment=True))
    print(json.dumps(dict(fresh=meta,new=delta['new'],gone=delta['gone'],retained=delta['retained'],metric_changes=delta['metric_changed'],historical_new=historical['new'],historical_gone=historical['gone'],current_sat_hardness_edges=len(sat_hard)),indent=2))

if __name__=='__main__':main()
