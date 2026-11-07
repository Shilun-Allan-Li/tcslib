"""Bounded static MIG-24 dispositions; mathematical candidates are not acceptance."""
from pathlib import Path
import importlib.util
import json
import re
import sys
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[5]
source=OUT.parent/'extracted/fill-mig1-mega/source'
base=OUT.parent.parent/'checkpoint07-2026-11-07/base-source'
spec=importlib.util.spec_from_file_location('s',ROOT/'campaign/gates/106-sg1-dedup/review/round2-current/source_tools.py')
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
def declarations(home,folder=source):
    file='TCSlib/Complexity/TuringMachine/'+home+'.lean.txt'
    return {d['name'].split('.')[-1]:d for d in s.decls((folder/file).read_text())}
p=declarations('Build/Primitives');pb=declarations('Build/Primitives',base)
l=declarations('Build/Loop');lb=declarations('Build/Loop',base)
c=declarations('Build/Catalog');cb=declarations('Build/Catalog',base)
sim=declarations('Simulation')
rewind=p['catalogRewind'];canonical=sim['timed_rewind']
assert rewind['header'].split('catalogRewind',1)[1]==canonical['header'].split('timed_rewind',1)[1]
callers=[dict(name=d['name'],line=d['start']) for d in p.values() if d['name']!=rewind['name'] and re.search(r'\bcatalogRewind\b',d['code'])]
assert len(callers)==4
t2pairs=[('emitterP2_body_erase_left','emitterP2_body_erase_right'),('emitterP2_prepare_rewind_candidate','emitterP2_prepare_rewind_suffix'),('emitterP2_pair_frame','emitterP2_small_frame'),('emitterP2_left_frame','emitterP2_right_frame'),('emitterP2PairIndex','emitterP2SmallIndex'),('emitterSplit_find','splitFind_eq')]
t2=[]
for pair in t2pairs:
    members=[]
    for n in pair:
        assert s.norm(p[n]['code'])==s.norm(pb[n]['code'])
        members.append(dict(name=p[n]['name'],line=p[n]['start'],unchanged_code_from_base=True))
    t2.append(members)
first=[dict(home='Loop',name=l['emCall_first_entry']['name'],line=l['emCall_first_entry']['start']),dict(home='Primitives',name=p['emitter_first_entry']['name'],line=p['emitter_first_entry']['start'])]
assert s.norm(l['emCall_first_entry']['code'].replace('emCall_first_entry','first_entry'))==s.norm(p['emitter_first_entry']['code'].replace('emitter_first_entry','first_entry'))
t3=[]
for n in ['emCall_bank_initial','emCall_bank_final']:
    assert s.norm(l[n]['code'])==s.norm(lb[n]['code'])
    count=len(re.findall(r'by rintro ⟨r\x27, hr⟩',l[n]['code']))
    assert count==6
    t3.append(dict(name=l[n]['name'],line=l[n]['start'],repeated_nonmembership_side_proofs=count,unchanged_code_from_base=True))
assert 'emCall_pair_not_mem' not in l and 'emCall_triple_not_mem' not in l
t5=[]
for n in ['copyMapTM','transferMapTM','clearTM','Cfg.ofWords_copy_endpoint','Cfg.ofWords_transfer_endpoint','incrementTM_run_succ_ofCfg','incrementTM_run_overflow_ofCfg']:
    actual=[d for d in c.values() if d['name'].endswith('.'+n)]
    old=[d for d in cb.values() if d['name'].endswith('.'+n)]
    assert len(actual)==len(old)==1
    d,old=actual[0],old[0]
    assert s.norm(d['code'])==s.norm(old['code'])
    t5.append(dict(name=d['name'],line=d['start'],kind=d['kind'],unchanged_code_from_base=True,classification='Frozen executable table/data, distinct actions; not proof factoring.' if d['kind']=='def' else 'Retained proof material; private proof-only factoring remains assigned.'))
result=dict(T1=dict(catalogRewind_line=rewind['start'],canonical_timed_rewind_line=canonical['start'],complete_mathematical_header_equal=True,callers=callers,disposition='Routine existing public theorem reuse is available, unimplemented in delivered source.'),T2=dict(unchanged_in_file_pairs=t2,unchanged_exact_cross_file_first_entry=first,disposition='In-file private parameter factoring remains; shared first-entry interface is separately proposed and UNAPPROVED.'),T2b=dict(retired_parser_names_absent=all(n not in p for n in ['mapParse_block','mapParse_first']),replay_pair=[dict(name=p[n]['name'],line=p[n]['start']) for n in ['extract_replay','rawStrip_replay']],disposition='Replay factor remains; lenParse_first/lenSuffix_run and token-double/separator have distinct source states/actions and already share their low-level public/helper routes.'),T3=dict(members=t3,private_not_mem_helpers_present=False,total_repeated_nonmembership_side_proofs=12,disposition='Two same-home parametric private nonmembership helpers or phase factoring remain; no public API is forced by this source review.'),T5=dict(members=t5,disposition='Canonical public rows retired, but surviving endpoint/framed proof factoring remains. Keep distinct public executable table bytes frozen; no new table-rewrite exception or debt acknowledgment inferred.'),limitation='Source-only check of selected assigned families. Does not prove proposed repairs or certify complete semantic reuse/closed rule-10 boundaries.')
(OUT/'MIG24-dispositions.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
