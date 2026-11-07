"""Static contract, move, seal-coverage and log checks; no delivered code runs."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
REPO=OUT.parents[4]
ROOT=OUT/'cp05/fill-mig1-mega-cp05'
spec=importlib.util.spec_from_file_location('independent_compare',OUT/'compare.py')
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
F='TCSlib/Complexity/TuringMachine/Build/Primitives.lean'
comparison=json.loads((OUT/'source-comparison.json').read_text())


def rename(code):
    code=re.sub(r'\ba2_MapState\b','FwdMapState',code)
    code=re.sub(r'\ba2_map([\w\']*)',r'fwdMap\1',code)
    code=re.sub(r'\bf2_poly([\w\']*)',r'poly\1',code)
    code=re.sub(r'\bf2_(CatalogPolyControl|catalogPoly[\w\']*)',r'\1',code)
    return mod.norm(code)


def main():
    src=(ROOT/'source'/(F+'.txt')).read_text()
    decls=mod.decls(src);byname={d['name']:d for d in decls}
    contract=mod.decls((REPO/'campaign/fills/mig1/inputs/forwarding-map-contract.lean.txt').read_text())
    assert len(contract)==3
    checks=[]
    for d in contract:
        actual=byname[d['name']]
        assert actual['header']==d['header'],d['name']
        if d['kind']=='def':assert mod.norm(actual['code'])==mod.norm(d['code'])
        assert not re.search(r'\bsorry\b',actual['code'])
        checks.append(dict(name=d['name'],header_identical=True,line=actual['start'],
                           definition_body_identical=True if d['kind']=='def' else None))
    catalog=(ROOT/'source/TCSlib/Complexity/TuringMachine/Build/Catalog.lean.txt').read_text()
    old={d['name']:d for d in mod.decls(catalog)}
    r=comparison['progression'][F]
    moves=[];changed_moves=[]
    for name in r['private_added']:
        short=name.rsplit('.',1)[1]
        prior=('a2_MapState' if short=='FwdMapState' else short.replace('fwdMap','a2_map',1) if short.startswith('fwdMap') else 'f2_'+short)
        previous=old['Turing.FinTM.'+prior]
        same=rename(previous['code'])==mod.norm(byname[name]['code'])
        row=dict(source=previous['name'],target=name,code_identical_modulo_renaming=same,
                 source_line=previous['start'],target_line=byname[name]['start'])
        moves.append(row)
        if not same:changed_moves.append(name)
    assert len(moves)==32
    assert changed_moves==['Turing.FinTM.poly_space','Turing.FinTM.fwdMap_space'],changed_moves
    assert all(row['code_identical_modulo_renaming'] for row in moves if byname[row['target']]['kind'] in ('def','inductive','instance'))
    sealed=(ROOT/'evidence/seal/Seal_Primitives.lean.txt').read_text()
    restored=re.sub(r'^section MIG1Seal\d+\nattribute \[local irreducible\] [^\n]+\n(?:attribute \[-simp\] [^\n]+\n)?','',sealed,flags=re.M)
    restored=re.sub(r'^end MIG1Seal\d+\n?','',restored,flags=re.M)
    assert mod.norm(mod.clean(src))==mod.norm(mod.clean(restored))
    gen=(ROOT/'evidence/seal/Seal_Primitives.gen').read_text()
    actual=gen.rstrip().split(' declarations: ',1)[1].split(', ')
    expected=set(r['public_added'])|{d['name'] for d in r['public_proof_changes']}|set(r['private_added'])
    assert len(actual)==len(set(actual))==len(expected)==42 and set(actual)==expected
    assert len(re.findall(r'^section MIG1Seal\d+$',sealed,re.M))==42
    attrs=sorted(set(re.findall(r'^attribute \[local irreducible\] (.+)$',sealed,re.M)))
    assert all('Turing.pairEncode' not in a.split() and 'Turing.pairDecode' not in a.split() for a in attrs)
    raw=(ROOT/'evidence/seal/Seal_Primitives.out').read_text()
    assert raw.rstrip().endswith('exit=1')
    errors=list(re.finditer(r'^([^\n]+?):(\d+):(\d+): error: ([^\n]+)',raw,re.M))
    assert len(errors)==18
    sd=mod.decls(sealed)
    diag=[]
    for e in errors:
        line=int(e[2]);owner=next(d for d in sd if d['start']<=line<=d['end'])
        assert owner['private']
        diag.append(dict(sealed_line=line,owner=owner['name'],message=e[4]))
    rawax=(ROOT/'evidence/logs/axioms/Ax_fb.out').read_text()
    entries=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",rawax,re.M)
    pub={d['name'] for d in r['public_proof_changes']}|{d['name'] for d in contract if d['kind'] in ('theorem','lemma')}
    assert pub<={n for n,a in entries} and len(entries)==17
    assert all(set(a.split(', '))=={'propext','Classical.choice','Quot.sound'} for n,a in entries)
    assert rawax.rstrip().endswith('exit=0')
    assert all(not byname[n]['private'] for n,a in entries)
    tail=(ROOT/'evidence/logs/tail-fb/summary.log').read_text()
    modules=[l for l in tail.splitlines() if re.match(r'TCSlib/.* start=',l)]
    assert len(modules)==35 and all('exit=0 errors=0' in l for l in modules) and 'failed=0' in tail
    prior=OUT.parent/'checkpoint03-2026-11-07/cp03/fill-mig1-mega-cp03'
    controlfiles=['ControlsSealed.lean.txt','ControlsSealed.out','ControlsUnsealed.lean.txt','ControlsUnsealed.out',
                  'neg-duplicate.out','neg-missing.out','neg-exit0.out']
    assert all((prior/'evidence/seal/controls'/n).read_bytes()==(ROOT/'evidence/seal/controls'/n).read_bytes() for n in controlfiles)
    additions=[l for l in (OUT/'cp03-to-cp05-source.diff').read_text().splitlines() if l.startswith('+') and not l.startswith('+++')]
    suspect=[l for l in additions if re.search(r'\b(unsafe|axiom|opaque|elab|run_tac|initialize|sorry|sorryAx|admit|native_decide|implemented_by)\b|^\+(?:#|attribute |set_option)',l)]
    assert not suspect
    out=dict(limitation='Source/log data inspection only; no fresh elaboration or payload execution.',
             forwarding_contracts=checks,private_moves=moves,non_verbatim_moves=changed_moves,
             seal=dict(expected_regions=42,supplied_regions=42,code_restores_exactly=True,
                       irreducible_sets=attrs,supplied_exit=1,errors=diag,
                       omitted_reached_foreign_definitions=['Turing.pairEncode','Turing.pairDecode']),
             axioms=dict(names=17,new_or_changed_public_proofs=len(pub),all_covered=True,
                         additional_unchanged_names=sorted({n for n,a in entries}-pub),only_standard_axioms=True),
             bootstrap_tail=dict(modules=35,all_recorded_exit_zero=True),
             paired_controls='Byte-identical to reviewed cp03/cp02; no pairEncode/pairDecode controls.',
             additional_explicit_definition_arguments={
                 'Turing.pairEncode':[3034,3474],
                 'Turing.pairDecode':[3060,3076,3089,3094,3100,3107],
                 'Mathlib SignType.cast':[2272,2274,2289,2313,2315,2329,2331,2344,2347,2352,2361]},
             primitives_argument_scan_artifact='No Primitives argument-scan output is present; these findings are independent source inspection.',
             fresh_elaboration_summaries={p.name:p.read_text().strip() for p in sorted((ROOT/'evidence/logs/elab').glob('fb*.summary'))},
             new_source_execution_or_bypass_candidates=suspect)
    (OUT/'evidence-check.json').write_text(json.dumps(out,indent=2)+'\n')
    for k in ['forwarding_contracts','non_verbatim_moves','axioms','bootstrap_tail']:print(k,json.dumps(out[k]))
    print('seal errors',len(diag),'regions',len(actual),'owners',sorted({d['owner'] for d in diag}))


if __name__=='__main__':main()
