"""Parse checkpoint evidence as data only. No Lean and no delivered tools run."""
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True

OUT=Path(__file__).resolve().parent
ROOT=OUT/'cp02'/'fill-mig1-mega-cp02'
spec=importlib.util.spec_from_file_location('independent_compare',OUT/'compare.py')
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
source_check=json.loads((OUT/'source-comparison.json').read_text())


def controls(name, source, expect):
    lines=source.read_text().splitlines()
    starts=[i+1 for i,l in enumerate(lines) if l.startswith('example ')]
    assert len(starts)==38
    ends=starts[1:]+[len(lines)+1]
    raw=(ROOT/'evidence/seal/controls'/name).read_text()
    diagnostics=list(re.finditer(r'^([^\n]+?):(\d+):(\d+): error: ([^\n]+)',raw,re.M))
    counts=Counter();stray=[];wrong_kind=[];wrong_file=[]
    for match in diagnostics:
        line=int(match[2])
        block=next((s for s,e in zip(starts,ends) if s<=line<e),None)
        if block is None:stray.append(line)
        else:counts[block]+=1
        if match[4] != 'Tactic `rfl` failed: The left-hand side':wrong_kind.append(match[4])
        if not match[1].endswith('ControlsSealed.lean'):wrong_file.append(match[1])
    exits=re.findall(r'^exit=(\d+)\s*$',raw,re.M)
    want=1 if expect=='fail' else 0
    bad=[dict(line=s,count=counts[s]) for s in starts if counts[s]!=want]
    accepted=(len(exits)==1 and (int(exits[0])!=0 if want else int(exits[0])==0)
              and not (stray or bad or wrong_kind or wrong_file))
    return dict(examples=len(starts),diagnostics=len(diagnostics),exit=exits,
                bad_examples=bad,stray=stray,unexpected_diagnostic_kind=wrong_kind,
                unexpected_diagnostic_file=wrong_file,accepted=accepted)


def main():
    out={'limitation':'Static parsing of delivered source/logs; not an independent elaboration.'}
    ctl=ROOT/'evidence/seal/controls'
    sealed=ctl/'ControlsSealed.lean.txt';unsealed=ctl/'ControlsUnsealed.lean.txt'
    out['controls']={
        'unsealed':controls('ControlsUnsealed.out',unsealed,'pass'),
        'sealed':controls('ControlsSealed.out',sealed,'fail'),
        'duplicate_negative':controls('neg-duplicate.out',sealed,'fail'),
        'missing_negative':controls('neg-missing.out',sealed,'fail'),
        'exit0_negative':controls('neg-exit0.out',sealed,'fail')}
    assert out['controls']['unsealed']['accepted']
    assert out['controls']['sealed']['accepted']
    assert all(not out['controls'][x]['accepted'] for x in ('duplicate_negative','missing_negative','exit0_negative'))
    u=unsealed.read_text();s=sealed.read_text()
    declarations='\n'.join(l for l in s.splitlines() if not l.startswith('attribute '))+'\n'
    assert declarations==u
    labels=re.findall(r'^-- C(\d+) (.+)',u,re.M)
    assert [int(n) for n,_ in labels]==list(range(1,20))
    out['control_pairs']=labels
    out['seal_regions']={}
    for home,f in [('Composition','TCSlib/Complexity/TuringMachine/Composition.lean'),
                   ('Encoding','TCSlib/Complexity/TuringMachine/Encoding.lean'),
                   ('TimeConstructible','TCSlib/Complexity/ClassP/TimeConstructible.lean'),
                   ('Simulation','TCSlib/Complexity/TuringMachine/Simulation.lean'),
                   ('Wrappers','TCSlib/Complexity/TuringMachine/Build/Wrappers.lean')]:
        src=(ROOT/'source'/(f+'.txt')).read_text()
        seal=(ROOT/'evidence/seal'/('Seal_'+home+'.lean.txt')).read_text()
        attrs=re.findall(r'^attribute \[local irreducible\] (.+)$',seal,re.M)
        wrappers=re.findall(r'^section MIG1Seal(\d+)$',seal,re.M)
        ends=re.findall(r'^end MIG1Seal(\d+)$',seal,re.M)
        assert len(attrs)==len(wrappers) and Counter(wrappers)==Counter(ends)
        restored=re.sub(r'^section MIG1Seal\d+\nattribute \[local irreducible\] [^\n]+\n(?:attribute \[-simp\] [^\n]+\n)?','',seal,flags=re.M)
        restored=re.sub(r'^end MIG1Seal\d+\n?','',restored,flags=re.M)
        assert mod.norm(mod.clean(src))==mod.norm(mod.clean(restored)),home
        expected=source_check['checkpoints']['cp02'][f]
        names=[d['name'] for d in expected['public_proof_changes']]+expected['private_added']+[d['name'] for d in expected['private_changed']]
        gen=(ROOT/'evidence/seal'/('Seal_'+home+'.gen')).read_text()
        listed=gen.rstrip().split(' declarations: ',1)[1].split(', ')
        assert Counter(names)==Counter(listed),(home,names,listed)
        assert len(names)==len(wrappers)
        if home in ('Composition','Wrappers'):
            assert all('Turing.FinTM.branchTM' not in a.split() and 'Turing.FinTM.leftCfg' not in a.split() and 'Turing.FinTM.rightCfg' not in a.split() for a in attrs)
        out['seal_regions'][home]=dict(regions=len(names),names=names,
            irreducible_sets=sorted(set(attrs)),
            nosimp_sets=sorted(set(re.findall(r'^attribute \[-simp\] (.+)$',seal,re.M))),
            restored_source_code_equal=True,
            supplied_output=(ROOT/'evidence/seal'/('Seal_'+home+'.out')).read_text().strip())
    expected_axioms={d['name'] for f,r in source_check['checkpoints']['cp02'].items() for d in r['public_proof_changes']}
    raw=(ROOT/'evidence/logs/axioms/Ax_cp02.out').read_text()
    entries=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",raw,re.M)
    assert len(entries)==22
    assert {n for n,a in entries}==expected_axioms
    assert all(set(a.split(', '))=={'propext','Classical.choice','Quot.sound'} for n,a in entries)
    assert raw.rstrip().endswith('exit=0')
    out['axiom_logs']=dict(public_names=22,exactly_covers_changed_public_proofs=True,
                           only_standard_axioms_in_supplied_output=True,
                           compiler_auxiliaries_census='NOT RUN (worker disclosure)')
    # Regression against the specific nested-binder hazard in the brief.
    sample='theorem t (h : f (input := x) = y) : z := by trivial'
    assert mod.header(sample)=='theorem t (h : f (input := x) = y) : z'
    out['header_regression_nested_binder']='PASS'
    (OUT/'evidence-check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'controls':out['controls'],'seal_regions':{h:r['regions'] for h,r in out['seal_regions'].items()},'axiom_logs':out['axiom_logs']},indent=2))


if __name__=='__main__':main()
