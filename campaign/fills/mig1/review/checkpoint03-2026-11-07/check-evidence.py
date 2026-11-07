"""Independent static parsing of cp03 evidence; no delivered code is executed."""
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
ROOT=OUT/'cp03/fill-mig1-mega-cp03'
spec=importlib.util.spec_from_file_location('independent_compare',OUT/'compare.py')
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
F='TCSlib/Complexity/TuringMachine/Build/Loop.lean'
comparison=json.loads((OUT/'source-comparison.json').read_text())


def warnings(text):
    # Retain diagnostic body/multiplicity; source paths and positions necessarily shift.
    rows=re.split(r'^.*?:\d+:\d+: warning: ',text,flags=re.M)[1:]
    return Counter(x.split('\nexit=',1)[0].strip() for x in rows if not re.search(r"declaration uses ['`]sorry['`]",x))


def main():
    src=(ROOT/'source'/(F+'.txt')).read_text()
    sealed=(ROOT/'evidence/seal/Seal_Loop.lean.txt').read_text()
    restored=re.sub(r'^section MIG1Seal\d+\nattribute \[local irreducible\] [^\n]+\n(?:attribute \[-simp\] [^\n]+\n)?','',sealed,flags=re.M)
    restored=re.sub(r'^end MIG1Seal\d+\n?','',restored,flags=re.M)
    assert mod.norm(mod.clean(src))==mod.norm(mod.clean(restored))
    r=comparison['progression'][F]
    expected={d['name'] for d in r['public_proof_changes']}|set(r['private_added'])|{d['name'] for d in r['private_changed']}
    gen=(ROOT/'evidence/seal/Seal_Loop.gen').read_text()
    actual=gen.rstrip().split(' declarations: ',1)[1].split(', ')
    assert len(actual)==len(set(actual))==15
    assert len(re.findall(r'^section MIG1Seal\d+$',sealed,re.M))==15
    missing=sorted(expected-set(actual));extra=sorted(set(actual)-expected)
    assert missing==['Turing.FinTM.loopHost_input_rewind'] and not extra
    raw=(ROOT/'evidence/seal/Seal_Loop.out').read_text()
    assert raw.rstrip().endswith('exit=0')
    errors=re.findall(r'^.*?:\d+:\d+: error:',raw,re.M)
    assert not errors
    base_raw=(ROOT/'evidence/logs/bootstrap-base/raw/TCSlib.Complexity.TuringMachine.Build.Loop.out').read_text()
    b,w=warnings(base_raw),warnings(raw)
    out={'limitation':'Delivered source/log consistency only; no fresh elaboration.',
         'seal':dict(expected_changed_or_new_regions=len(expected),supplied_regions=len(actual),
                     missing_regions=missing,extra_regions=extra,code_restores_exactly=True,
                     supplied_exit=0,errors=len(errors),
                     irreducible_sets=sorted(set(re.findall(r'^attribute \[local irreducible\] (.+)$',sealed,re.M))),
                     warnings=sum(w.values()),base_non_sorry_warnings=sum(b.values()),
                     warning_multiset_equal=b==w,
                     warnings_added=list((w-b).elements()),warnings_removed=list((b-w).elements()))}
    rawax=(ROOT/'evidence/logs/axioms/Ax_fc.out').read_text()
    entries=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",rawax,re.M)
    pub={d['name'] for d in r['public_proof_changes']}
    assert {n for n,a in entries}==pub|{'Turing.FinTM.callTM_run'}
    assert len(entries)==10
    assert all(set(a.split(', '))=={'propext','Classical.choice','Quot.sound'} for n,a in entries)
    assert rawax.rstrip().endswith('exit=0')
    out['axiom_log']=dict(names=len(entries),all_nine_changed_public_proofs_covered=True,
                         additional_unchanged_name='Turing.FinTM.callTM_run',only_standard_axioms=True)
    tail=(ROOT/'evidence/logs/tail-fc/summary.log').read_text()
    modules=[l for l in tail.splitlines() if re.match(r'TCSlib/.* start=',l)]
    assert len(modules)==36 and all('exit=0 errors=0' in l for l in modules)
    assert 'failed=0' in tail
    out['bootstrap_tail']=dict(modules=len(modules),all_recorded_exit_zero=True,failed=0)
    out['fresh_elaboration_summaries']={}
    for p in sorted((ROOT/'evidence/logs/elab').glob('fc*.summary')):
        out['fresh_elaboration_summaries'][p.name]=p.read_text().strip()
    # Check that cumulative controls are exactly preserved; no reason to rerun parsers/tests.
    prior=OUT.parent/'checkpoints-2026-11-07/cp02/fill-mig1-mega-cp02/evidence/seal/controls'
    names=['ControlsSealed.lean.txt','ControlsSealed.out','ControlsUnsealed.lean.txt','ControlsUnsealed.out',
           'neg-duplicate.out','neg-missing.out','neg-exit0.out']
    same=[n for n in names if (prior/n).read_bytes()==(ROOT/'evidence/seal/controls'/n).read_bytes()]
    assert same==names
    out['paired_controls']='Byte-identical to reviewed cp02 controls/logs; no captureCfg controls added.'
    additions=[l for l in (OUT/'cp02-to-cp03-source.diff').read_text().splitlines() if l.startswith('+') and not l.startswith('+++')]
    suspect=[l for l in additions if re.search(r'\b(unsafe|axiom|opaque|elab|run_tac|initialize|sorry|sorryAx|admit|native_decide|implemented_by)\b|^\+(?:#|attribute |set_option)',l)]
    out['new_source_execution_or_bypass_candidates']=suspect
    assert not suspect
    (OUT/'evidence-check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
