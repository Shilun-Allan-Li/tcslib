"""Selected axiom and instance-attribute checks after the local cold replay."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

PREP = Path(__file__).resolve().parent
OUT = PREP / 'partial-r1/native-fixes-r1'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    result = json.loads((OUT / 'RESULT.json').read_text())
    assert result['all_passed'] and result['checked_local_modules'] == 124
    work = Path(result['worktree'])
    tree = Path(result['tree'])
    attempts = [json.loads(line) for line in (OUT / 'attempts.jsonl').read_text().splitlines()]
    for row in attempts:
        assert sha(OUT / row['log']) == row['log_sha256']
    latest = {row['module']: row for row in attempts}
    assert len(latest) == 125 and len([row for row in attempts if not row['passed']]) == 2
    for row in latest.values():
        assert row['passed'] and sha(work / (row['module'] + '.lean')) == row['source_sha256']
        assert sha(tree / (row['module'] + '.olean')) == row['object_sha256']
    env = dict(os.environ)
    env['PATH'] = str(Path.home() / '.elan/bin') + ':' + env['PATH']
    env.pop('LEAN_PATH', None)
    env['TCSLIB_OLEANS'] = str(tree)
    checker = work / 'scripts/lean_check_tree.sh'
    assert sha(checker) == result['checker_sha256']
    prefix = '.lake/ps-maintainer/cleanup-partial-fixes-20261108-r1/'

    def check(name, source):
        for process in ['lean', 'lake']:
            response = subprocess.run(['pgrep', '-x', process], capture_output=True, text=True)
            assert response.returncode == 1, ('Shared host occupied', process, response.stdout)
        module = prefix + name
        path = work / (module + '.lean')
        assert not path.exists()
        path.write_text(source)
        source_sha = sha(path)
        log_path = OUT / 'evidence/logs' / (name + '.attempt01.log')
        command = ['/usr/bin/time', '-l', 'bash', 'scripts/lean_check_tree.sh', module]
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        t0 = time.monotonic()
        with log_path.open('xb') as log:
            log.write((json.dumps({'event': 'START', 'utc': start, 'module': module,
                                  'source_sha256': source_sha, 'command': command,
                                  'runner_sha256': sha(Path(__file__)),
                                  'closure_result_sha256': sha(OUT / 'RESULT.json')}) + '\n').encode())
            log.flush()
            process = subprocess.Popen(command, cwd=work, env=env, stdin=subprocess.DEVNULL,
                                       stdout=log, stderr=subprocess.STDOUT)
            rc = process.wait()
            end = datetime.datetime.now(datetime.timezone.utc).isoformat()
            elapsed = time.monotonic() - t0
            log.write((json.dumps({'event': 'END', 'utc': end, 'rc': rc,
                                   'elapsed_seconds': elapsed}) + '\n').encode())
        raw = log_path.read_text()
        obj = tree / (module + '.olean')
        passed = (rc == 0 and not re.search(r'\berror(?:\([^)]*\))?:', raw)
                  and obj.is_file() and obj.stat().st_size > 0 and sha(path) == source_sha)
        report = {'module': module, 'source': source, 'source_sha256': source_sha,
                  'start_utc': start, 'end_utc': end, 'elapsed_seconds': elapsed,
                  'rc': rc, 'passed': passed, 'log': str(log_path.relative_to(OUT)),
                  'log_sha256': sha(log_path),
                  'object_sha256': sha(obj) if obj.exists() else None}
        (OUT / (name + '.json')).write_text(json.dumps(report, indent=2) + '\n')
        assert passed, ('Preserve failed probe; no native claim', name)
        return report, raw

    names = [
        'Complexity.NUPPT.ofPolyTime',
        'Complexity.NUPPT.output_ofPolyTimeUniform',
        'Complexity.NUPPT.runAtL_ofPolyTimeUniform',
        'TCSlib.Cryptography.not_hardCore_const',
        'TCSlib.Cryptography.Collection.glPadSample_runAt',
        'TCSlib.Cryptography.Collection.glPad_sample_runAtL',
        'TCSlib.Cryptography.EncodingMachines.unaryMul_poly',
        'TCSlib.Cryptography.OneWay.polyTimeComputable_unaryMulPair',
        'TCSlib.Cryptography.GGMRed.unaryMul_poly',
        'TCSlib.Cryptography.GI.unaryMul_poly',
    ]
    source = ''.join('import ' + module + '\n' for module in [
        'TCSlib.Cryptography.Asymptotic.HardCore',
        'TCSlib.Cryptography.ZeroKnowledge.EncodingMachines',
        'TCSlib.Cryptography.Asymptotic.GGMReduction',
        'TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep',
    ]) + '\n' + '\n'.join('#print axioms ' + name for name in names) + '\n'
    report, raw = check('SelectedAxioms', source)
    axiom_rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", raw, re.S)
    axioms = {name: [value.strip() for value in values.split(',') if value.strip()]
              for name, values in axiom_rows}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", raw):
        assert name not in axioms
        axioms[name] = []
    assert set(axioms) == set(names)
    report['axioms'] = axioms
    report['standard_only'] = set(value for values in axioms.values() for value in values) <= {
        'propext', 'Classical.choice', 'Quot.sound'}
    report['limit'] = 'Ten selected actual constants only; not the complete cleanup axiom census.'
    (OUT / 'SelectedAxioms-result.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'selected_axiom_sets': len(axioms), 'standard_only': report['standard_only']}), flush=True)

    instance_source = '''import TCSlib.Complexity.TuringMachine.Configuration
import Lean

open Lean Lean.Meta in
run_cmd do
  let n := `Turing.instInhabitedCfg
  let env ← getEnv
  let info ← getConstInfo n
  unless info.isDefinition && isInstanceCore env n do
    throwError "Expected the exact imported definition-instance"
  unless (← getReducibilityStatus n) matches .semireducible do
    throwError "Expected semireducible before local attribute"
  logInfo m!"INSTANCE-ELIGIBILITY before name={n.toString} kind=definition instance=true status=semireducible"

attribute [local irreducible] Turing.instInhabitedCfg

open Lean Lean.Meta in
run_cmd do
  let n := `Turing.instInhabitedCfg
  unless (← getReducibilityStatus n) matches .irreducible do
    throwError "Local irreducibility was not installed"
  logInfo m!"INSTANCE-ELIGIBILITY after name={n.toString} status=irreducible; EOF"
'''
    instance, raw = check('InstanceEligibility', instance_source)
    assert raw.count('INSTANCE-ELIGIBILITY before name=Turing.instInhabitedCfg') == 1
    assert raw.count('INSTANCE-ELIGIBILITY after name=Turing.instInhabitedCfg status=irreducible; EOF') == 1
    instance['eligibility_verified'] = True
    instance['limit'] = ('One exact ordinary semireducible definition-instance accepts local irreducibility without unsafe options. '
                         'This is not a complete instance sensitivity test or a notation/scope ruling.')
    (OUT / 'InstanceEligibility-result.json').write_text(json.dumps(instance, indent=2) + '\n')
    print(json.dumps({'instance_attribute_eligibility': True, 'instance': 'Turing.instInhabitedCfg'}), flush=True)


if __name__ == '__main__':
    main()
