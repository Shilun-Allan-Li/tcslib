"""Apply the reviewed Gate06 seal/controls machinery to the five S2 modules.

Preparation only. All three underlying tool sources plus this adapter are saved.
The only configuration changes are expected module count 5, S2 root/evidence,
RSA controls, and the independently verified constant-AST request encoding.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
origin = Path(__file__).resolve().parent
root = Path('/Users/seyoonr/.codex/worktrees/ps-gate08-repair/tcslib-pass-shelat-ch2-4')
e = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/fills/shared-lemmas/s2/final/maintainer-rule10')
scratch = root / '.lake/ps-maintainer/gate06'
tool_dir = e / 'tool-inputs'
assert not tool_dir.exists()
assert json.loads((e / 'collect1.json').read_text())['rc'] == 0
scratch.mkdir(parents=True, exist_ok=True)
tool_dir.mkdir()
inputs={}
for src, name in [(origin/'build_seals.py','build_seals.py'),
                  (origin/'build_controls.py','build_controls.py'),
                  (origin/'repairs/prepare_rule10_harness_retry_v3.py','request_payload_adapter.py')]:
    raw=src.read_bytes()
    dest=scratch/name
    assert not dest.exists()
    dest.write_bytes(raw)
    (tool_dir/name).write_bytes(raw)
    inputs[name]=hashlib.sha256(raw).hexdigest()
assert inputs['request_payload_adapter.py'] == 'ae79f1ec66e93c8bc7749a53e12e3d383feda020ad2978520a0cfa24b12eb5de'

def load(name):
    p=scratch/(name+'.py')
    spec=importlib.util.spec_from_file_location('s2_'+name,p)
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value)
    return value

bs, controls, payload = load('build_seals'), load('build_controls'), load('request_payload_adapter')
bs.EXPECTED_MODULES=5
payload.configure_builders(bs,controls)
# Retain the configured, source-identical builder when the control preparer
# loads it, so both installers and catalog verifiers use the same encoding.
controls.load_builder=lambda path: bs
sys.argv=[str(scratch/'build_seals.py'),str(e),'--root',str(root)]
bs.main()
adapter={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'tool_input_sha256':inputs,'expected_math_modules':5,
         'request_encoding':'constant-AST newline/tab String parsed at runtime',
         'proof_budgets_changed':False,'coverage_exclusions_added':False,
         'controls_module':'TCSlib.Cryptography.Candidates.RSA',
         'note':'Underlying tool source retains Gate06 names; this saved adapter supplies S2 configuration.'}
manifest=json.loads((e/'seal-manifest.json').read_text())
manifest['preparation_adapter']=adapter
(e/'seal-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
sys.argv=[str(scratch/'build_controls.py'),str(e),'--root',str(root),
          '--module','TCSlib.Cryptography.Candidates.RSA']
controls.main()
manifest=json.loads((e/'controls-manifest.json').read_text())
manifest['preparation_adapter']=adapter
(e/'controls-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(e/'prepare_s2_seals.py').write_bytes(Path(__file__).read_bytes())
(e/'tool-adapter.json').write_text(json.dumps(adapter,indent=2)+'\n')
print(json.dumps({'modules':5,'controls':11,'native_runs_started':0,'adapter':adapter}))
