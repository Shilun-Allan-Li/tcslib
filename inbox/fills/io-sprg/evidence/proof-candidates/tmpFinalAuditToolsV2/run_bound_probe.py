#!/usr/bin/env python3
"""UNRUN ROOT-ONLY runner: bind a prepared census/axiom-print probe to current imports.

Delegates the sole Lean invocation to the unchanged pinned serial runner_full.py.
This preparing subagent has never invoked it. No algorithm or implementation edits.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import subprocess

WRAPPER_SHA = 'ff64d8d5b6baf4e7b1c15172a7faeb70246f22c6acf76134bbdb70c017f41f1a'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--inventory', required=True)
    ap.add_argument('--prepared-binding', required=True)
    ap.add_argument('--environment-tree', required=True)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    home = Path(__file__).resolve().parent
    iv = runpy.run_path(str(home / 'checkpoint_inventory.py'))
    inv = iv['load'](args.inventory)
    root, out = Path(inv['root']), Path(args.out).resolve()
    iv['need'](not out.exists(), 'Use a fresh probe-run directory')
    prepared_path = Path(args.prepared_binding)
    prepared = json.loads(prepared_path.read_text())
    iv['need'](prepared['head'] == inv['head'] and
               prepared['inventory_sha256'] == inv['inventory_sha256'] and
               prepared['owners'] == inv['owners'], 'Prepared probe inventory differs')
    module = prepared['probe_module']
    source = (root / (module + '.lean')).resolve()
    iv['need'](source.is_relative_to(root / 'evidence/probes'), 'Probe outside evidence/probes')
    sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
    iv['need'](sha(source) == prepared['probe_sha256'], 'Prepared probe source differs')
    iv['need'](sha('/private/tmp/io-sprg-tools/lean-slot.sh') == WRAPPER_SHA,
               'Pinned serial slot wrapper differs')
    out.mkdir(parents=True)
    eb = runpy.run_path(str(home / 'io-sprg-rule10/environment_binding.py'))
    before = eb['snapshot'](args.environment_tree, out)
    order = out / 'order.txt'
    order.write_text(module + '\n')
    env = dict(os.environ, LEAN_SLOT_TAG='io-sprg')
    subprocess.run(['python3', '-I', str(root / 'evidence/tools/seal/runner_full.py'),
                    str(root), str(order), str(Path(args.environment_tree).resolve()), str(out)],
                   cwd=root, env=env, check=True)
    after = eb['snapshot'](args.environment_tree, out)
    iv['need'](before == after, 'Import environment changed during diagnostic run')
    iv['need'](iv['load'](args.inventory) == inv, 'Committed inventory changed during run')
    rows = [json.loads(line) for line in (out / 'results.jsonl').read_text().splitlines()]
    runs = [row for row in rows if 'module' in row]
    iv['need'](len(runs) == 1 and runs[0]['module'] == module,
               'Unexpected diagnostic run-result coverage')
    row = runs[0]
    log = out / 'mods' / (module.replace('/', '_') + '.log')
    iv['need'](row['source_sha256'] == prepared['probe_sha256'] == sha(source)
               and row['log_sha256'] == sha(log), 'Run source/log differs')
    iv['need'](row['rc'] == row['errors'] == 0 and not re.search(r'error[:(]', log.read_text()),
               'Diagnostic probe has a failing return code or error form')
    binding = dict(head=inv['head'], inventory_sha256=inv['inventory_sha256'],
                   owners=inv['owners'], environment_sha256=after,
                   prepared_binding=str(prepared_path.resolve()),
                   prepared_binding_sha256=sha(prepared_path), probe_module=module,
                   probe_sha256=sha(source), log=str(log), log_sha256=sha(log),
                   results_sha256=sha(out / 'results.jsonl'), run=row,
                   wrapper_sha256=WRAPPER_SHA, status='CURRENT_BOUND_PROBE_PASS')
    (out / 'current-probe-binding.json').write_text(json.dumps(binding, indent=2) + '\n')
    print('CURRENT_BOUND_PROBE_PASS', module, after)


if __name__ == '__main__':
    main()
