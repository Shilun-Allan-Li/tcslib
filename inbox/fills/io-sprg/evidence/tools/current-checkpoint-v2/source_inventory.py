#!/usr/bin/env python3
"""UNRUN candidate: current exact-owner lexical inventory, including zero-hole schemas.

No Lean/cache/source mutation. Read-only Git/source validation occurs through the
committed checkpoint inventory. Frozen preservation and full kernel axioms are
independent mandatory guards, never inferred from these lexical counts.
"""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import re
import runpy
import sys
sys.dont_write_bytecode = True

FIELDS = ['Lean_name', 'file_line', 'kind', 'paper_item_page_tag', 'deviations', 'statement_prose']
HOLE_FIELDS = ['Lean_name', 'file_line', 'milestone', 'owner_proof_sketch']


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--inventory', required=True)
    ap.add_argument('--obligations', default='evidence/review/m0-report-sp-w2/proof-obligations.tsv')
    ap.add_argument('--out', required=True, help='Fresh current-checkpoint statements directory')
    ap.add_argument('--require-complete', action='store_true')
    args = ap.parse_args()
    iv = runpy.run_path(str(Path(__file__).with_name('checkpoint_inventory.py')))
    inventory = iv['load'](args.inventory)
    root, out = Path(inventory['root']), Path(args.out).resolve()
    iv['need'](not out.exists(), 'Choose fresh output directory; preserve old inventories')
    parser = runpy.run_path(str(root / 'evidence/tools/clash/clash_scan.py'))
    obligations = Path(args.obligations)
    if not obligations.is_absolute():
        obligations = root / obligations
    old = {row['Lean_name']: row for row in csv.DictReader(obligations.open(), delimiter='\t')}
    rows, holes, seen, tokens = [], [], set(), []
    for path in iv['files'](inventory):
        raw = (root / path).read_bytes()
        text = raw.decode()
        lines, code = text.splitlines(), parser['strip_code'](text)
        decls = parser['parse_decls'](text)
        iv['need'](not any(re.match(r'^\s*example\b', line) for line in code),
                   'Anonymous owned example is not a tracked theorem obligation: ' + path)
        for index, decl in enumerate(decls):
            name = decl['full']
            iv['need'](name not in seen, 'Duplicate lexical declaration: ' + name)
            seen.add(name)
            j = decl['line'] - 2
            while j >= 0 and (not lines[j].strip() or lines[j].startswith('omit ')):
                j -= 1
            doc = ''
            if j >= 0 and lines[j].rstrip().endswith('-/'):
                k = j
                while k >= 0 and '/--' not in lines[k]:
                    k -= 1
                if k >= 0:
                    doc = '\n'.join(lines[k:j + 1]).strip()[3:-2].strip()
            prose = ' '.join(doc.split('**Proof sketch.**', 1)[0].split())
            tag = re.search(r'\[JLS26,\s*([^]]+)\]', prose)
            rows.append(dict(Lean_name=name, file_line=path + ':' + str(decl['line']),
                             kind=decl['kind'], paper_item_page_tag=tag[1] if tag else
                             'No declaration-level JLS tag; inspect owning section/module or glue prose',
                             deviations=','.join(sorted(set(re.findall(r'Dv\d+|SP-W\d+', doc)))),
                             statement_prose=prose))
            end = decls[index + 1]['line'] - 1 if index + 1 < len(decls) else len(code)
            chunk = '\n'.join(code[decl['line'] - 1:end])
            if re.search(r'\b(?:sorry|admit)\b', chunk):
                iv['need'](decl['kind'] in {'theorem', 'lemma'}, 'Non-theorem hole: ' + name)
                iv['need'](name in old, 'New helper/source hole is not a frozen obligation: ' + name)
                iv['need']('**Proof sketch.**' in doc, 'Frozen remaining hole lacks sketch: ' + name)
                holes.append(dict(Lean_name=name, file_line=path + ':' + str(decl['line']),
                                  milestone=old[name]['milestone'],
                                  owner_proof_sketch=' '.join(doc.split('**Proof sketch.**', 1)[1].split())))
        for index, line in enumerate(code, 1):
            for match in re.finditer(r'\b(sorry|admit)\b', line):
                tokens.append({'file': path, 'line': index, 'token': match[1]})
    iv['need']({row['Lean_name'] for row in holes} <= set(old), 'Untracked remaining proof hole')
    if args.require_complete:
        iv['need'](not holes and not tokens, 'Final source still contains proof-hole tokens')
    out.mkdir(parents=True)
    # Fixed schemas deliberately handle the legitimate final empty obligations table.
    for name, data, fields in [('fidelity-current.tsv', rows, FIELDS),
                               ('proof-obligations-current.tsv', holes, HOLE_FIELDS)]:
        with (out / name).open('w') as handle:
            writer = csv.DictWriter(handle, fieldnames=fields, delimiter='\t')
            writer.writeheader()
            writer.writerows(data)
    binding = dict(head=inventory['head'], inventory_sha256=inventory['inventory_sha256'],
                   named_headers=len(rows), named_sorry_bodies=len(holes),
                   sorry_tokens=tokens, remaining_named_obligations=[row['Lean_name'] for row in holes],
                   frozen_obligations_sha256=hashlib.sha256(obligations.read_bytes()).hexdigest(),
                   source_sha256={path: inventory['source_sha256'][path]
                                  for path in iv['files'](inventory)},
                   qualification='Lexical source/docstring inventory, not typed or axiom evidence. '
                                 'Remaining holes are a subset of frozen obligations; new helpers '
                                 'cannot carry sorry. Full stored-constant graph remains mandatory.')
    (out / 'source-inventory-binding.json').write_text(json.dumps(binding, indent=2) + '\n')
    print('SOURCE_INVENTORY', len(rows), 'headers;', len(holes), 'remaining frozen holes;',
          len(tokens), 'source sorry/admit tokens')


if __name__ == '__main__':
    main()
