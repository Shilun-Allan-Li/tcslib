"""Configure one-clone/one-tree PFR checks, without native execution.

Usage: python3 -I prepare_pfr.py CLONE TREE STATIC_SUPPLEMENT RUNTIME_DIR REAL_LEAN
All package and toolchain paths are resolved in the caller's own clone/installation.
"""
from pathlib import Path
import hashlib
import json
import os
import shlex
import subprocess
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


def main():
    clone, tree, supplement, runtime, real = [Path(x).resolve() for x in sys.argv[1:]]
    assert len(sys.argv) == 6
    assert clone.is_dir() and real.is_file()
    assert not runtime.exists(), 'Use a fresh runtime directory and retain every previous attempt'
    delivery = supplement / 'DELIVERY-MANIFEST.json'
    assert sha(delivery) == '70dd1a408a2c0c46af7ab2da50ff50520b26b2983e298492935008debb1a2cbd', 'Frozen PFR inventory manifest drift'
    for row in json.loads(delivery.read_text())['files']:
        path = supplement / row['path']
        assert path.resolve(strict=True).is_relative_to(supplement)
        assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], 'Frozen PFR inventory data drift'
    assert (clone / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.25.0'
    manifest = json.loads((clone / 'lake-manifest.json').read_text())
    packages = {p['name']: p for p in manifest['packages']}
    # The adapter never fetches, edits or reclones packages. Every present
    # package must retain the root manifest's exact URL and revision.
    bindings = []
    for name, data in sorted(packages.items()):
        path = clone / '.lake/packages' / name
        if not path.is_dir():
            bindings.append({'name': name, 'status': 'ABSENT'})
            continue
        head = git(path, 'rev-parse', 'HEAD')
        url = git(path, 'remote', 'get-url', 'origin')
        assert head == data['rev'] and url == data['url'], (name, head, url)
        bindings.append({'name': name, 'status': 'MATCH', 'head': head, 'url': url})
    package = clone / '.lake/packages/PFR'
    assert package.resolve(strict=True).is_relative_to(clone), 'Package source must belong to this clone'
    pin = packages['PFR']['rev']
    assert pin == 'e1095d58b7c6f10734988816f7764f2103b9bf29'
    static = json.loads((supplement / 'ordered-modules.json').read_text())
    assert len(static) == 31
    sources = {}
    seen = set()
    for ordinal, row in enumerate(static, 1):
        assert row['package'] == 'PFR' and row['package_revision'] == pin
        assert row['ordinal'] == ordinal and row['module'].startswith('PFR.')
        assert row['module'] not in seen
        assert row['package_relative_source'] == row['module'].replace('.', '/') + '.lean'
        rel = '.lake/packages/PFR/' + row['package_relative_source']
        src = clone / rel
        assert src.resolve(strict=True).is_relative_to(package.resolve(strict=True)/'PFR')
        assert src.is_file() and sha(src) == row['source_sha256']
        raw = src.read_bytes()
        blob = hashlib.sha1(f'blob {len(raw)}\0'.encode() + raw).hexdigest()
        assert blob == row['git_blob']
        assert blob == git(package, 'rev-parse', pin + ':' + row['package_relative_source'])
        for imp in row['imports']:
            name = imp['module']
            if name.startswith('PFR.'):
                assert name in seen, ('Wrong PFR order', row['module'], name)
            else:
                assert name.startswith('Mathlib.'), ('Unexpected external boundary', name)
        sources[rel] = {'sha256': row['source_sha256'], 'module': row['module'], 'git_blob': blob}
        seen.add(row['module'])
    expected_order = '\n'.join(x.removesuffix('.lean') for x in sources) + '\n'
    assert (supplement / 'bootstrap-order.txt').read_text() == expected_order
    pfr_config = next(p for p in json.loads((supplement / 'package-bindings.json').read_text())
                      if p['package'] == 'PFR')
    assert pfr_config['lean_options'] == {
        'autoImplicit': False, 'relaxedAutoImplicit': False,
        'pp': {'unicode': {'fun': True}, 'proofs': {'withType': False}}}
    lake = next(p for p in pfr_config['configuration_files'] if p['package_relative_path'] == 'lakefile.toml')
    assert sha(package / 'lakefile.toml') == lake['sha256']
    tree.mkdir(parents=True, exist_ok=True)
    physical = tree / '.lake/packages/PFR/PFR'
    assert physical.resolve().is_relative_to(tree), 'Physical object prefix escapes the one tree'
    physical.mkdir(parents=True, exist_ok=True)
    logical = tree / 'PFR'
    if logical.exists() or logical.is_symlink():
        assert logical.is_symlink() and logical.resolve(strict=True) == physical.resolve(strict=True), 'Conflicting PFR object prefix'
    else:
        logical.symlink_to('.lake/packages/PFR/PFR', target_is_directory=True)
    assert logical.resolve(strict=True).is_relative_to(tree)
    runtime.mkdir(parents=True, exist_ok=True)
    binary = runtime / 'bin'
    binary.mkdir(exist_ok=True)
    driver = Path(__file__).resolve().with_name('pfr_lean.py')
    config = {'clone': str(clone), 'tree': str(tree), 'real_lean': str(real),
              'real_lean_sha256': sha(real), 'pfr_package_pin': pin,
              'pfr_lakefile_sha256': lake['sha256'], 'sources': sources,
              'driver_sha256': sha(driver), 'package_bindings': bindings,
              'object_namespace_alias': {'path': str(logical), 'relative_target': '.lake/packages/PFR/PFR'},
              'source_aliases_created': False, 'native_execution_performed': False}
    config_path = runtime / 'config.json'
    config_path.write_text(json.dumps(config, indent=2) + '\n')
    entry = binary / 'lean'
    entry.write_text('#!/usr/bin/env bash\nexec python3 -I ' + shlex.quote(str(driver)) + ' "$@"\n')
    entry.chmod(0o755)
    print(json.dumps({'config': str(config_path), 'wrapper_bin': str(binary), 'sources': len(sources),
                      'source_aliases_created': False, 'native_execution_performed': False}, indent=2))


if __name__ == '__main__':
    main()
