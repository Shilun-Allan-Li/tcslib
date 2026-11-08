"""PFR-only source-root/options adapter for the unchanged one-module checker.

Invoke through the generated shell entry point, which uses python3 -I. This does
not locate or repair Lean: configuration binds an already working pinned binary.
"""
from pathlib import Path
import hashlib
import json
import os
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    cfg = json.loads(Path(os.environ['PFR_BOOTSTRAP_CONFIG']).read_text())
    assert sha(Path(__file__).resolve()) == cfg['driver_sha256'], 'Adapter source drift'
    clone = Path(cfg['clone']).resolve(strict=True)
    package = (clone / '.lake/packages/PFR').resolve(strict=True)
    tree = Path(cfg['tree']).resolve(strict=True)
    assert Path.cwd().resolve() == clone
    assert len(sys.argv) == 4 and sys.argv[2] == '-o', 'Unexpected checker argument shape'
    relative = sys.argv[1]
    assert relative in cfg['sources'], 'Source is outside the fixed PFR closure'
    src = (clone / relative).resolve(strict=True)
    assert src.is_relative_to(package / 'PFR')
    assert sha(src) == cfg['sources'][relative]['sha256'], 'Pinned PFR source drift'
    assert (clone / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.25.0'
    assert (package / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.25.0'
    assert sha(package / 'lakefile.toml') == cfg['pfr_lakefile_sha256']
    physical = tree / relative.removesuffix('.lean')
    expected = Path(str(physical) + '.olean').resolve()
    actual = Path(sys.argv[3]).resolve()
    assert actual == expected and actual.is_relative_to(tree), 'Object escapes the one tree'
    namespace = tree / 'PFR'
    assert namespace.is_symlink()
    target = (tree / '.lake/packages/PFR/PFR').resolve(strict=True)
    assert namespace.resolve(strict=True) == target and target.is_relative_to(tree)
    real = Path(cfg['real_lean']).resolve(strict=True)
    assert real.is_file() and sha(real) == cfg['real_lean_sha256']
    # Exact PFR lakefile options. This selects a compilation root, not a
    # locator shim, trust option, alternate toolchain or proof shortcut.
    options = ['-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
               '-Dpp.unicode.fun=true', '-Dpp.proofs.withType=false']
    os.execv(str(real), [str(real), '--root=' + str(package), *options, *sys.argv[1:]])


if __name__ == '__main__':
    main()
