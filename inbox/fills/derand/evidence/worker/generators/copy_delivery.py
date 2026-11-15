from pathlib import Path
import shutil
import sys

source = Path(sys.argv[1]).resolve()
root = Path('/Users/seyoonr/.codex/worktrees/exchange-derand/tcslib-exchange').resolve()
target = root / 'inbox/fills/derand'
assert source.name == 'derand' and (source / 'SHA256SUMS').is_file()
assert not target.is_symlink() and target.resolve().is_relative_to(root)
for parent in [root / 'inbox', root / 'inbox/fills']:
    assert not parent.is_symlink()
if target.exists():
    shutil.rmtree(target)
target.parent.mkdir(parents=True, exist_ok=True)
shutil.copytree(source, target)
print(target)
