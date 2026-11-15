"""Give the proof worktree physical probe paths; copy only finished evidence."""
from pathlib import Path
import shutil

dest = Path('evidence')
expected = Path('/Users/seyoonr/.codex/worktrees/derand/tcslib-exchange/evidence')
assert dest.is_symlink() and dest.resolve() == expected
dest.unlink()
dest.mkdir()
for child in expected.iterdir():
    if child.name == 'logs':
        target = dest / 'logs'
        target.mkdir()
        for log in child.iterdir():
            if log.name == 'base-bootstrap':
                continue
            if log.is_dir():
                shutil.copytree(log, target / log.name)
            else:
                shutil.copy2(log, target / log.name)
    elif child.is_dir():
        shutil.copytree(child, dest / child.name)
    else:
        shutil.copy2(child, dest / child.name)
print('Copied completed evidence only; running baseline logs remain in their original directory.')
