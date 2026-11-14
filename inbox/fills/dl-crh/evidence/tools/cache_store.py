#!/usr/bin/env python3
"""Record the cache tool's existing archive store without changing it."""
import os
from pathlib import Path

store = Path(os.environ.get("XDG_CACHE_HOME", str(Path.home() / ".cache"))) / "mathlib"
entries = [p for p in store.rglob("*") if p.is_file()] if store.exists() else []
print(f"store={store}")
print(f"exists={store.exists()}")
print(f"files={len(entries)}")
print(f"bytes={sum(p.stat().st_size for p in entries)}")
print("origin=pre-existing host cache; exact originating sessions unknown")
