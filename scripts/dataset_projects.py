"""Source roots and provenance for independently compiled dataset projects.

Paths in dataset/projects.json are relative to the dataset repository, not the
caller's working directory. A project keeps its original module names and Lean
environment; registering it does not add a Lake dependency to TCSlib.
"""

from __future__ import annotations

from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import shutil

BASE = Path(__file__).resolve().parent.parent
REGISTRY = BASE / "dataset" / "projects.json"


@lru_cache(maxsize=1)
def projects() -> dict[str, Path]:
    rows = json.loads(REGISTRY.read_text()).get("projects", {}) if REGISTRY.exists() else {}
    return {"TCSlib": BASE, **{name: (BASE / row["root"]).resolve()
                               for name, row in rows.items()}}


def project_name(module: str) -> str:
    return module.split(".", 1)[0]


def is_internal(module: str) -> bool:
    return project_name(module) in projects()


def source_path(module: str) -> Path:
    root = projects().get(project_name(module))
    if root is None:
        raise ValueError(f"No dataset project registered for {module}")
    return root / (module.replace(".", "/") + ".lean")


def display_path(path: Path) -> str:
    return os.path.relpath(path, BASE)


def source_modules() -> dict[str, Path]:
    return {name + "." + p.relative_to(root / name).with_suffix("").as_posix().replace("/", "."): p
            for name, root in projects().items() for p in (root / name).rglob("*.lean")}


def module_matches(module: str, wanted) -> bool:
    for w in wanted:
        w = w.strip()
        if not w:
            continue
        full = w if is_internal(w) else project_name(module) + "." + w
        if module == full or module.endswith("." + w) or module.startswith(full + "."):
            return True
    return False


def sha256(path: Path) -> str | None:
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def provenance(name: str, root: Path) -> dict:
    def git(*args):
        p = subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True)
        return p.stdout.strip() if p.returncode == 0 else None
    toolchain = root / "lean-toolchain"
    license_text = (root / "LICENSE").read_text() if (root / "LICENSE").is_file() else ""
    return {"project": name, "commit": git("rev-parse", "HEAD"),
            "repository": git("remote", "get-url", "origin"),
            "lean_toolchain": toolchain.read_text().strip() if toolchain.exists() else None,
            "dependency_manifest_sha256": sha256(root / "lake-manifest.json"),
            "license": "Apache-2.0" if "Apache License" in license_text and "Version 2.0" in license_text else None,
            "license_file": "LICENSE" if name == "TCSlib" else f"dataset/licenses/{name}.txt",
            "license_sha256": sha256(root / "LICENSE")}


@lru_cache(maxsize=None)
def source_provenance(module: str) -> dict:
    path = source_path(module)
    text = path.read_text()
    header = text[:text.index("-/") + 2] if text.startswith("/-") and "-/" in text else ""
    return {"source_sha256": sha256(path), "source_header": header}


def register(specs: list[str]) -> None:
    rows = json.loads(REGISTRY.read_text()) if REGISTRY.exists() else {"projects": {}}
    for spec in specs:
        name, sep, value = spec.partition("=")
        if not sep or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name) or name == "TCSlib":
            raise ValueError("Use --project-root ModuleRoot=/path/to/project (TCSlib is implicit)")
        root = Path(value).expanduser().resolve()
        if not (root / name).is_dir() or not (root / "lean-toolchain").is_file():
            raise ValueError(f"{root} is not a Lean project containing {name}/")
        if not (root / ".lake/build/lib/lean" / name).is_dir():
            raise ValueError(f"{root} has no compiled artifacts for {name}")
        if (root / "LICENSE").is_file():
            notices = BASE / "dataset/licenses"
            notices.mkdir(parents=True, exist_ok=True)
            shutil.copy2(root / "LICENSE", notices / f"{name}.txt")
        rows["projects"][name] = {"root": display_path(root), **provenance(name, root)}
    REGISTRY.parent.mkdir(parents=True, exist_ok=True)
    REGISTRY.write_text(json.dumps(rows, indent=2) + "\n")
    projects.cache_clear()

