#!/usr/bin/env python3
"""Normalize exact proposal hunks; dry-run by default. Only the maintainer runs --apply."""
import argparse
import difflib
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

HUNK = re.compile(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@[^\n]*\n\Z")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def parse_patch(text):
    """Pure parser: existing TCSlib .lean paths, same-path edits, exact hunk counts."""
    require(text.endswith("\n") and "\r" not in text, "proposal must use terminated LF lines")
    lines, changes, i = text.splitlines(keepends=True), {}, 0
    while i < len(lines):
        banner = None
        if lines[i].startswith("diff --git "):
            banner = lines[i]
            i += 1
        require(i + 1 < len(lines) and lines[i].startswith("--- a/")
                and lines[i + 1].startswith("+++ b/"), "expected plain same-path file headers")
        path, new = lines[i][6:-1], lines[i + 1][6:-1]
        parts = path.split("/")
        require(path == new and parts[0] == "TCSlib" and len(parts) > 1
                and all(re.fullmatch(r"[A-Za-z0-9_.-]+", x) and x not in (".", "..") for x in parts)
                and PurePosixPath(path).suffix == ".lean", "foreign/unsafe path or rename")
        require(path not in changes, "duplicate file section: " + path)
        require(banner is None or banner == f"diff --git a/{path} b/{path}\n", "invalid diff banner")
        i += 2
        hunks = []
        while i < len(lines) and lines[i].startswith("@@"):
            match = HUNK.fullmatch(lines[i])
            require(match is not None, "malformed hunk header")
            old_start, old_count, new_start, new_count = (int(match[1]), int(match[2] or 1),
                                                        int(match[3]), int(match[4] or 1))
            i += 1
            old, new = [], []
            while i < len(lines) and not lines[i].startswith(("@@", "--- a/", "diff --git ")):
                line = lines[i]
                require(line[:1] in (" ", "+", "-"), "unsupported hunk line/metadata")
                if line[0] != "+":
                    old.append(line[1:])
                if line[0] != "-":
                    new.append(line[1:])
                i += 1
            require((len(old), len(new)) == (old_count, new_count),
                    f"malformed hunk counts in {path}: declared {old_count}/{new_count}, actual {len(old)}/{len(new)}")
            require(old and old_start > 0 and new_start > 0, "empty/unsupported old hunk")
            hunks.append((old_start, new_start, "".join(old), "".join(new)))
        require(hunks, "file section has no hunks: " + path)
        changes[path] = hunks
    require(changes, "empty proposal")
    return changes


def plan(files, changes):
    """Pure exact composition; files is {relative_path: current_text}."""
    canonical, records, proposed = [], [], {}
    digest = lambda value: hashlib.sha256(value.encode("utf-8")).hexdigest()
    for path, hunks in changes.items():
        original = current = files[path]
        require("\r" not in original and (not original or original.endswith("\n")), "source must use terminated LF lines")
        positions = []
        for old_start, new_start, old, new in hunks:
            pos = current.find(old)
            require(pos >= 0 and current.find(old, pos + 1) < 0
                    and (pos == 0 or current[pos - 1] == "\n"), "old hunk is not one exact full-line occurrence: " + path)
            positions.append({"proposal_old_start": old_start, "proposal_new_start": new_start,
                              "matched_start_after_prior_hunks": current[:pos].count("\n") + 1})
            current = current[:pos] + new + current[pos + len(old):]
        require(current != original, "proposal has no change: " + path)
        canonical.extend(difflib.unified_diff(original.splitlines(keepends=True), current.splitlines(keepends=True),
                                             fromfile="a/" + path, tofile="b/" + path, n=3))
        records.append({"path": path, "original_sha256": digest(original),
                        "proposed_sha256": digest(current), "hunks": positions})
        proposed[path] = current
    return "".join(canonical), records, proposed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("proposal", type=Path)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument("--out-prefix", type=Path, required=True, help="new .patch/.json artifact prefix")
    parser.add_argument("--apply", action="store_true", help="maintainer only: check and apply canonical patch")
    args = parser.parse_args()
    root = args.root.resolve()
    raw = args.proposal.read_bytes()
    changes = parse_patch(raw.decode("utf-8"))
    paths = {name: root / name for name in changes}
    require(all(p.resolve() == p and p.is_file() for p in paths.values()), "missing or symlinked target")
    before = {name: p.read_bytes() for name, p in paths.items()}
    canonical, records, _ = plan({name: b.decode("utf-8") for name, b in before.items()}, changes)
    prefix = args.out_prefix.resolve()
    patch_path, meta_path = Path(str(prefix) + ".patch"), Path(str(prefix) + ".json")
    require(prefix.parent.is_dir() and not any(p.exists() for p in (patch_path, meta_path)), "artifact directory missing or artifact already exists")
    require(not prefix.is_relative_to(root / "TCSlib"), "artifacts must be outside TCSlib")
    metadata = {"root": str(root), "proposal": str(args.proposal.resolve()),
                "proposal_sha256": hashlib.sha256(raw).hexdigest(),
                "canonical_patch_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
                "apply_requested": args.apply, "files": records}
    with patch_path.open("x", encoding="utf-8", newline="") as output:
        output.write(canonical)
    with meta_path.open("x", encoding="utf-8", newline="") as output:
        json.dump(metadata, output, indent=2)
        output.write("\n")
    if args.apply:
        for stage in ("--check", None):
            require(all(p.resolve() == p and p.is_file() and p.read_bytes() == before[name]
                        for name, p in paths.items()), "source changed after planning")
            subprocess.run(["git", "apply"] + ([stage] if stage else []) + ["-"],
                           input=canonical.encode("utf-8"), cwd=root, check=True)
    print(("applied" if args.apply else "dry-run") + f": {patch_path} ; {meta_path}")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, UnicodeError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error))
