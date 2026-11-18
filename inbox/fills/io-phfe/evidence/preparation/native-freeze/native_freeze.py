#!/usr/bin/env python3
"""Rebuild a stronger, separate M0 freeze from Git source using native Lean syntax spans.

No Lean command is chosen automatically. --parser-command-json must be an explicit
slot-wrapped native parser command approved/run by the lead. Git operations here are
read-only. The original manifest and live sources are never written.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

BASE_REF = "70b85f9ba83f27393d98fa5bf88505aea3d22a8d"
MARKER = b"**Proof sketch.**"
PREFIX = "NATIVE_FREEZE_JSON\t"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def dump(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def checked_git(repo: Path, *args: str) -> bytes:
    proc = subprocess.run(["git", "-C", str(repo), *args], capture_output=True)
    if proc.returncode:
        raise RuntimeError(f"read-only git failed {args!r}: {proc.stderr.decode(errors='replace')}")
    return proc.stdout


def relative_file(raw: str) -> str:
    p = PurePosixPath(raw)
    if p.is_absolute() or ".." in p.parts or p.suffix != ".lean":
        raise ValueError(f"unsafe/non-Lean source path: {raw!r}")
    return p.as_posix()


def module_of(path: str) -> str:
    return str(PurePosixPath(path).with_suffix("")).replace("/", ".")


def text_slice(source: bytes, span: dict) -> bytes:
    a, b = span["start"], span["stop"]
    if not isinstance(a, int) or not isinstance(b, int) or not 0 <= a <= b <= len(source):
        raise ValueError(f"invalid native UTF-8 byte span: {span}")
    piece = source[a:b]
    piece.decode("utf-8")  # Reject offsets inside multibyte characters.
    return piece


def normalize(source: bytes, result: dict) -> dict:
    if result.get("schema") != "native-freeze-spans-v1":
        raise ValueError("unexpected native extractor schema")
    if result["sourceBytes"] != len(source):
        raise ValueError("native/source byte count mismatch")
    rows = {}
    for row in result["rows"]:
        name = row["name"]
        if name in rows:
            raise ValueError(f"duplicate parsed declaration name: {name}")
        command = row["command"]
        text_slice(source, command)
        header_start = row["headerStart"]
        prose = ""
        doc = row.get("doc")
        if doc is not None:
            raw = text_slice(source, doc)
            if not raw.startswith(b"/--") or not raw.endswith(b"-/"):
                raise ValueError(f"unexpected native doc span for {name}: {raw[:60]!r}")
            # Preserve the original freeze policy: only the opening prose before
            # the explicitly marked proof-sketch remainder is frozen.
            prose = raw[3:-2].split(MARKER, 1)[0].decode("utf-8").rstrip()
            if header_start != doc["stop"]:
                raise ValueError("header/doc boundary mismatch")
        stop = command["stop"]
        if row["kind"] in ("theorem", "lemma"):
            delim = row.get("delimiter")
            proof = row.get("proofTerm")
            signature = row.get("signature")
            if delim is None or proof is None or signature is None:
                raise ValueError(f"missing native theorem spans for {name}")
            if text_slice(source, delim) != b":=":
                raise ValueError(f"native body token is not := for {name}")
            text_slice(source, proof)
            text_slice(source, signature)
            if not signature["stop"] <= delim["start"] < delim["stop"] <= proof["start"]:
                raise ValueError(f"signature/body ordering mismatch for {name}")
            stop = delim["start"]
            for body in row["returnLetBodies"]:
                text_slice(source, body)
                if not signature["start"] <= body["start"] < body["stop"] <= stop:
                    raise ValueError(f"return-type let lies outside frozen header: {name}")
        if not command["start"] <= header_start <= stop <= command["stop"]:
            raise ValueError(f"invalid header ordering for {name}")
        header = source[header_start:stop].decode("utf-8").strip()
        if not header:
            raise ValueError(f"empty native header for {name}")
        rows[name] = {
            "kind": row["kind"], "private": row["privateDecl"],
            "prose": prose, "header": header,
        }
    return rows


def compare(old: dict, new: dict) -> tuple[list, list]:
    changes, helpers = [], []
    for file, rows in old.items():
        if file not in new:
            changes.append({"file": file, "reason": "REMOVED_FILE"})
            continue
        for name, record in rows.items():
            if name not in new[file]:
                changes.append({"file": file, "name": name, "reason": "REMOVED"})
            elif record != new[file][name]:
                fields = [k for k in record if record[k] != new[file][name][k]]
                changes.append({"file": file, "name": name, "reason": "CHANGED", "fields": fields})
    for file, rows in new.items():
        helpers.extend({"file": file, "name": name} for name in rows if name not in old.get(file, {}))
    return changes, helpers


class Native:
    def __init__(self, command: list[str], repo: Path, sysroot: str, out: Path):
        self.command, self.repo, self.sysroot, self.out = command, repo, sysroot, out
        self.serial = 0

    def parse(self, module: str, requests: list[dict]) -> dict:
        self.serial += 1
        stem = f"{self.serial:04d}-{module}"
        request_file = self.out / "requests" / f"{stem}.json"
        dump(request_file, requests)
        proc = subprocess.run(
            self.command + [self.sysroot, module, str(request_file)],
            cwd=self.repo, capture_output=True, text=True,
        )
        logdir = self.out / "logs"
        logdir.mkdir(exist_ok=True)
        (logdir / f"{stem}.stdout").write_text(proc.stdout)
        (logdir / f"{stem}.stderr").write_text(proc.stderr)
        dump(logdir / f"{stem}.command.json", {"argv": self.command + [self.sysroot, module, str(request_file)], "returncode": proc.returncode})
        if proc.returncode:
            raise RuntimeError(f"native parser failed for {module}; see {logdir / stem}")
        parsed = {}
        for line in proc.stdout.splitlines():
            if not line.startswith(PREFIX):
                continue  # Slot-wrapper/status output is retained in raw logs.
            result = json.loads(line[len(PREFIX):])
            identity = result["id"]
            if identity in parsed or result["moduleName"] != module:
                raise ValueError("duplicate native result id or wrong imported module")
            parsed[identity] = result
        if set(parsed) != {r["id"] for r in requests}:
            raise ValueError("native result coverage mismatch; no partial audit is accepted")
        for request in requests:
            if parsed[request["id"]]["path"] != request["path"]:
                raise ValueError("native source path mismatch")
        return parsed


def one_character(source: bytes, start: int, stop: int) -> tuple[bytes, int]:
    match = re.search(rb"[A-Za-z]", source[start:stop])
    if match is None:
        raise ValueError("no one-byte alphabetic control position in required native span")
    at = start + match.start()
    replacement = b"Z" if source[at:at + 1] != b"Z" else b"Y"
    return source[:at] + replacement + source[at + 1:], at


def run_controls(native: Native, baseline_sources: dict, native_rows: dict, baseline: dict, out: Path) -> dict:
    let_target = next(((f, r) for f, result in native_rows.items() for r in result["rows"]
                       if r["kind"] in ("theorem", "lemma") and r["returnLetBodies"]), None)
    prose_target = next(((f, r) for f, result in native_rows.items() for r in result["rows"]
                         if r["kind"] in ("theorem", "lemma") and r.get("doc") is not None
                         and MARKER in text_slice(baseline_sources[f], r["doc"])), None)
    if let_target is None or prose_target is None:
        raise ValueError("required baseline return-let/doc-sketch negative-control targets absent")
    controls = []
    file, row = let_target
    span = row["returnLetBodies"][0]
    mutated, at = one_character(baseline_sources[file], span["start"], span["stop"])
    if at >= row["delimiter"]["start"]:
        raise ValueError("type control did not precede actual native declaration body")
    controls.append(("one_character_type_after_return_let", file, mutated, False, at))
    file, row = prose_target
    source = baseline_sources[file]
    doc = row["doc"]
    marker_at = source.index(MARKER, doc["start"], doc["stop"])
    mutated, at = one_character(source, doc["start"] + 3, marker_at)
    assert MARKER in text_slice(mutated, doc)
    controls.append(("source_prose_edit_with_sketch_present", file, mutated, False, at))
    # The delimiter itself is policy-sensitive: corrupting it must not hide prose.
    at = marker_at + 2
    mutated = source[:at] + b"X" + source[at + 1:]
    controls.append(("proof_sketch_marker_edit", file, mutated, False, at))
    mutated, at = one_character(source, marker_at + len(MARKER), doc["stop"] - 2)
    controls.append(("proof_sketch_only_edit_allowed", file, mutated, True, at))
    proof = row["proofTerm"]
    mutated = source[:proof["start"]] + b"by\n  exact (by sorry)" + source[proof["stop"]:]
    if mutated == source:
        raise ValueError("positive proof-body control did not change source bytes")
    controls.append(("proof_body_only_edit_allowed", file, mutated, True, proof["start"]))
    results = {}
    for label, file, mutated, expected_pass, at in controls:
        path = out / "controls" / f"{label}.lean"
        path.parent.mkdir(exist_ok=True)
        path.write_bytes(mutated)
        parsed = native.parse(module_of(file), [{"id": label, "path": str(path)}])[label]
        # A negative control counts only when native parsing succeeds: a parse failure
        # is not evidence that a well-formed source mutation was compared correctly.
        rows = normalize(mutated, parsed)
        changes, helpers = compare({file: baseline[file]}, {file: rows})
        passed = not changes
        results[label] = {
            "expected_check_pass": expected_pass, "check_pass": passed,
            "correct": passed == expected_pass, "file": file, "byte": at,
            "source_sha256": digest(mutated), "changes": changes, "helpers": helpers,
        }
    dump(out / "negative-controls.json", results)
    if not all(r["correct"] for r in results.values()):
        raise RuntimeError("native source mutation controls did not behave as required")
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--original-manifest", required=True, type=Path)
    parser.add_argument("--files-list", required=True, type=Path)
    parser.add_argument("--parser-source", required=True, type=Path)
    parser.add_argument("--parser-command-json", required=True)
    parser.add_argument("--sysroot", required=True)
    parser.add_argument("--baseline-ref", default=BASE_REF)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    repo, out = args.repo.resolve(), args.out.resolve()
    original_path, parser_source = args.original_manifest.resolve(), args.parser_source.resolve()
    command = json.loads(args.parser_command_json)
    if not isinstance(command, list) or not command or not all(isinstance(v, str) and v for v in command):
        raise ValueError("parser command must be an explicit nonempty JSON argv array")
    original_bytes, parser_bytes = original_path.read_bytes(), parser_source.read_bytes()
    original = json.loads(original_bytes)
    ref = checked_git(repo, "rev-parse", "--verify", f"{args.baseline_ref}^{{commit}}").decode().strip()
    if original.get("head") != ref or ref != BASE_REF:
        raise ValueError("original checkpoint0 manifest and exact authorized Git baseline disagree")
    # Refuse to overwrite ANY previous stronger baseline or audit evidence.
    out.mkdir(parents=True, exist_ok=False)
    current_files = [relative_file(s.strip()) for s in args.files_list.read_text().splitlines() if s.strip()]
    files = sorted(set(current_files) | {relative_file(f) for f in original["files"]})
    tracked = set(checked_git(repo, "ls-tree", "-r", "--name-only", ref).decode().splitlines())
    baseline_sources, current_sources, source_metadata = {}, {}, {}
    for file in files:
        if file in tracked:
            baseline_sources[file] = checked_git(repo, "show", f"{ref}:{file}")
        elif file in original["files"]:
            raise ValueError(f"original frozen file absent from authorized checkpoint Git source: {file}")
        live = repo / file
        if live.is_file():
            current_sources[file] = live.read_bytes()
        source_metadata[file] = {}
        for label, sources in (("baseline", baseline_sources), ("current", current_sources)):
            if file in sources:
                sources[file].decode("utf-8")
                target = out / "sources" / label / file
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(sources[file])
                source_metadata[file][label] = {"path": str(target), "sha256": digest(sources[file])}
    native = Native(command, repo, args.sysroot, out)
    baseline, current, native_baseline = {}, {}, {}
    for file in files:
        requests = [{"id": label, "path": source_metadata[file][label]["path"]}
                    for label in ("baseline", "current") if label in source_metadata[file]]
        if not requests:
            continue
        parsed = native.parse(module_of(file), requests)
        for label, sources, destination in (("baseline", baseline_sources, baseline), ("current", current_sources, current)):
            if label in parsed:
                destination[file] = normalize(sources[file], parsed[label])
                dump(out / "native-spans" / label / (file + ".json"), parsed[label])
                if label == "baseline":
                    native_baseline[file] = parsed[label]
    # Original manifest is coverage evidence, never the source of a truncated new header.
    coverage = []
    for file, old_rows in original["files"].items():
        for name, old in old_rows.items():
            new = baseline.get(file, {}).get(name)
            if new is None:
                coverage.append({"file": file, "name": name, "reason": "ORIGINAL_NAME_NOT_NATIVE_PARSED"})
            elif any(new[k] != old[k] for k in ("kind", "private", "prose")):
                coverage.append({"file": file, "name": name, "reason": "BASELINE_METADATA_MISMATCH"})
    dump(out / "original-coverage.json", coverage)
    if coverage:
        raise RuntimeError("native baseline did not reproduce original manifest coverage/metadata")
    common_metadata = {
        "schema": "native-freeze-manifest-v1", "baseline_head": ref,
        "original_manifest": str(original_path), "original_manifest_sha256": digest(original_bytes),
        "parser_source": str(parser_source), "parser_source_sha256": digest(parser_bytes),
        "driver_sha256": digest(Path(__file__).read_bytes()),
        "parser_command": command, "sysroot": args.sysroot,
        "prose_policy": "opening doc prose before first literal **Proof sketch.**; remainder excluded",
        "scope": "all parsed declarations in original-manifest files plus current owned-files list",
    }
    dump(out / "native-checkpoint0.json", common_metadata | {"files": baseline})
    dump(out / "native-current.json", common_metadata | {"files": current})
    changes, helpers = compare(baseline, current)
    controls = run_controls(native, baseline_sources, native_baseline, baseline, out)
    if original_path.read_bytes() != original_bytes or parser_source.read_bytes() != parser_bytes:
        raise RuntimeError("original manifest or parser source changed during the audit")
    if any(not (repo / f).is_file() or (repo / f).read_bytes() != data for f, data in current_sources.items()):
        raise RuntimeError("live source changed during audit; take a new snapshot and rerun")
    report = common_metadata | {
        "pass": not changes, "changes": changes, "helpers": helpers,
        "original_declarations": sum(map(len, original["files"].values())),
        "native_baseline_declarations": sum(map(len, baseline.values())),
        "native_current_declarations": sum(map(len, current.values())),
        "negative_controls_correct": all(v["correct"] for v in controls.values()),
        "source_metadata": source_metadata,
        "limitation": "native syntax/header preservation only; compiled declaration-type/axiom audit remains separate",
    }
    dump(out / "report.json", report)
    print(json.dumps({k: report[k] for k in ("pass", "original_declarations", "native_baseline_declarations", "native_current_declarations", "negative_controls_correct")}, indent=2))
    return 0 if report["pass"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"NATIVE_FREEZE_DRIVER_ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
