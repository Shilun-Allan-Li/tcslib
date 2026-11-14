#!/usr/bin/env python3
"""Inventory added Lean source declarations between the issued base and HEAD.

Run with python3 -I. This is a source-command inventory, including private named
declarations, not a census of generated kernel constants. It reads committed Git
objects, strips nested comments/strings while preserving lines, and tracks command
namespaces. The separate axiom evidence covers generated/stored constants.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess


def git(*args, optional=False):
    process = subprocess.run(["git", *args], capture_output=True, text=True)
    if optional and process.returncode:
        return ""
    assert process.returncode == 0, (args, process.stderr)
    return process.stdout


def scrub(text):
    chars, out = list(text), list(text)
    depth, quoted, i = 0, False, 0
    while i < len(chars):
        pair = text[i:i+2]
        if depth:
            if pair == "/-":
                out[i:i+2] = [" ", " "]
                depth += 1
                i += 2
                continue
            if pair == "-/":
                out[i:i+2] = [" ", " "]
                depth -= 1
                i += 2
                continue
            if chars[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if quoted:
            if chars[i] != "\n":
                out[i] = " "
            if chars[i] == "\\" and i+1 < len(chars):
                if chars[i+1] != "\n":
                    out[i+1] = " "
                i += 2
                continue
            if chars[i] == '"':
                quoted = False
            i += 1
            continue
        if pair == "/-":
            out[i:i+2] = [" ", " "]
            depth = 1
            i += 2
            continue
        if pair == "--":
            while i < len(chars) and chars[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if chars[i] == '"':
            out[i] = " "
            quoted = True
        i += 1
    assert depth == 0 and not quoted, "unterminated comment/string"
    return "".join(out)


DECL = re.compile(
    r"^\s*(?:@\[[^\n]*?\]\s*)*"
    r"(?P<modifiers>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class|opaque|axiom|constant|instance)\b"
    r"(?:\s+(?P<name>[^\s:({\[]+))?"
)


def inventory(text, path):
    result, stack, namespace, anonymous = {}, [], "", Counter()
    original_lines = text.splitlines()
    for number, line in enumerate(scrub(text).splitlines(), 1):
        scope = re.match(r"^\s*(namespace|section|end)(?:\s+([^\s]+))?\s*$", line)
        if scope:
            if scope[1] == "end":
                assert stack, (path, number, "unbalanced end")
                namespace = stack.pop()
            else:
                stack.append(namespace)
                if scope[1] == "namespace":
                    assert scope[2], (path, number, "unnamed namespace")
                    name = scope[2]
                    if name.startswith("_root_."):
                        namespace = name.removeprefix("_root_.")
                    else:
                        namespace = ".".join(filter(None, (namespace, name)))
            continue
        match = DECL.match(line)
        if not match:
            continue
        kind, name = match["kind"], match["name"]
        if name is None:
            assert kind == "instance", (path, number, "unnamed declaration", line)
            anonymous[(namespace, kind)] += 1
            name = f"<anonymous-instance-{anonymous[(namespace, kind)]}>"
        full_name = name.removeprefix("_root_.") if name.startswith("_root_.") else ".".join(
            filter(None, (namespace, name)))
        key = (kind, full_name)
        assert key not in result, (path, number, "duplicate source declaration", key)
        result[key] = dict(path=path, line=number, kind=kind, source_name=name,
                           qualified_source_name=full_name,
                           private="private" in match["modifiers"].split(),
                           source_header=original_lines[number-1].strip())
    assert not stack, (path, "unclosed scope")
    return result


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--base", default="eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9")
parser.add_argument("--head", default="HEAD")
parser.add_argument("--report", type=Path, default=Path("evidence/new-declarations.md"))
parser.add_argument("--json", type=Path, default=Path("evidence/new-declarations.json"))
args = parser.parse_args()
base, head = git("rev-parse", args.base).strip(), git("rev-parse", args.head).strip()
paths = git("diff", "--name-only", base, head, "--", "*.lean").splitlines()
added, removed, sources = [], [], []
for path in paths:
    before, after = git("show", f"{base}:{path}", optional=True), git("show", f"{head}:{path}")
    old, new = inventory(before, path), inventory(after, path)
    added += [new[key] for key in new.keys()-old.keys()]
    removed += [old[key] for key in old.keys()-new.keys()]
    sources.append(dict(path=path, base_sha256=hashlib.sha256(before.encode()).hexdigest() if before else None,
                        head_sha256=hashlib.sha256(after.encode()).hexdigest(),
                        base_declarations=len(old), head_declarations=len(new)))
added.sort(key=lambda d: (d["path"], d["line"]))
removed.sort(key=lambda d: (d["path"], d["line"]))
data = dict(base=base, head=head, method="committed Lean source commands; generated kernel constants excluded",
            changed_files=sources, added_count=len(added), removed_count=len(removed), added=added, removed=removed)
args.json.write_text(json.dumps(data, indent=2) + "\n")
reproduce = shlex.join(["python3", "-I", "evidence/tools/new_declarations.py", "--base", base,
                        "--head", head, "--report", str(args.report), "--json", str(args.json)])
lines = ["# Added source declarations", "", f"Base: `{base}`.", f"Head: `{head}`.", "",
         f"{len(added)} added source declarations across {len(paths)} changed Lean files; {len(removed)} removed.",
         "Private source declarations are included. Compiler-generated kernel constants are covered by",
         "the separate stored-constant census and axiom evidence; they are not invented as source commands here.",
         "", f"Reproduce: `{reproduce}`.", "",
         "The pre-existing target `Authentication.dlHash_crh` has a replaced proof body and is not a new declaration."]
for path in paths:
    declarations = [entry for entry in added if entry["path"] == path]
    lines += ["", f"## {path}", "", f"{len(declarations)} additions.", "",
              "| Line | Kind | Qualified source name | Visibility |", "|---:|---|---|---|"]
    for declaration in declarations:
        visibility = "private" if declaration["private"] else "public"
        lines.append(f"| {declaration['line']} | {declaration['kind']} | `{declaration['qualified_source_name']}` | {visibility} |")
if removed:
    lines += ["", "## Removed source declarations", ""]
    for declaration in removed:
        lines.append(f"- `{declaration['path']}:{declaration['line']}`: `{declaration['qualified_source_name']}`.")
lines.append("")
args.report.write_text("\n".join(lines))
print(json.dumps({"base": base, "head": head, "files": len(paths), "added": len(added), "removed": len(removed)}))
