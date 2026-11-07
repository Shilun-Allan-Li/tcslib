"""Lexical sorry census outside nested comments, strings and quoted identifiers.

Usage: python3 -I sorrycensus.py <root> [--rev REV]. This is not elaboration.
"""
from pathlib import Path
import argparse
import re
import subprocess

TOKEN = re.compile(r"(?<![\w.'])sorry(?![\w'])")
RAW_START = re.compile(r'r(#+)"')


def code_text(source):
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1; out.append("  "); i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1; out.append("  "); i += 2
        elif depth:
            out.append("\n" if source[i] == "\n" else " "); i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            out.append(" " * (end - i)); i = end
        elif source[i] == "«":
            end = source.find("»", i + 1)
            end = len(source) if end < 0 else end + 1
            out.append(" " * (end - i)); i = end
        else:
            raw = RAW_START.match(source, i)
            if raw:
                marker = '"' + raw.group(1)
                end = source.find(marker, raw.end())
                end = len(source) if end < 0 else end + len(marker)
                out.append("\n" * source[i:end].count("\n") + " "); i = end
            elif source[i] == '"':
                i += 1; out.append(" ")
                while i < len(source):
                    if source[i] == "\\":
                        i += 2
                    elif source[i] == '"':
                        i += 1; break
                    else:
                        if source[i] == "\n": out.append("\n")
                        i += 1
            else:
                out.append(source[i]); i += 1
    return "".join(out)


def count(source):
    return len(TOKEN.findall(code_text(source)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--rev")
    args = parser.parse_args()
    if args.rev:
        paths = subprocess.check_output(
            ["git", "-C", str(args.root), "ls-tree", "-r", "--name-only", args.rev, "TCSlib"],
            text=True).splitlines()
        paths = [path for path in paths if path.endswith(".lean")]
    else:
        paths = [str(path.relative_to(args.root)) for path in (args.root / "TCSlib").rglob("*.lean")]
    total = 0
    for path in sorted(paths):
        source = subprocess.check_output(
            ["git", "-C", str(args.root), "show", args.rev + ":" + path], text=True
        ) if args.rev else (args.root / path).read_text()
        number = count(source)
        if number:
            print(f"{number:4d} {path}"); total += number
    print(f"TOTAL {total}")


if __name__ == "__main__":
    main()
