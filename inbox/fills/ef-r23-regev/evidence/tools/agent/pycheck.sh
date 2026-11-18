#!/usr/bin/env bash
# pycheck.sh <file.py>... (tools-agent, fill ef-r23-regev): syntax-check Python files with python3 -I, writing no
# bytecode (builtin compile(); `python3 -I -m py_compile` would write __pycache__ next to the tools).
rc=0; for f in "$@"; do python3 -I -c "import sys; compile(open(sys.argv[1],encoding='utf-8').read(), sys.argv[1], 'exec')" "$f" && echo "SYNTAX-OK $f" || { echo "SYNTAX-FAIL $f"; rc=1; }; done; exit $rc
