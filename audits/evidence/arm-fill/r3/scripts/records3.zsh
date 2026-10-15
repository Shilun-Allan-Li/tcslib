#!/bin/zsh
# R2-2 and R2-6: where the maintainer's records commit put each named record at the tip, and what the
# tip's records still say about the payback items #101 has since landed (text search, git show only).
# usage: zsh records3.zsh <repo> <tip>
set -uo pipefail
REPO=$1; TIP=$2
show() { git -C $REPO show "${TIP}:$1" }
hit() { local f=$1; shift; print "## $f: $*"; show $f | /usr/bin/grep -n -E "$@" | cut -c1-180 | sed 's/^/  /'; print }
print "# arm-fill-r3-records: the R2-2 and R2-6 records at the tip $TIP (line numbers at the tip)"
hit machine-library-design.md '^## 14\.|^\| H(7|8|9|10|11|12|13) \|'
hit machine-library-design.md 'Accepted exception|Gate before reuse|direct importers and named transitive users|vword_whole₁. is at'
hit machine-library-design.md '^\| H(1|3|4|6) \|'
hit machine-library-design.md 'Bon26'
hit machine-library-design.md 'PR #92, merged'
hit machine-library-design.md 'historical: S1b stopped'
hit backlog.md '^\| MIG-(19|22) \|'
hit AroraBarakChapters3-4Plan.md '^\| \*\*B2 Configuration-graph simulation'
hit audits/arm-extensions-fill-r2-resolutions.md 'AxF6|AxF7|AxF8|AxARM'
print "# records that still describe #101's items as future work (to update after #101; text search)"
hit machine-library-design.md 'retires into .Turing\.Cfg\.InWindow. in the payback PR|D7 and .decChain. \(decided\)'
hit backlog.md 'net −938|net -938'
