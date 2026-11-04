#!/bin/bash
# Test the landed file: elaboration, audit (axioms, walk), the maximal seal (sealed/unsealed),
# freeze, code identity with the head, regions, docs and lint.  One elaboration at a time.
R=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/nf-fill
SP=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
OL=$SP/oleans-leqc3; cd $R
shasum -a 256 land/NDNormalForm.lean > out/20-land-sha.txt
bash scripts/elab.sh $R/wt-head $OL $R/land/NDNormalForm.lean out/20a-land-elab.txt
python3 -I scripts/tacargs.py land/NDNormalForm.lean 45 720 out/aux-land-tacargs.tsv out/aux-land-ids.txt > /dev/null
python3 -I scripts/mkaudit.py land/NDNormalForm.lean scripts/audit_tail.lean.txt scripts/kinds_tail.lean.txt scripts/sorry_tail.lean.txt out/aux-land-ids.txt probe/NFLandAudit.lean
bash scripts/elab.sh $R/wt-head $OL $R/probe/NFLandAudit.lean out/20b-land-audit.out
mkdir -p probe/land; python3 -I scripts/mkseal.py land/NDNormalForm.lean out/05c-alldefs.txt probe/land/
bash scripts/elab.sh $R/wt-head $OL $R/probe/land/NFSeal_sealed.lean out/20c-land-seal-sealed.out
bash scripts/elab.sh $R/wt-head $OL $R/probe/land/NFSeal_unsealed.lean out/20d-land-seal-unsealed.out
python3 -I scripts/sealsum.py out/20c-land-seal-sealed.out out/20d-land-seal-unsealed.out out/05c-alldefs.txt out/06c-reached-defs.txt > out/20e-land-seal-summary.txt
{ echo "## declfreeze base -> landed"; python3 -I scripts/declfreeze.py src/base.lean land/NDNormalForm.lean exists_codeNDTM_accepts_linear
  echo "## declfreeze head -> landed"; python3 -I scripts/declfreeze.py src/head.lean land/NDNormalForm.lean exists_codeNDTM_accepts_linear
  echo "## code identical head vs landed (comments stripped)"; python3 -I scripts/codeonly.py src/head.lean land/NDNormalForm.lean
  echo "## target code"; python3 -I scripts/targetcmp.py src/base.lean land/NDNormalForm.lean 'theorem exists_codeNDTM_accepts_linear' | head -3
  echo "## regions base -> landed"; python3 -I scripts/regions.py src/base.lean land/NDNormalForm.lean | grep -E '^(insert|replace|delete)|added lines|over 100|consecutive'
  echo "## docs"; python3 -I scripts/doccheck.py src/base.lean land/NDNormalForm.lean | grep -E 'without|over 20 lines without|campaign-like|head [0-9]+: \['
  echo "## lint"; bash scripts/lint_run.sh $R/wt-head $R/land/NDNormalForm.lean | grep -E 'lint copies|NDNormalForm|FAIL,|findings|exit'; rm -rf scripts/lintroot
} > out/20f-land-checks.txt 2>&1
