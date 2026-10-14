#!/bin/zsh
# Regenerates logs/arm-fill-freeze.log. Read-only on the checkout.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
W=$S/wt-t2; G=$S/gate-arm; B=$G/evidence/before
AL="TQBF_mem_PSPACE,TQBF_PSPACEHard,TQBF_PSPACEComplete,NL_eq_coNL,NSPACE_compl_eq,compl_PATH_mem_NL,PATH_NLComplete,PATH_mem_NL,PSPACE_eq_NPSPACE,compile_correct"
L=$G/logs/arm-fill-freeze.log
SP=TCSlib/Complexity/SpaceComplexity
{
echo "# arm-fill-freeze: statement freeze of the 8 modified files, 069cde82 (before) vs 8c23f3bc (after; = tip $(git -C $W rev-parse --short HEAD) for these files)"
echo "# before copies: audits/evidence/arm-fill/before/<path>.txt (git show 069cde82:<path>)"
echo
echo "## Part A. Maintainer tool tools/declfreeze.py <before> <after> <authorized list>"
echo "## authorized list (the brief's expected filled targets): $AL"
echo "## note: declfreeze's 'body change' covers docstring and/or proof (its chunk starts at the docstring)"
for f in $(cat $G/work/modified.txt); do echo "### $f"; python3 -I $S/tools/declfreeze.py $B/$f.txt $W/$f $AL; echo "rc=$?"; done
echo
echo "## Part B. Independent comparison scripts/freeze2.py (statement = header to first depth-0 ':='; doc = the /-- -/ block directly above; body = the rest; sorry = comment-stripped token count)"
for f in $(cat $G/work/modified.txt); do echo "### $f"; python3 -I $G/scripts/freeze2.py $B/$f.txt $W/$f; echo "rc=$?"; done
echo
echo "## Part C. Comment-stripped code identity (tools/codeonly.py; then scripts/codediff.py ignoring added import lines). Full code-only diffs: evidence/modified-codeonly.diff.txt"
for f in $(cat $G/work/modified.txt); do echo "### $f"; printf 'codeonly.py: '; python3 -I $S/tools/codeonly.py $B/$f.txt $W/$f; python3 -I $G/scripts/codediff.py $B/$f.txt $W/$f --ignore-added-imports | head -2; done
echo
echo "## Part D. The three relocated publics: ConfigGraph.lean at 069cde82 vs ExpTime.lean at 8c23f3bc (scripts/moved.py)"
python3 -I $G/scripts/moved.py $B/$SP/ConfigGraph.lean.txt $W/$SP/ExpTime.lean NSPACE_subset_exp_dtime,NL_subset_P,polyTimeReducible_of_mem_NL; echo "rc=$?"
echo
echo "## Part D2. References to the three names outside ConfigGraph.lean (git grep, .lean files)"
for r in 069cde82 8c23f3bc; do echo "### at $r"; git -C $W grep -n -E 'NSPACE_subset_exp_dtime|NL_subset_P\b|polyTimeReducible_of_mem_NL' $r -- '*.lean' | /usr/bin/grep -v ":TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:"; done
echo "### importers of ConfigGraph at 069cde82 (module-path references)"; git -C $W grep -n 'import TCSlib.Complexity.SpaceComplexity.ConfigGraph' 069cde82 -- '*.lean'
echo "### importers of ExpTime at 8c23f3bc"; git -C $W grep -n 'import TCSlib.Complexity.SpaceComplexity.ExpTime' 8c23f3bc -- '*.lean'
echo
echo "## Part E. Docstring diffs and citation tags of every changed declaration (scripts/freeze2.py with names)"
python3 -I $G/scripts/freeze2.py $B/TCSlib/Complexity/ClassPSPACE/TQBF.lean.txt $W/TCSlib/Complexity/ClassPSPACE/TQBF.lean TQBF_mem_PSPACE,TQBF_PSPACEHard,TQBF_PSPACEComplete | sed -n '/^=====/,$p'
python3 -I $G/scripts/freeze2.py $B/$SP/Logspace/ImmermanSzelepcsenyi.lean.txt $W/$SP/Logspace/ImmermanSzelepcsenyi.lean NL_eq_coNL,NSPACE_compl_eq,compl_PATH_mem_NL | sed -n '/^=====/,$p'
python3 -I $G/scripts/freeze2.py $B/$SP/Logspace/Path.lean.txt $W/$SP/Logspace/Path.lean PATH_mem_NL,PATH_NLComplete | sed -n '/^=====/,$p'
python3 -I $G/scripts/freeze2.py $B/$SP/Savitch.lean.txt $W/$SP/Savitch.lean PSPACE_eq_NPSPACE | sed -n '/^=====/,$p'
python3 -I $G/scripts/freeze2.py $B/$SP/Machines/Compile.lean.txt $W/$SP/Machines/Compile.lean compile_correct | sed -n '/^=====/,$p'
} > $L 2>&1
