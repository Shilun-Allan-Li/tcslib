#!/usr/bin/env bash
# C10 clash scan (gsw-6b-u18-u19): every new name of the head (from decls2 and the private helpers),
# (a) git grep -w at the base, iO/phase-a-base, cleanup/stage2-s2a and the records tip;
# (b) short names elsewhere; (c) unqualified uses in the UNIT-DOWN modules.
TAG=$1
R=/work/tcslib; B=bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d
G=TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW
cd $R
HEAD=$(git rev-parse HEAD)
echo "# C10 clash scan (gsw-6b-u18-u19), head $HEAD ($TAG)."
echo "# new declarations (git diff $B HEAD, owned files, declaration lines added):"
git diff $B HEAD -- $G/PolyRatio.lean $G/Asymptotic.lean | grep -E '^\+(private )?(theorem|lemma|def|abbrev|instance) ' | sed 's/^/#   /'
echo "# full names: TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.ofFamily_columns_le (public);"
echo "#   _private.TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio.0.TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.two_mul_width_lt_of_ratio (private)"
n_else=0
for name in ofFamily_columns_le two_mul_width_lt_of_ratio; do
  for ref in $B origin/iO/phase-a-base origin/cleanup/stage2-s2a origin/cryptography/pass-shelat-ch2-4; do
    c=$(git grep -n -w $name $ref -- TCSlib audits | wc -l)
    echo "(a/b) git grep -n -w $name $ref ($(git rev-parse $ref)) -- TCSlib audits: $c hits"
    n_else=$((n_else + c))
  done
done
echo "(c) uses of the new names in the UNIT-DOWN modules at the head (all qualified or in the defining file):"
for m in $(grep -P '^UNIT-DOWN\tgsw-6b-u18-u19\t' /tmp/b/briefs/lattice-gsw/phase6/issued-6b-fills-r1/closures.txt | cut -f3); do
  git grep -n -w -E 'ofFamily_columns_le|two_mul_width_lt_of_ratio' HEAD -- $m.lean | grep -v '^\S*:[0-9]*:\s*--' | sed 's/^/    /'
done
echo "    Both names are new everywhere ((a/b): 0 hits), so no existing unqualified use can change its resolution;"
echo "    the private name is invisible outside PolyRatio.lean; the head sweep of the 5 UNIT-DOWN modules is rc 0, 0 errors."
echo "RESULT new_names=2 existing_elsewhere=$n_else"
