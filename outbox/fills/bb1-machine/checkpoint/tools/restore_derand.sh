#!/usr/bin/env bash
# restore_derand.sh (derand review: restore.sh plus removal of the Mathlib symlink overlay and its one compiled olean)
# restore.sh <tree> <backup-dir> <evidence-dir>: put the base oleans back (tree/backed-up.txt, hashes checked),
# delete the oleans of modules new since eff2dcd0 (tree/new-oleans.txt) and every probe olean under PlProbe/,
# remove the empty directories left behind (listed first), snapshot and compare with tree/snapshot-pre.txt.
set -u
T=$1; BK=$2; E=$3; L=$E/restore/restore-log.txt; mkdir -p $E/restore; : > $L
(cd $BK && sha256sum -c $E/tree/backed-up.txt) | grep -vc ': OK$' | sed 's/^/backup hash failures: /' >> $L
while read h f; do cp -p $BK/$f $T/$f; echo "RESTORED $f" >> $L; done < $E/tree/backed-up.txt
while read m; do if [ -f $T/$m.olean ]; then echo "DELETED $(sha256sum < $T/$m.olean | cut -d' ' -f1) $m.olean" >> $L; rm $T/$m.olean; fi; done < $E/tree/new-oleans.txt
if [ -d $T/Mathlib ]; then echo "DELETED-MATHLIB-OVERLAY symlinks $(find $T/Mathlib -type l | wc -l) files $(find $T/Mathlib -type f | wc -l)" >> $L; find $T/Mathlib -type f -exec sha256sum {} + | sed "s|^|DELETED-MATHLIB-FILE |" >> $L; rm -r $T/Mathlib; fi
if [ -d $T/PlProbe ]; then find $T/PlProbe -type f | sort | while read f; do echo "DELETED-PROBE $(sha256sum < $f | cut -d' ' -f1) ${f#$T/}" >> $L; done; rm -r $T/PlProbe; fi
find $T -type d -empty | sort > $E/restore/empty-dirs-before-prune.txt
find $T -type d -empty -delete; find $T -type d -empty -delete
python3 -I $E/tools/snapshot.py $T $E/tree/snapshot-post.txt
cmp $E/tree/snapshot-pre.txt $E/tree/snapshot-post.txt && echo "SNAPSHOT EQUAL" || echo "SNAPSHOT DIFFERS"
