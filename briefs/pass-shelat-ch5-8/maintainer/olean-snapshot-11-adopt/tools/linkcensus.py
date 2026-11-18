"""linkcensus.py (lstat; symlinks skipped) <snap> <tree>...: for every .olean of <snap>: its link count, and which of the named trees hold the
same inode at the same relative path. Reports how many of <snap>'s inodes are held only by <snap> (deleting <snap>
frees them) and how many links lie outside <snap> and the named trees (other trees, e.g. jobs' cp -al copies)."""
import sys, os
snap, trees = sys.argv[1], sys.argv[2:]
n = only = shared_new = outside = sl = 0; held = {t: 0 for t in trees}; freed = 0; uniq = []
for r, ds, fs in os.walk(snap):
    for f in fs:
        p = os.path.join(r, f); rel = os.path.relpath(p, snap); st = os.lstat(p)
        if os.path.islink(p): sl += 1; continue
        n += 1
        c = 1
        for t in trees:
            q = os.path.join(t, rel)
            try:
                s2 = os.lstat(q)
                if s2.st_ino == st.st_ino and s2.st_dev == st.st_dev: held[t] += 1; c += 1
            except FileNotFoundError: pass
        if st.st_nlink == 1: only += 1; freed += st.st_size; uniq.append(rel)
        outside += st.st_nlink - c
print(f'{snap}: regular files {n}; symlinks skipped {sl}; link count 1 (held only here): {only}, {freed} bytes {uniq[:10]}')
for t in trees: print(f'  same inode at same path in {t}: {held[t]}')
print(f'  links elsewhere (not this tree, not the named trees, any path): {outside}')
