import sys
def sub(path, old, new, count=1):
    s=open(path).read()
    assert s.count(old)==count, (path, s.count(old), old[:120])
    s=s.replace(old,new); open(path,'w').write(s)
