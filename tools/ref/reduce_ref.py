from functools import reduce as fold
B,L=256,8
def block(xs,op):
    lanes=[]
    for j in range(min(L,len(xs))):
        a=xs[j]
        for v in xs[j+L::L]: a=op(a,v)
        lanes.append(a)
    lanes+= [None]*(L-len(lanes))
    def comb(a,b):
        if a is None: return b
        if b is None: return a
        return op(a,b)
    while len(lanes)>1:
        lanes=[comb(lanes[i],lanes[i+1]) for i in range(0,len(lanes),2)]
    return lanes[0]
def red(xs,op):
    ps=[block(xs[i:i+B],op) for i in range(0,len(xs),B)]
    while len(ps)>1:
        ps=[op(ps[i],ps[i+1]) if i+1<len(ps) else ps[i] for i in range(0,len(ps),2)]
    return ps[0]
sub=lambda a,b:a-b
s=lambda a,b:"(%s %s)"%(a,b)
for n in (7,9): print(n, red(["x%d"%i for i in range(n)],s))
for n in (1,3,7,8,9,257):
    xs=[1.0]*n; print(n,"ones",red(xs,sub),fold(sub,xs))
for n in (7,8,9):
    xs=[float(2**i) for i in range(n)]; print(n,"pow2",red(xs,sub),fold(sub,xs))
xs=[1.0]*257; xs[256]=3.0; print(red(xs,sub))
