"""The families of Theorem 8.6 (two rows of cells), checked on real edge sets.

A path from (0,0) to (a,2) is the pair (i, i') of the columns of its two
North steps, 0 <= i <= i' <= a.  oneclass(a) is the family of size
floor(a/2)+3 with pairwise common-edge counts of the parity of a; polyB(a)
(a odd) is an even family of size floor((5a-1)/4); polyC(a) (a even) is an
odd family of size floor((5a-2)/4).  Running the file checks them for
2 <= a <= 60.
"""
def edges(a,p):
    i,ii=p; E=set()
    for x in range(i): E.add(('h',x,0))
    E.add(('v',i,0))
    for x in range(i,ii): E.add(('h',x,1))
    E.add(('v',ii,1))
    for x in range(ii,a): E.add(('h',x,2))
    return E
def check(a,F,par):
    assert len(set(F))==len(F)
    for p in F: assert 0<=p[0]<=p[1]<=a
    Es={p:edges(a,p) for p in F}
    return all(len(Es[p]&Es[q])%2==par for p in F for q in F if p!=q)
def oneclass(a):
    e=2*(a//2)
    return [(k,k) for k in range(0,a+1,2)]+[(0,1),(e-1,e)]
def polyB(a): # a odd, even family
    return [(2*j,2*j+1) for j in range(0,(a-1)//2)]+[(s,s+3) for s in range(0,a-4,4)]+[(o,a) for o in range(1,a+1,2)]
def polyC(a): # a even, odd family
    return [(2*j+1,2*j+2) for j in range(0,(a-2)//2)]+[(s,s+3) for s in range(1,a-4,4)]+[(e,a) for e in range(0,a+1,2)]

def main():
    ok=True
    for a in range(2,61):
        F=oneclass(a); 
        if not (check(a,F,a%2) and len(F)==a//2+3): print("oneclass fail",a); ok=False
        if a%2==1:
            F=polyB(a)
            if not (check(a,F,0) and len(F)==(5*a-1)//4): print("B fail",a,len(F),(5*a-1)//4); ok=False
        else:
            F=polyC(a)
            if not (check(a,F,1) and len(F)==(5*a-2)//4): print("C fail",a,len(F),(5*a-2)//4); ok=False
    print("ok" if ok else "fail")


if __name__ == "__main__":
    main()
