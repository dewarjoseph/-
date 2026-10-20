"""
Second independent audit script: frame-assignment controls, canonical plaquette curvature at levels 1-4,
the Spin(4) obstruction-matrix arbitrariness test, and the soldered-Laplacian gauge-consistency test.
Run from the repository root:  python3 -I audit/controls_plaquettes_spin4_solder_audit.py
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from independent_clifford_q8_audit import *  # noqa: F401,F403
import numpy as np, collections, itertools

ACHIRAL={k:(0,1,2) for k in FR30}
CANON={'0':(0,1,2),(0,0,0):(0,1,2),(0,0,1):(0,2,1),(0,1,0):(0,2,1),(0,1,1):(0,1,2),(1,0,0):(0,2,1),(1,0,1):(0,1,2),(1,1,0):(0,1,2)}
def summary(frames,lvl):
    tiles=tiles_at_level(frames,lvl); owner,edges=panel_edges(tiles); n=len(tiles)
    links=[clifford_link(tiles[a][0],tiles[b][0],nf) for a,b,nf,_,_ in edges]
    hol=fundamental_cycle_holonomies(n,edges,links)
    cnt=collections.Counter(q8label(h) for h in hol); ncyc=len(hol)
    nontriv=ncyc-cnt['+1']; tr0=sum(v for k,v in cnt.items() if k not in('+1','-1'))
    H=np.zeros((2*n,2*n),complex)
    for (a,b,_,_,_),C in zip(edges,links):
        H[2*a:2*a+2,2*a:2*a+2]+=np.eye(2); H[2*b:2*b+2,2*b:2*b+2]+=np.eye(2); H[2*a:2*a+2,2*b:2*b+2]-=C; H[2*b:2*b+2,2*a:2*a+2]-=C.conj().T
    ev=np.linalg.eigvalsh(H)
    dets=[round(np.linalg.det(t[0])) for t in tiles]
    return dict(V=n,E=len(edges),cycles=ncyc,nontriv_pct=round(100*nontriv/ncyc,1),tr0_pct=round(100*tr0/ncyc,1),min_ev=round(ev[0],4),hol=generated_subgroup(hol),dets=collections.Counter(dets))
print("CONTROLS vs monograph Table (level 1):")
for name,fr in [("ACHIRAL (M=D_s, det -1 allowed)",ACHIRAL),("CANONICAL_HOMO",CANON),("FR30",FR30)]:
    print(" ",name, summary(fr,1))
print("FR30 level 2:", summary(FR30,2)); print("FR30 level 3:", summary(FR30,3))

print("\nCANONICAL PLAQUETTE CURVATURE BY LEVEL (tree-independent, gauge-invariant up to conjugacy)")
def plaquette_stats(lvl):
    tiles=tiles_at_level(FR30,lvl); owner,edges=panel_edges(tiles)
    cubes=set(owner)
    def link_cubes(c1,c2):
        a,b=owner[c1],owner[c2]
        if a==b: return np.eye(2,dtype=complex)
        d=(np.array(c2)-np.array(c1)).astype(int)
        return clifford_link(tiles[a][0],tiles[b][0],d)
    cnt=collections.Counter(); mixed=0; total=0
    for c in cubes:
        for (i,j) in [(0,1),(1,2),(0,2)]:
            ei=np.zeros(3,int); ei[i]=1; ej=np.zeros(3,int); ej[j]=1
            c1=tuple(np.array(c)+ei); c2=tuple(np.array(c)+ei+ej); c3=tuple(np.array(c)+ej)
            if c1 in cubes and c2 in cubes and c3 in cubes:
                total+=1
                if len({owner[c],owner[c1],owner[c2],owner[c3]})>1:
                    mixed+=1; cnt[q8label(link_cubes(c,c1)@link_cubes(c1,c2)@link_cubes(c2,c3)@link_cubes(c3,c))]+=1
    nontriv=mixed-cnt['+1']; tr0=sum(v for k,v in cnt.items() if k not in('+1','-1'))
    return total,mixed,dict(cnt),round(100*nontriv/mixed,2),round(100*tr0/mixed,2),round(100*cnt['-1']/mixed,2)
for lvl in (1,2,3,4):
    t,m,c,p,q,r=plaquette_stats(lvl)
    print(f" level {lvl}: plaquettes={t} inter-tile={m} dist={c}\n          nontrivial={p}%  Tr=0: {q}%  W=-1: {r}%")

print("\nSPIN(4) 'OBSTRUCTION MATRIX' ARBITRARINESS TEST")
import sympy as sp
U4=[v for v in itertools.product((0,1),repeat=4) if v!=(1,1,1,1)]
def boundary_panels():
    out=[]
    for u in U4:
        for mu in range(4):
            for s in (-1,1):
                nb=list(u); nb[mu]+=s
                if tuple(nb) not in U4: out.append((u,mu,s))
    return sorted(out)
pk=boundary_panels(); print(" boundary 3-cubes:",len(pk))
def build_M(mult,off):
    rows=[]
    for idx in range(64):
        ua,mua,sa=pk[idx%len(pk)]; ub,mub,sb=pk[(idx*mult+off)%len(pk)]
        na=[0]*4; na[mua]=sa; nb=[0]*4; nb[mub]=sb
        row=[]
        for bidx,(mu,nu) in enumerate([(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]):
            w=na[mu]*nb[nu]-na[nu]*nb[mu]
            if w==0 and idx%6==bidx: w=1 if (idx//6)%2==0 else -1
            row.append(w)
        rows.append(row)
    return sp.Matrix(rows)
M=build_M(7,3); G=M.T*M
print(" repo pairing (idx*7+3): rank",M.rank()," det Gram",G.det(), " equals stored 21414742:", G.det()==21414742)
for mult,off in [(5,1),(11,2),(13,9),(1,0)]:
    M2=build_M(mult,off); print(f" alternative arbitrary pairing (idx*{mult}+{off}): rank {M2.rank()}, det Gram {(M2.T*M2).det()}")
print(" NOTE: rows pair panel idx with panel (idx*7+3) mod 64 and fill zero wedges with +-1 by idx parity; no frame assignment pi: U4->S4 enters.")

print("\nSOLDERED LAPLACIAN: GAUGE-CONSISTENCY TEST (level 1)")
tiles=tiles_at_level(FR30,1); owner,edges=panel_edges(tiles); n=len(tiles)
W=collections.Counter(); Np=collections.defaultdict(lambda: np.zeros((3,3)))
for a,b,nf,_,_ in edges:
    u,v=min(a,b),max(a,b); W[(u,v)]+=1; ax=int(np.argmax(nf)); Np[(u,v)][ax,ax]+=1
def assemble(mode):
    D=np.zeros((3*n,3*n))
    for (u,v),w in W.items():
        Mu,Mv=tiles[u][0].astype(float),tiles[v][0].astype(float); N=Np[(u,v)]
        if mode=='repo':   # as in src/chair44/solder_laplacian.py
            duu=w*np.eye(3)+Mu.T@N@Mu; dvv=w*np.eye(3)+Mv.T@N@Mv; off=-(w*np.eye(3)+Mu.T@N@Mv)
        else:              # covariant: every coupling transported with the same connection V_uv = Mu^T Mv
            duu=Mu.T@(w*np.eye(3)+N)@Mu; dvv=Mv.T@(w*np.eye(3)+N)@Mv; off=-Mu.T@(w*np.eye(3)+N)@Mv
        D[3*u:3*u+3,3*u:3*u+3]+=duu; D[3*v:3*v+3,3*v:3*v+3]+=dvv; D[3*u:3*u+3,3*v:3*v+3]+=off; D[3*v:3*v+3,3*u:3*u+3]+=off.T
    return D
for mode in ('repo','covariant'):
    D=assemble(mode); ev=np.linalg.eigvalsh(D)
    print(f" {mode:10s}: trace={D.trace():.0f} rank={np.linalg.matrix_rank(D,tol=1e-9)} lowest eigenvalues={np.round(ev[:4],6)}")
# check: covariant kernel = pure-gauge sections x_a = M_a^T y
D=assemble('covariant')
for y in np.eye(3):
    x=np.concatenate([tiles[a][0].T@y for a in range(n)]); print("  covariant D @ (M_a^T y):", np.abs(D@x).max())
