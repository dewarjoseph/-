"""
Independent re-derivation of the Chair44 Clifford Q8 connection, written from the
mathematical definitions only (no imports from the repository).
Run from the repository root:  python3 -I audit/independent_clifford_q8_audit.py
"""
import itertools, collections, sys
import numpy as np
import sympy as sp

# ---------- 1. Substitution and FR30 frames ----------
U3 = [v for v in itertools.product((0,1), repeat=3) if v != (1,1,1)]
FR30 = {'0':(0,1,2),(0,0,0):(0,1,2),(0,0,1):(0,2,1),(0,1,0):(2,1,0),(0,1,1):(1,2,0),
        (1,0,0):(1,0,2),(1,0,1):(0,1,2),(1,1,0):(2,0,1)}
def perm_mat(p):
    M=np.zeros((3,3),dtype=int)
    for i in range(3): M[i,p[i]]=1
    return M
def tiles_at_level(frames, level):
    ops=[(perm_mat(frames['0']), np.array([1,1,1]))]
    for v in U3:
        Ds=np.diag([1-2*v[0],1-2*v[1],1-2*v[2]])
        ops.append((Ds@perm_mat(frames[v]), 4*np.array(v)))
    poses=[(np.eye(3,dtype=int), np.zeros(3,dtype=int))]
    for _ in range(level):
        poses=[(G@g, 2*T+G@t) for G,T in poses for g,t in ops]
    base=[np.array([2*u[0]+1,2*u[1]+1,2*u[2]+1]) for u in U3]
    out=[]
    for G,T in poses:
        cubes=frozenset(tuple((G@bc+2*T-1)//2) for bc in base)
        out.append((G,T,cubes))
    return out

def check_tiling(tiles, level):
    allc=collections.Counter(c for _,_,cs in tiles for c in cs)
    overlaps=sum(1 for c,n in allc.items() if n>1)
    N=2**(level+1)
    box=set(itertools.product(range(N),repeat=3))
    # supertile at level k is the chair [0,2N/2]^3 \ (N/2,N]^3 scaled: C = [0,N]^3 \ (N/2,N]^3
    target={c for c in box if not all(ci>=N//2 for ci in c)}
    return overlaps, set(allc)==target, len(allc), len(target)

# ---------- 2. Panel multigraph and Clifford links ----------
SIG=[np.array([[0,1],[1,0]],complex), np.array([[0,-1j],[1j,0]],complex), np.array([[1,0],[0,-1]],complex)]
def sdot(u): return sum(u[j]*SIG[j] for j in range(3))
def q8label(U):
    for name,mat in [('+1',np.eye(2)),('-1',-np.eye(2))]+[(f'{s}{n}', s_*1j*SIG[k]) for k,n in enumerate('ijk') for s,s_ in [('+',1),('-',-1)]]:
        if np.allclose(U,mat,atol=1e-9): return name
    return 'other'

def panel_edges(tiles):
    owner={c:a for a,(_,_,cs) in enumerate(tiles) for c in cs}
    edges=[]   # (a,b,n_f ambient from a to b, cube_a, cube_b)
    for c,a in owner.items():
        for ax in range(3):
            d=[0,0,0]; d[ax]=1
            c2=(c[0]+d[0],c[1]+d[1],c[2]+d[2])
            b=owner.get(c2)
            if b is not None and b!=a:
                n=np.zeros(3,int); n[ax]=1
                edges.append((a,b,n,c,c2))
    return owner, edges

def clifford_link(Ma,Mb,n):
    ua=Ma.T@n; ub=Mb.T@n
    return sdot(ua)@sdot(ub)

def fundamental_cycle_holonomies(ntiles, edges, links, root=0):
    adj=collections.defaultdict(list)
    for idx,(a,b,n,_,_) in enumerate(edges):
        adj[a].append((b,links[idx],idx)); adj[b].append((a,links[idx].conj().T,idx))
    parent={root:None}; T={root:np.eye(2,dtype=complex)}; tree=set(); q=[root]
    while q:
        u=q.pop(0)
        for v,C,idx in adj[u]:
            if v not in parent:
                parent[v]=u; tree.add(idx); T[v]=T[u]@C; q.append(v)
    hol=[]
    for idx,(a,b,n,_,_) in enumerate(edges):
        if idx in tree: continue
        hol.append(T[a]@links[idx]@T[b].conj().T)
    return hol

def generated_subgroup(elems):
    S={q8label(e) for e in elems}
    mats={q8label(e):e for e in elems}
    # closure
    changed=True
    while changed:
        changed=False
        for x in list(mats.values()):
            for y in list(mats.values()):
                l=q8label(x@y)
                if l not in mats: mats[l]=x@y; changed=True
    return sorted(mats)


def main():
    print("="*70); print("1. TILING / SUBSTITUTION CHECKS")
    for lvl in (1,2,3):
        tiles=tiles_at_level(FR30,lvl)
        ov,exact,ncubes,ntarget=check_tiling(tiles,lvl)
        print(f" level {lvl}: tiles={len(tiles)} cubes={ncubes} target={ntarget} overlaps={ov} exact_chair_supertile={exact}")
        for G,_,_ in tiles:
            assert (G.T@G==np.eye(3,dtype=int)).all() and round(np.linalg.det(G))==1

    print("\n"+"="*70); print("2. LEVEL-1 LAPLACIAN AND CHARACTERISTIC POLYNOMIAL (independent)")
    tiles=tiles_at_level(FR30,1)
    owner,edges=panel_edges(tiles)
    n=len(tiles); W=collections.Counter()
    for a,b,_,_,_ in edges: W[(min(a,b),max(a,b))]+=1
    L=sp.zeros(n,n)
    for (a,b),w in W.items():
        L[a,b]-=w; L[b,a]-=w; L[a,a]+=w; L[b,b]+=w
    print(" shared panels:",len(edges)," b1 = |E|-|V|+1 =",len(edges)-n+1)
    print(" L =",L.tolist())
    lam=sp.Symbol('lambda')
    cp=sp.factor((lam*sp.eye(n)-L).det())
    print(" charpoly:",cp)
    print(" matches claim:", sp.expand(cp-lam*(lam-24)*(lam**2-30*lam+207)*(lam**2-21*lam+99)**2)==0)

    print("\n"+"="*70); print("3. CLIFFORD CONNECTION: STRUCTURE THEOREMS CHECKED NUMERICALLY")
    links=[clifford_link(tiles[a][0],tiles[b][0],nf) for a,b,nf,_,_ in edges]
    print(" all links in Q8:", all(q8label(C)!='other' for C in links))
    print(" link value counts:", collections.Counter(q8label(C) for C in links))
    # spin lift of M in SO(3,Z): find U in SU(2) with U sigma_i U^dag = sum_j M_ji sigma_j  (i.e. U (sigma.v) U^dag = sigma.(Mv))
    def spin_lift(M):
        # via rotation vector
        from scipy.spatial.transform import Rotation as R
        rv=R.from_matrix(M.astype(float)).as_rotvec()
        th=np.linalg.norm(rv)
        if th<1e-12: return np.eye(2,dtype=complex)
        nvec=rv/th
        return np.cos(th/2)*np.eye(2)-1j*np.sin(th/2)*sdot(nvec)
    for a in range(n):
        U=spin_lift(tiles[a][0])
        for v in np.eye(3):
            assert np.allclose(U@sdot(v)@U.conj().T, sdot(tiles[a][0]@v))
    # Theorem: C_ab = U_a^dag (sigma.n) U_a U_b^dag (sigma.n) U_b   and ambient gauge  U_a C_ab U_b^dag = N_f V_ab N_f with V_ab = U_a U_b^dag
    ok1=ok2=True
    for (a,b,nf,_,_),C in zip(edges,links):
        Ua,Ub=spin_lift(tiles[a][0]),spin_lift(tiles[b][0]); N=sdot(nf)
        ok1 &= np.allclose(C, Ua.conj().T@N@Ua@Ub.conj().T@N@Ub)
        ok2 &= np.allclose(Ua@C@Ub.conj().T, N@(Ua@Ub.conj().T)@N)
    print(" C_ab = U_a^+ N_f U_a U_b^+ N_f U_b  :", ok1)
    print(" ambient gauge: U_a C_ab U_b^+ = N_f (U_a U_b^+) N_f  [face-normal-twisted spinor coboundary]:", ok2)
    # frame-change non-covariance: changing the frame at a single tile is NOT a gauge transformation
    Ra=perm_mat((1,2,0))  # even permutation, det +1; chair geometry invariant under coordinate permutations
    tiles_mod=list(tiles); G0,T0,c0=tiles_mod[3]; tiles_mod[3]=(G0@Ra,T0,c0)
    links_mod=[clifford_link(tiles_mod[a][0],tiles_mod[b][0],nf) for a,b,nf,_,_ in edges]
    hol0=fundamental_cycle_holonomies(n,edges,links); holm=fundamental_cycle_holonomies(n,edges,links_mod)
    print(" change frame of tile 3 by even permutation (geometry unchanged):")
    print("   holonomy traces before:", sorted(collections.Counter(int(round(np.trace(h).real)) for h in hol0).items()))
    print("   holonomy traces after :", sorted(collections.Counter(int(round(np.trace(h).real)) for h in holm).items()))
    print("   -> connection depends on frame decoration, not only on the point-set tiling:", 
          sorted(collections.Counter(q8label(h) for h in hol0).items())!=sorted(collections.Counter(q8label(h) for h in holm).items()))

    print("\n"+"="*70); print("4. HOLONOMY GROUP AND DISTRIBUTIONS BY LEVEL")
    for lvl in (1,2,3):
        tiles=tiles_at_level(FR30,lvl); owner,edges=panel_edges(tiles); n=len(tiles)
        links=[clifford_link(tiles[a][0],tiles[b][0],nf) for a,b,nf,_,_ in edges]
        hol=fundamental_cycle_holonomies(n,edges,links)
        cnt=collections.Counter(q8label(h) for h in hol)
        ncyc=len(hol); nontriv=ncyc-cnt['+1']; tr0=sum(v for k,v in cnt.items() if k not in ('+1','-1'))
        print(f" level {lvl}: |V|={n} |E|={len(edges)} b1={len(edges)-n+1} cycles={ncyc} nontrivial={nontriv} ({100*nontriv/ncyc:.1f}%) Tr0={tr0} ({100*tr0/ncyc:.1f}%) -1:{cnt['-1']}")
        print("    generated holonomy group:", generated_subgroup(hol), " (order", len(generated_subgroup(hol)),")")
        # adjoint (spin-1) image: Q8 -> SO(3) has image {1, R_x(pi),R_y(pi),R_z(pi)} = Z2 x Z2 ; count classes mod center
        cl=collections.Counter(q8label(h).strip('+-') for h in hol)
        print("    image mod center (Z2xZ2 classes):", dict(cl))

    print("\n"+"="*70); print("5. CANONICAL PLAQUETTE CURVATURE (56-cube graph, 4 cubes around each lattice edge)")
    tiles=tiles_at_level(FR30,1); owner,edges=panel_edges(tiles); n=len(tiles)
    Mof={c:tiles[a][0] for c,a in owner.items()}
    def link_cubes(c1,c2):
        a,b=owner[c1],owner[c2]
        if a==b: return np.eye(2,dtype=complex)
        d=np.array(c2)-np.array(c1)
        return clifford_link(tiles[a][0],tiles[b][0],d.astype(int))
    plaq=collections.Counter(); nplaq=0; mixed=0
    cubes=set(owner)
    for c in cubes:
        for (i,j) in [(0,1),(1,2),(0,2)]:
            ei=np.zeros(3,int); ei[i]=1; ej=np.zeros(3,int); ej[j]=1
            c1=tuple(np.array(c)+ei); c2=tuple(np.array(c)+ei+ej); c3=tuple(np.array(c)+ej)
            if c1 in cubes and c2 in cubes and c3 in cubes:
                tl={owner[c],owner[c1],owner[c2],owner[c3]}
                Wp=link_cubes(c,c1)@link_cubes(c1,c2)@link_cubes(c2,c3)@link_cubes(c3,c)
                nplaq+=1
                if len(tl)>1:
                    mixed+=1; plaq[q8label(Wp)]+=1
    print(f" plaquettes={nplaq}, plaquettes touching >1 tile={mixed}, curvature distribution on those: {dict(plaq)}")

    print("\n"+"="*70); print("6. SPECTRA: Clifford hopping Hamiltonian vs trivial (coboundary) connection, level 1")
    def hopping_H(n,edges,links):
        H=np.zeros((2*n,2*n),complex)
        for (a,b,_,_,_),C in zip(edges,links):
            H[2*a:2*a+2,2*a:2*a+2]+=np.eye(2); H[2*b:2*b+2,2*b:2*b+2]+=np.eye(2)
            H[2*a:2*a+2,2*b:2*b+2]-=C; H[2*b:2*b+2,2*a:2*a+2]-=C.conj().T
        return H
    tiles=tiles_at_level(FR30,1); owner,edges=panel_edges(tiles); n=len(tiles)
    links=[clifford_link(tiles[a][0],tiles[b][0],nf) for a,b,nf,_,_ in edges]
    Hc=hopping_H(n,edges,links); Ht=hopping_H(n,edges,[np.eye(2,dtype=complex)]*len(edges))
    evc=np.linalg.eigvalsh(Hc); evt=np.linalg.eigvalsh(Ht)
    print(" Clifford  spectrum:", np.round(evc,6))
    print(" trivial   spectrum:", np.round(evt,6))
    print(" Kramers pairs (Clifford):", all(abs(evc[i]-evc[i+1])<1e-10 for i in range(0,16,2)))
    Tm=np.kron(np.eye(n),1j*SIG[1])
    print(" T-symmetry  T H T^-1 = H with T = 1 x (i sigma_y K):", np.allclose(Tm@Hc.conj()@Tm.conj().T, Hc))
    # exact algebraic eigenvalues of the Clifford Hamiltonian via sympy on the 8x8 quaternionic (=16x16 complex) matrix
    Hs=sp.Matrix(np.rint(Hc.real).astype(int)+sp.I*np.rint(Hc.imag).astype(int))
    cpc=sp.factor((lam*sp.eye(16)-Hs).det())
    print(" Clifford Hamiltonian charpoly (exact):", cpc)


if __name__ == "__main__":
    main()
