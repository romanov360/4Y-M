"""varpi per observable for su2bp4d output (jackknife, 20 blocks), pure Python. usage: analyze4d.py files..."""
import sys, json
NOBS=9; names=[f'W{w}_{t}' for w in (1,2,3) for t in ('k0all','kx1','kx4')]
def est(rows, n, V):
    out=[]
    for o in range(NOBS):
        num=sum(r[o] for r in rows)/len(rows)
        f=[complex(r[NOBS+2*o],r[NOBS+2*o+1]) for r in rows]; m=sum(f)/len(f)
        var=sum(abs(x-m)**2 for x in f)/len(f)
        out.append(num/(n**4*var/V))
    return out
for fn in sys.argv[1:]:
    hdr=dict(kv.split('=') for kv in open(fn).readline()[2:].split()); L=int(hdr['L']); n=int(hdr['n']); V=L**4
    A=[[float(x) for x in l.split()[1:]] for l in open(fn) if l.startswith('C')]
    if len(A)<40: continue
    nb=20; bs=len(A)//nb; A=A[:bs*nb]
    full=est(A,n,V); reps=[est(A[:i*bs]+A[(i+1)*bs:],n,V) for i in range(nb)]
    err=[((nb-1)/nb*sum((r[o]-sum(x[o] for x in reps)/nb)**2 for r in reps))**0.5 for o in range(NOBS)]
    print(json.dumps(dict(D=4,L=L,beta=float(hdr['beta']),n=n,s=int(hdr['s']),nconf=len(A),n_over_L=n/L,
        varpi={k:[a,b] for k,a,b in zip(names,full,err)})))
