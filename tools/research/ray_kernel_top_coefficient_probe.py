"""Resolve the omitted y*u^2 term using the highest longitudinal coefficient.
SymPy checks, not a complete Lean source adapter. Includes the full weight-7
kernel layer, all weight-6 kernel-compatible G3, arbitrary weight-5 G4 and
weight-3 G6. The first positive Hessian order is assumed to be 2. Order 5
cannot contribute at order 4 because there are no negative parameter orders.
"""
import sympy as s
from itertools import product, permutations
x,y,z,w,A,B=s.symbols('x y z w A B'); u=3*x+4*z*w*y
q=s.symbols('q0:4')
def ordinary(deg,prefix):
    return sum(s.Symbol(f'{prefix}{i}')*z**i*w**(deg-i) for i in range(deg+1))
def kernel(deg,prefix):
    return s.expand(sum(u**i*ordinary(deg-3*i,f'{prefix}p{i}_') for i in range(deg//3+1)) + y*sum(u**i*ordinary(deg-1-3*i,f'{prefix}q{i}_') for i in range((deg-1)//3+1)))
def weighted(deg,prefix):
    return sum(s.Symbol(f'{prefix}_{i}_{j}_{k}')*x**i*y**j*z**k*w**(deg-3*i-j-k) for i in range(deg//3+1) for j in range(deg-3*i+1) for k in range(deg-3*i-j+1))
F0=x*(z*w)**3+y*(z*w)**4
G2=(A*z+B*w)*u**2+y*u*sum(q[i]*z**(3-i)*w**i for i in range(4))+u*ordinary(4,'p4_')+ordinary(7,'p7_')+y*ordinary(6,'q6_')
H={k:s.hessian(f,(x,y,z,w)).applyfunc(s.expand) for k,f in [(0,F0),(2,G2),(3,kernel(6,'g3')),(4,weighted(5,'g4')),(6,weighted(3,'g6'))]}
for M in H.values():
 for e in M: assert e==0 or s.degree(e,x)<=1
entries={(k,i,j,d):M[i,j].coeff(x,d) for k,M in H.items() for i in range(4) for j in range(4) for d in (0,1)}
ps=list(permutations(range(4))); signs={p:(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4)) for p in ps}
def coeff(n,j):
 ans=0
 for ks in product(H,repeat=4):
  if sum(ks)!=n:continue
  for ds in product((0,1),repeat=4):
   if sum(ds)!=j:continue
   for p in ps:
    fs=[entries[ks[i],i,p[i],ds[i]] for i in range(4)]
    if all(f!=0 for f in fs):ans+=signs[p]*s.prod(fs)
 return s.expand(ans)

k=s.symbols('k');G2+=k*y*u**2
# Check completeness in the polynomial coordinates (u,y,z,w), including the
# affine kernel coordinate y. The change x=(u-4zwy)/3 is invertible.
U=s.symbols('U')
normal=s.Poly(s.expand(G2.subs(x,(U-4*z*w*y)/3)),U,y,z,w)
expected={(i,j,l,7-3*i-j-l) for j in (0,1) for i in range((7-j)//3+1) for l in range(7-3*i-j+1)}
assert set(normal.monoms())==expected and len(expected)==27
H[2]=s.hessian(G2,(x,y,z,w)).applyfunc(s.expand)
assert s.expand((s.Matrix([[4*z*w,-3,0,0]])*H[2]*s.Matrix([4*z*w,-3,0,0]))[0])==0
for M in H.values():
    for e in M: assert e==0 or s.degree(e,x)<=1
entries={(order,i,j,d):M[i,j].coeff(x,d) for order,M in H.items() for i in range(4) for j in range(4) for d in (0,1)}
top=coeff(4,4)
assert s.expand(top-14580*k*k*w**4*z**4)==0
print('PASS: complete 27-dimensional first kernel layer; full Hessians before y specialization')
print('[t^4*x^4] determinant =',s.factor(top))
print('Thus k=0 before the earlier six-coefficient calculation is applied.')
