"""Exact symbolic coefficient checks for a rank-three model ray.

Requires SymPy. These checks are not Lean proofs and do not cover all terminal
rays. All weight-5 and weight-3 later corrections and every kernel-compatible
weight-6 correction are included, as are all affine-in-kernel first-layer terms.
The weight-8 Hessian layer is assumed zero (globally first Hessian order 2).
IMPORTANT: the coefficient of the additional kernel term y*u^2 is assumed
zero. See ray_kernel_missing_term_probe.py for the nonzero branch.
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
H0=s.hessian(F0,(x,y,z,w))
v=s.Matrix([4*z*w,-3,0,0])
assert all(s.expand(e)==0 for e in H0*v)
assert s.expand(H0.extract([1,2,3],[1,2,3]).det())!=0
G2=(A*z+B*w)*u**2+y*u*sum(q[i]*z**(3-i)*w**i for i in range(4))+u*ordinary(4,'p4_')+ordinary(7,'p7_')+y*ordinary(6,'q6_')
assert s.expand((v.T*s.hessian(G2,(x,y,z,w))*v)[0])==0
H={k:s.hessian(f,(x,y,z,w)).subs(y,0).applyfunc(s.expand) for k,f in [(0,F0),(2,G2),(3,kernel(6,'g3')),(4,weighted(5,'g4')),(6,weighted(3,'g6'))]}
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
C4=coeff(4,2); print('computed full C4',flush=True)
C6=coeff(6,3); print('computed full C6',flush=True)
print('C4 extreme q0:',s.factor(C4.coeff(z,10).coeff(w,4)))
print('C4 extreme q3:',s.factor(C4.coeff(z,4).coeff(w,10)))
C4r=s.expand(C4.subs({q[0]:0,q[3]:0}));C6r=s.expand(C6.subs({q[0]:0,q[3]:0}))
for zz,ww in [(8,6),(6,8)]:print('C4',zz,ww,s.factor(C4r.coeff(z,zz).coeff(w,ww)))
for zz,ww in [(6,3),(3,6)]:print('C6',zz,ww,s.factor(C6r.coeff(z,zz).coeff(w,ww)))

assert C4.coeff(z,10).coeff(w,4) == 648*q[0]**2
assert C4.coeff(z,4).coeff(w,10) == 648*q[3]**2
assert s.expand(C4r.coeff(z,8).coeff(w,6)+2592*A*q[1]) == 0
assert s.expand(C4r.coeff(z,6).coeff(w,8)+2592*B*q[2]) == 0
assert s.expand(C6r.coeff(z,6).coeff(w,3)-972*A*(64*A**2+8*A*q[1]+q[1]**2)) == 0
assert s.expand(C6r.coeff(z,3).coeff(w,6)-972*B*(64*B**2+8*B*q[2]+q[2]**2)) == 0
# The general-exponent scalar certificate, proved separately in Lean.
m,a,b=s.symbols('m a b')
T=8*(m+1)**2*a**2+4*(m+1)*a*b+(m-1)*b**2
Q=8*a*m**2-8*a*m-16*a+b*(m**2-4*m+3)
assert s.expand((m-3)**2*T-Q*((m-3)*b-4*(m+1)*a)
                -8*(m+1)**2*(m-1)**2*a**2) == 0
print('PASS: all six extremal coefficients and the elimination certificate')

# Conditional common-monomial endpoint: the full source would need to have
# this form. This identity does not establish that missing support condition.
fxx,fxy,fyy,fxh,fyh,fhh,fh=s.symbols('fxx fxy fyy fxh fyh fhh fh')
M=s.Matrix([[fxx,fxy,w*fxh,z*fxh],
            [fxy,fyy,w*fyh,z*fyh],
            [w*fxh,w*fyh,w*w*fhh,fh+z*w*fhh],
            [z*fxh,z*fyh,fh+z*w*fhh,z*z*fhh]])
D3=fxx*fyy*fhh+2*fxy*fxh*fyh-fxx*fyh**2-fyy*fxh**2-fxy**2*fhh
assert s.expand(M.det()+fh*(fh*(fxx*fyy-fxy**2)+2*z*w*D3))==0
print('PASS: conditional common-monomial determinant factorization')
