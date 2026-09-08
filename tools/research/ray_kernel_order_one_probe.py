"""Exact symbolic first-order calculation for the level-9 model.
Requires SymPy; coefficient extraction is not yet certified in Lean.
Includes the entire kernel-compatible weight-8 first layer and arbitrary
weight-7 and weight-6 later layers. This does not classify all terminal rays.
"""
import sympy as s
from itertools import product,permutations
x,y,z,w=s.symbols('x y z w');u=3*x+4*z*w*y
a,b,c,d,e=s.symbols('a b c d e')
F0=x*(z*w)**3+y*(z*w)**4
G1=u**2*(a*z*z+b*z*w+c*w*w)+y*u**2*(d*z+e*w)
def weighted(deg,prefix):
 return sum(s.Symbol(f'{prefix}_{i}_{j}_{k}')*x**i*y**j*z**k*w**(deg-3*i-j-k) for i in range(deg//3+1) for j in range(deg-3*i+1) for k in range(deg-3*i-j+1))
H={k:s.hessian(f,(x,y,z,w)).subs(y,0).applyfunc(s.expand) for k,f in [(0,F0),(1,G1),(2,weighted(7,'g2')),(3,weighted(6,'g3'))]}
entries={(k,i,j,d):M[i,j].coeff(x,d) for k,M in H.items() for i in range(4) for j in range(4) for d in range(3)}
assert all(s.expand(M[i,j]-sum(entries[k,i,j,d]*x**d for d in range(3)))==0 for k,M in H.items() for i in range(4) for j in range(4))
ps=list(permutations(range(4)));signs={p:(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4)) for p in ps}
def coeff(n,j):
 ans=0
 for ks in product(H,repeat=4):
  if sum(ks)!=n:continue
  for ds in product(range(3),repeat=4):
   if sum(ds)!=j:continue
   for p in ps:
    fs=[entries[ks[i],i,p[i],ds[i]] for i in range(4)]
    if all(f!=0 for f in fs):ans+=signs[p]*s.prod(fs)
 return s.factor(s.expand(ans))
q=s.symbols('q0:5')
def ordinary(deg,prefix):return sum(s.Symbol(f'{prefix}{i}')*z**i*w**(deg-i) for i in range(deg+1))
G1+=u*ordinary(5,'p5_')+ordinary(8,'p8_')+y*u*sum(q[i]*z**(4-i)*w**i for i in range(5))+y*ordinary(7,'q7_')
H[1]=s.hessian(G1,(x,y,z,w)).subs(y,0).applyfunc(s.expand)
entries={(k,i,j,d):M[i,j].coeff(x,d) for k,M in H.items() for i in range(4) for j in range(4) for d in range(3)}
C24=coeff(2,4)
print('top kernel term',C24,flush=True)
assert s.expand(C24-729*w**4*z**4*(17*d**2*z**2+30*d*e*w*z+17*e**2*w**2))==0
H[1]=H[1].subs({d:0,e:0}).applyfunc(s.expand)
entries={(k,i,j,d):M[i,j].coeff(x,d) for k,M in H.items() for i in range(4) for j in range(4) for d in range(3)}
C22=s.expand(coeff(2,2).subs({d:0,e:0}));C33=s.expand(coeff(3,3).subs({d:0,e:0}))

assert C22.coeff(z,12).coeff(w,4) == 1053*q[0]**2
assert C22.coeff(z,4).coeff(w,12) == 1053*q[4]**2
R2=s.expand(C22.subs({q[0]:0,q[4]:0}))
R3=s.expand(C33.subs({q[0]:0,q[4]:0}))
for A,Q,zz,ww in [(a,q[1],10,6),(c,q[3],6,10)]:
    assert s.expand(R2.coeff(z,zz).coeff(w,ww)-81*Q*(Q-32*A))==0
for A,Q,zz,ww in [(a,q[1],9,3),(c,q[3],3,9)]:
    assert s.expand(R3.coeff(z,zz).coeff(w,ww)-972*A*(64*A*A-8*A*Q+Q*Q))==0
print('PASS: outer kernel coefficients and both boundary quadratic terms are excluded')
print('The middle coefficient b and later layers are not eliminated by this test.')
