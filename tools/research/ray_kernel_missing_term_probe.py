"""Correct the scope of the earlier order-2 kernel calculation.
Exact SymPy diagnostics only; not a Lean source coefficient theorem.
The full first layer includes k*y*u^2, omitted from the original ansatz.
All permitted later layers from the earlier probe are retained here.
This records why the lower coefficients alone were insufficient. The higher
coefficient in ray_kernel_top_coefficient_probe.py now eliminates k first.
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

k=s.symbols('k');G2+=k*y*u**2
H[2]=s.hessian(G2,(x,y,z,w)).subs(y,0).applyfunc(s.expand)
entries={(order,i,j,d):M[i,j].coeff(x,d) for order,M in H.items() for i in range(4) for j in range(4) for d in (0,1)}
Q3=sum(q[i]*z**(3-i)*w**i for i in range(4))
C43=coeff(4,3)
assert s.expand(C43-1944*k*w**4*z**4*(Q3-8*w*z*(A*z+B*w)))==0
outer=s.factor(coeff(4,2).coeff(z,10).coeff(w,4))
assert s.expand(outer-648*(q[0]**2-3*k*s.Symbol('q6_6')))==0
print('Full first layer [t^4*x^3]:',s.factor(C43))
print('Outer quadratic coefficient:',outer)
print('PASS: the extra kernel term changes the former pure-square equation')
