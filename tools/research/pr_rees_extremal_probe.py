"""Exact local obstruction probe; not a terminal or an HC4 counterexample."""
import sympy as s
x,y,z,w,e=s.symbols('x y z w e')
v=(x,y,z,w)
h=z*w
u=2*x+3*h*y
F0=x*h**2+y*h**3
F=s.expand(F0+e*u**2)
D,r=7,3
# This is exactly a reverse weighted Rees family, not an arbitrary deformation.
f=F.subs(e,1)
assert s.expand(e**D*f.subs(dict(zip(v,(x/e**r,y/e,z/e,w/e))), simultaneous=True)-F)==0
assert s.expand(r*x*s.diff(F,x)+sum(t*s.diff(F,t) for t in (y,z,w))+e*s.diff(F,e)-D*F)==0
H=s.hessian(F,v)
H0=H.subs(e,0)
assert all(H0[i,j]==0 for i in (0,1) for j in (0,1))
assert s.expand(H0[0,2]*H0[1,3]-H0[0,3]*H0[1,2])==0
assert s.expand(H0.extract([2,3],[2,3]).det())!=0
# Both contact endpoints lie on the same affine rational support line.
assert s.Poly(F0,*v).monoms()==[(1,0,2,2),(0,1,3,3)]
# Columns: active Euler directions, longitudinal Euler, weighted Euler.
U=s.Matrix([[0,0,x,r*x],[0,0,0,y],[z,0,0,z],[0,w,0,w]])
J=U.T*H*U
a,b,d=J[0,0],J[0,1],J[1,1]
p,q,rr,ss=J[0,2],J[0,3],J[1,2],J[1,3]
xx,yy,zz=J[2,2],J[2,3],J[3,3]
A=s.expand(a*d-b*b)
SA=A*xx-d*p*p+2*b*p*rr-a*rr*rr
SB=A*yy-d*p*q+b*(p*ss+q*rr)-a*rr*ss
SC=A*zz-d*q*q+2*b*q*ss-a*ss*ss
B=s.expand(xx*SC+zz*SA-2*yy*SB+(p*ss-q*rr)**2)
E=lambda g:e*s.diff(g,e)
L=x*s.diff(F,x)
R=s.expand(xx*e**2*s.diff(F,e,2)-2*(D-1)*xx*E(F)+2*(D-r)*L*E(L)-E(L)**2)
core=s.expand(xx*zz-yy*yy-R)
detH=s.factor(H.det())
assert s.expand(detH-576*e**3*h*(6*e*y+h)*u**3)==0
assert s.expand(B-A*R-A*core-(x*y*z*w)**2*detH)==0
coeff=lambda g:s.expand(g).coeff(e,2).coeff(x,4)
assert s.expand(p*ss-q*rr)==0
assert coeff(xx*SC+zz*SA-2*yy*SB)==-81792*y**2*z**6*w**6
assert coeff(A*R)==-50688*y**2*z**6*w**6
assert coeff(R)==64
assert coeff(B-A*R)==-31104*y**2*z**6*w**6
assert coeff(A*core)==coeff(B-A*R)
print('PASS: exact Rees identity, Euler identity, affine block, mixed determinant, ray support')
print('PASS: nonzero coefficient [e^2 x^4](B-A*R) =',s.factor(coeff(B-A*R)))
print('det Hess F =',detH)
print('SCOPE: determinant clock fails at order 3; no actual terminal is constructed.')

# The first failed clock equation cannot be repaired by later Rees layers
# while preserving the preceding equation. Only the x-linear portion of
# layer 2 contributes to these two coefficients; see the companion note.
a,b,c,d,j,k=s.symbols('a b c d j k')
A2=a*y*y+b*y*z+c*y*w+d*z*z+j*z*w+k*w*w
H2=s.hessian(F+e**2*x*A2,v)
from itertools import permutations
truncated=0
for perm in permutations(range(4)):
    term=s.Integer((-1)**sum(perm[i]>perm[j] for i in range(4) for j in range(i+1,4)))
    for i in range(4):
        poly=s.Poly(s.expand(term*H2[i,perm[i]]),e)
        term=sum(co*e**power[0] for power,co in poly.terms() if power[0]<=3)
    truncated+=term
truncated=s.expand(truncated)
assert s.expand(truncated.coeff(e,2).coeff(x,2)-32*a*h**4)==0
assert s.expand(truncated.coeff(e,3).coeff(x,3)-192*(24-a)*h**2)==0
print('PASS: clock order 2 forces a=0; clock order 3 forces a=24.')

# qN minimality is only at longitudinal N; earlier lower-index layers survive.
lam=s.symbols('lam')
F9=x*h**3+y*h**4+lam*e**2*x*h**2+e**3*(3*x+4*h*y)**2
assert s.expand(3*x*s.diff(F9,x)+sum(vv*s.diff(F9,vv) for vv in (y,z,w))+e*s.diff(F9,e)-9*F9)==0
assert all(s.expand(F9).coeff(e,j).coeff(x,2)==0 for j in range(3))
assert s.expand(F9).coeff(e,3).coeff(x,2)==9
assert s.expand(F9).coeff(e,2).coeff(x,1)==lam*h**2
L9=x*s.diff(F9,x)
core9=s.expand(x**2*s.diff(F9,x,2)*(72*F9-6*L9)-36*L9**2)
pivot9=s.expand(z**2*w**2*(s.diff(F9,z,2)*s.diff(F9,w,2)-s.diff(F9,z,w)**2))
assert s.expand(pivot9*core9).coeff(e,6).coeff(x,4).coeff(lam,3)==2592*h**9
print('PASS: qN=3 minimality at N=2 allows lower-index layers and a nonzero quartic convolution term.')
