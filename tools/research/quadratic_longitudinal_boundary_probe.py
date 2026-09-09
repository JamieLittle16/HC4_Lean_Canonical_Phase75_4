"""Exact full-Hessian check for the surviving mixed quadratic boundary.

B and C are unrestricted symbolic functions of y,z,w. This verifies jet
identities; it does not reduce arbitrary terminal sources to this form.
"""
from itertools import permutations, product
import sympy as s

x, y, z, w, b, g, k = s.symbols('x y z w b g k')
B = s.Function('B')(y, z, w)
C = s.Function('C')(y, z, w)
H = s.hessian((b*z*w + g + k*y)*x**2 + B*x + C, (x, y, z, w))
entries = {(i, j, d): s.expand(H[i, j]).coeff(x, d)
           for i in range(4) for j in range(4) for d in range(3)}
assert all(s.expand(H[i,j] - sum(entries[i,j,d]*x**d for d in range(3))) == 0
           for i in range(4) for j in range(4))

def coefficient(n):
    out = 0
    for perm in permutations(range(4)):
        sign = (-1)**sum(perm[i] > perm[j] for i in range(4) for j in range(i+1, 4))
        for degrees in product(range(3), repeat=4):
            if sum(degrees) == n:
                out += sign*s.prod(entries[i, perm[i], degrees[i]] for i in range(4))
    return s.factor(out)

assert coefficient(6) == 4*b**2*k**2
assert s.expand(coefficient(5).subs(k, 0) - 2*b**2*(3*b*z*w-g)*s.diff(B,y,2)) == 0
p, q = s.Function('p')(z,w), s.Function('q')(z,w)
pz, pw = s.diff(p,z), s.diff(p,w)
expected = 2*b**2*(3*b*z*w-g)*s.diff(C,y,2) + b*(
    4*b*w**2*pw**2 - 4*b*w*z*pw*pz - 4*b*w*p*pw +
    4*b*z**2*pz**2 - 4*b*z*p*pz + b*p**2 + 4*g*pw*pz)
actual = coefficient(4).subs(k,0).subs(B,y*p+q).doit()
assert s.expand(actual-expected) == 0
assert s.expand(s.diff(actual,y)-2*b**2*(3*b*z*w-g)*s.diff(C,y,3)) == 0
print('PASS: exact x^6, x^5, x^4 identities with unrestricted lower source jets')
print('Conditional consequence for b != 0: k=0, B_yy=0, C_yyy=0')
print('No arbitrary-terminal quadratic-degree reduction or contradiction is asserted.')
