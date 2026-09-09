"""Eliminate the mixed first-order term using full-source constraints.

The imported probe retains the complete first kernel layer and arbitrary
later layers. The two previously uncontrolled terms are coefficients of
x^2*y and x*y^2*z*w. The full-source x^6/x^5 equations force them to vanish
when the mixed quadratic coefficient is nonzero.
"""
from pathlib import Path
import runpy
import sympy as s

here = Path(__file__).parent
runpy.run_path(str(here / 'quadratic_longitudinal_boundary_probe.py'))
data = runpy.run_path(str(here / 'ray_kernel_order_one_probe.py'))
a, b, c, z, w = (data[n] for n in ('a', 'b', 'c', 'z', 'w'))
q = data['q']
# Verify the original first-layer ansatz covers every weight-eight monomial
# that is affine in the kernel coordinate after the invertible u-change.
U = s.Symbol('U')
x, y = data['x'], data['y']
normal = s.Poly(s.expand(data['G1'].subs(x, (U-4*z*w*y)/3)), U,y,z,w)
expected = {(i,j,l,8-3*i-j-l) for j in (0,1)
            for i in range((8-j)//3+1) for l in range(8-3*i-j+1)}
assert set(normal.monoms()) == expected and len(expected) == 33
vanished = {a:0, c:0, q[1]:0, q[3]:0}
second = s.expand(data['R2'].subs(vanished)).coeff(z,8).coeff(w,8)
third = s.expand(data['R3'].subs(vanished)).coeff(z,6).coeff(w,6)
k = s.Symbol('g2_2_1_0')  # coefficient of x^2*y in the whole source
r = s.Symbol('g2_1_2_1')  # coefficient of x*y^2*z*w
assert s.expand(second + 9*(288*b*q[2]-12*r+32*k+27*q[2]**2)) == 0
assert s.expand(third + 54*(-1152*b**3-144*b*b*q[2]+32*b*k+9*b*q[2]**2-2*k*q[2])) == 0
assert s.expand(second.subs({k:0,r:0}) + 81*q[2]*(32*b+3*q[2])) == 0
assert s.expand(third.subs({k:0,r:0}) + 486*b*(q[2]**2-16*b*q[2]-128*b*b)) == 0
# The two branches of the quadratic equation give nonzero multiples of b^2.
bracket = q[2]**2-16*b*q[2]-128*b*b
assert s.expand(bracket.subs(q[2],0)) == -128*b*b
assert s.expand(bracket.subs(q[2],-s.Rational(32,3)*b)) == s.Rational(1408,9)*b*b
print('PASS: the balanced second/third equations force the mixed coefficient b=0')
print('Scope: level-nine quadratic-longitudinal model, not arbitrary terminal rays.')
