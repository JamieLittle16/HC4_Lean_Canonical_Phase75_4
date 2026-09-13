"""Exact symbolic test of the full-to-binary determinant implication.

This is NOT an HC4 counterexample or a model of the retained rank-three ray.
It tests only whether exact Hessian-one, reverse Rees, positive weights,
quadratic clock margin and Euler identities imply the binary-layer vanishing.
Run with Python and SymPy. These assertions are not Lean certificates.
"""
import sympy as s

x, y, z, w, t = s.symbols('x y z w t')
coords = (x, y, z, w)
F = x*y + z*w + x**3*z**3
weights = (2, 2, 2, 2)
level = 12
profile_weight = weights[0]
defect = 4*level - 2*sum(weights)
assert 2*level < defect
assert s.expand(s.det(s.hessian(F, coords))) == 1
ray = s.expand(t**level * F.subs(
    {v: v/t**a for v, a in zip(coords, weights)}, simultaneous=True))
assert ray == t**8*x*y + t**8*z*w + x**3*z**3
assert s.expand(s.det(s.hessian(ray, coords))) == t**defect
assert s.expand(t*s.diff(ray, t) + sum(
    a*v*s.diff(ray, v) for v, a in zip(coords, weights)) - level*ray) == 0
binary = s.expand(ray.subs(
    {v: t**a*v for v, a in zip(coords[1:], weights[1:])}, simultaneous=True))
assert binary == t**10*x*y + t**12*z*w + t**6*x**3*z**3
binary_clock = 4*level - 2*profile_weight
full = s.expand(s.det(s.hessian(binary, coords)))
assert full == t**binary_clock
assert s.expand(t*s.diff(binary, t) + profile_weight*x*s.diff(binary, x)
                - level*binary) == 0
# Exactly the three Euler-scaled rows used by binaryProfileHessianDetFamily.
h00 = t**2*s.diff(binary, t, 2)
h01 = t*x*s.diff(binary, t, x)
h11 = x**2*s.diff(binary, x, 2)
profile = s.expand(h00*h11 - h01*h01)
order = 2*level - profile_weight*2
assert order == 20 and order < binary_clock
assert full.coeff(t, order) == 0
assert profile.coeff(t, order) == -100*x**2*y**2
# Explicitly record why this does NOT instantiate the actual terminal package.
assert s.hessian(ray.subs(t, 0), coords).rank() == 2
print('source det Hess = 1; reverse Rees defect =', defect)
print('binary full det Hess =', full)
print('binary profile layer at order', order, '=', profile.coeff(t, order))
print('Excluded hypothesis: the leading source is rank two, not the retained rank-three ray.')
