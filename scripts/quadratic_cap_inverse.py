#!/usr/bin/env python3
"""Exact inverse constructor for quadratic-transverse Hessian potentials over QQ.

For a polynomial F(x, y_1,...,y_n), total y-degree <= 2, and nonzero
constant det Hess F, construct inverse of the full gradient and verify
BOTH compositions symbolically. This is an executable adversarial check,
not a replacement for the universal paper proof or Lean formalization.

Requires: python3 -m pip install sympy
Usage: python scripts/quadratic_cap_inverse.py --demo
       python scripts/quadratic_cap_inverse.py \
         --expr 'x*u + v*w + x**7*v**2' --transverse u,v,w
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from typing import Sequence
import sympy as sp


@dataclass
class Certificate:
    potential: sp.Expr
    variables: tuple[sp.Symbol, ...]
    outputs: tuple[sp.Symbol, ...]
    inverse: tuple[sp.Expr, ...]
    determinant: sp.Rational
    branch: str
    witness: dict[str, str]


def norm(a: sp.Expr) -> sp.Expr:
    return sp.cancel(sp.factor(a))


def is_zero(v: sp.Expr) -> bool:
    return norm(v) == 0


def poly_QQ(expr: sp.Expr, variables: Sequence[sp.Symbol]) -> sp.Poly:
    return sp.Poly(norm(expr), *variables, domain=sp.QQ)


def assert_polynomial(expr: sp.Expr, variables: Sequence[sp.Symbol], label: str) -> None:
    try:
        poly_QQ(expr, variables)
    except (sp.PolynomialError, sp.CoercionFailed) as e:
        raise ValueError(f"{label} is not a QQ-polynomial: {expr}") from e


def check_zero_matrix(M: sp.Matrix, label: str) -> None:
    for i in range(M.rows):
        for j in range(M.cols):
            if not is_zero(M[i, j]):
                raise AssertionError(f"{label}[{i},{j}] = {M[i,j]} != 0")


def substitute(expr: sp.Expr, mapping: dict[sp.Symbol, sp.Expr]) -> sp.Expr:
    return norm(expr.subs(mapping, simultaneous=True))


def construct_inverse(F: sp.Expr, x: sp.Symbol,
                      ys: Sequence[sp.Symbol], *, verify=True) -> Certificate:
    """Build the exact polynomial inverse of the gradient, or reject the input."""
    ys = tuple(ys)
    n = len(ys)
    if n < 1 or x in ys or len(set(ys)) != n:
        raise ValueError("Supply one x and distinct transverse y variables")
    variables = (x, *ys)
    P = poly_QQ(F, variables)
    F = P.as_expr()
    if any(sum(powers[1:]) > 2 for powers, _ in P.terms()):
        raise ValueError("Transverse degree exceeds two")
    H = sp.hessian(F, variables)
    delta_expr = norm(H.det(method='domain-ge'))
    delta_poly = poly_QQ(delta_expr, variables)
    if delta_poly.total_degree() != 0 or is_zero(delta_expr):
        raise ValueError(f"Hessian determinant is not a nonzero scalar: {delta_expr}")
    delta = sp.Rational(delta_expr)
    z0 = {y: sp.Integer(0) for y in ys}
    b = sp.Matrix([norm(sp.diff(F, y).subs(z0)) for y in ys])
    C = sp.Matrix([[norm(sp.diff(F, yi, yj).subs(z0))
                    for yj in ys] for yi in ys])
    bp = b.diff(x)
    D = norm(C.det(method='domain-ge'))
    px = sp.Symbol('out_x')
    py = sp.Matrix([sp.Symbol(f'out_{y.name}') for y in ys])
    outputs = (px, *tuple(py))
    Fx = sp.diff(F, x)
    witnesses = {"det_HessF": str(delta), "det_C": str(D)}

    if not is_zero(D):
        branch = "REGULAR"
        M = C.inv().applyfunc(norm)
        check_zero_matrix((C * M - sp.eye(n)).applyfunc(norm), "CM-I")
        for i in range(n):
            for j in range(n):
                assert_polynomial(M[i, j], (x,), "derived inverse transverse Hessian")
        if not is_zero(D.diff(x)):
            raise AssertionError("det C must be constant by the Riccati equation")
        y_of_x = (M * (py - b)).applyfunc(norm)
        g = substitute(Fx, dict(zip(ys, list(y_of_x))))
        slope = norm(delta / D)
        if not is_zero(sp.diff(g, x) - slope):
            raise AssertionError("Partial-Legendre fibre derivative is not constant")
        g0 = norm(g.subs(x, 0))
        x_inverse = norm((D / delta) * (px - g0))
        yi = [substitute(t, {x: x_inverse}) for t in y_of_x]
        witnesses.update({"constant_fibre_slope": str(slope), "g_p_zero": str(g0)})
    else:
        branch = "SINGULAR"
        w = (C.adjugate() * bp).applyfunc(norm)
        if all(is_zero(t) for t in w):
            raise AssertionError("Missing nonzero kernel witness")
        if not is_zero((bp.T * w)[0] + delta):
            raise AssertionError("Kernel pairing is not -delta")
        check_zero_matrix((C * w).applyfunc(norm), "Cw")
        check_zero_matrix((C.diff(x) * w).applyfunc(norm), "C'w")
        check_zero_matrix(w.diff(x).applyfunc(norm), "w'")
        k = next(i for i, wi in enumerate(w) if not is_zero(wi))
        I = [i for i in range(n) if i != k]
        E = C.extract(I, I)
        detE = norm(E.det(method='domain-ge')) if I else sp.Integer(1)
        if is_zero(detE) or not is_zero(sp.diff(detE, x)):
            raise AssertionError("Complementary minor must be nonzero constant")
        E_inv = E.inv().applyfunc(norm) if I else sp.zeros(0, 0)
        beta = norm((w.T * b)[0].subs(x, 0))
        x_inverse = norm((beta - (w.T * py)[0]) / delta)
        yh = [sp.Integer(0)] * n
        if I:
            rhs = (py - b).extract(I, [0])
            recovered = (E_inv * rhs).applyfunc(norm)
            for j, idx in enumerate(I):
                yh[idx] = substitute(recovered[j], {x: x_inverse})
        gx0 = substitute(Fx, {x: x_inverse, **dict(zip(ys, yh))})
        shift = norm((gx0 - px) / delta)
        yi = [norm(yh[i] + shift * w[i]) for i in range(n)]
        witnesses.update({
            "constant_kernel": str(list(w)),
            "kernel_pivot_index": str(k),
            "active_complement_det": str(detE),
            "linear_gradient_offset": str(beta),
        })

    inverse = (x_inverse, *yi)
    for i, expr in enumerate(inverse):
        assert_polynomial(expr, outputs, f"inverse coordinate {i}")
    if verify:
        grad = tuple(sp.diff(F, var) for var in variables)
        for i, (g, output) in enumerate(zip(grad, outputs)):
            if not is_zero(substitute(g, dict(zip(variables, inverse))) - output):
                raise AssertionError(f"gradient after inverse, coordinate {i}")
        for i, (f, var) in enumerate(zip(inverse, variables)):
            if not is_zero(substitute(f, dict(zip(outputs, grad))) - var):
                raise AssertionError(f"inverse after gradient, coordinate {i}")
    return Certificate(F, variables, outputs, inverse, delta, branch, witnesses)


def demonstration() -> None:
    x, u, v, w = sp.symbols('x u v w')
    cases = [
        ("degree_9_singular", x*u + v*w + x**7*v**2),
        ("nonconstant_regular_C", -x**2/2 + u*v - x*v**2/2 + w**2/2),
        ("quadratic", x*u + v*w),
        ("mixed_constant_kernel", x*(u+v) + (u-v)*w + x**4*(u-v)**2),
        ("regular_drifting_b", -(x**3+x**2)/2 + x*u - x**2*v
            + u*v - x*v**2/2 + w**2/2),
    ]
    for name, F in cases:
        cert = construct_inverse(F, x, (u, v, w))
        print(f"{name}: {cert.branch}, det={cert.determinant}; "
              "both compositions verified")
        print(dict(zip(cert.variables, cert.inverse)))

    # Check the dimension-independent claim beyond four total variables.
    cert1 = construct_inverse(x*u + x**8, x, (u,))
    assert cert1.branch == "SINGULAR"
    z = sp.symbols('z')
    cert5 = construct_inverse(x*u + v*w + z**2/2 + x**6*v**2,
                              x, (u, v, w, z))
    assert cert5.determinant == 1
    print("transverse n=1 and n=4: both directions verified")

    for name, F in [
        ("cubic_cap", x*u + v*w + u*v**2 + x**7*v**3),
        ("nonconstant_det", x**3*u**2 + v*w),
    ]:
        try:
            construct_inverse(F, x, (u, v, w))
        except ValueError:
            print(f"{name}: rejected as expected")
        else:
            raise AssertionError(f"{name}: invalid input accepted")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expr")
    parser.add_argument("--longitudinal", default="x")
    parser.add_argument("--transverse", default="u,v,w")
    parser.add_argument("--demo", action="store_true")
    parser.add_argument("--no-check", action="store_true",
                        help="Skip both symbolic composition checks")
    args = parser.parse_args()
    if args.demo or not args.expr:
        demonstration()
        return
    names = [args.longitudinal,
             *[a.strip() for a in args.transverse.split(',')]]
    symbols = sp.symbols(' '.join(names))
    F = sp.sympify(args.expr, locals=dict(zip(names, symbols)))
    cert = construct_inverse(F, symbols[0], symbols[1:],
                             verify=not args.no_check)
    print(f"BRANCH={cert.branch}; det Hess={cert.determinant}")
    print("WITNESSES", cert.witness)
    for v, inv in zip(cert.variables, cert.inverse):
        print(f"  {v} = {inv}")
    if not args.no_check:
        print("VERIFIED both polynomial compositions")


if __name__ == "__main__":
    main()
