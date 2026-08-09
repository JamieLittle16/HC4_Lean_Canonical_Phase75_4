# Phase 93.52 — Integral kernel blow-up

This phase formalises the coefficient-level integrality statement in the
handwritten kernel blow-up lemma.

## Main constructor

For a chosen source coordinate `kernel` and natural slope `q`, assume every
source-monomial coefficient `c_d(τ)` of a polynomial family `P` is divisible
by

    τ^(q * d(kernel)).

Lean chooses the quotient coefficients and reconstructs the transformed
polynomial as the finite sum

    Ptilde = sum_d monomial d (quotient_d).

The theorem

    integralKernelBlowupFamily_isIntegralKernelBlowup

proves for every exponent `d`

    coeff_d(P)
      = τ^(q * d(kernel)) * coeff_d(Ptilde).

Thus the formal substitution `T -> τ^(-q) T` is represented by an honest
polynomial family over `K[τ]`; no Laurent coefficients are introduced.

The patch also proves that no new source monomials are introduced and that
coefficients of kernel degree zero are unchanged.

## Moving sections

`kernelBlowupSection` implements the integral point transformation

    a_kernel -> τ^q a_kernel,

with all other coordinates unchanged.

At positive slope, the blown-up kernel coordinate reduces to zero on the
special fibre.

## Remaining bridge

The next phase should prove the evaluation/derivative covariance identity:

    family collision for P
      ->
    family collision for Ptilde at the blown-up sections.

After that, Phase 93.51 already transports the collision to the special
fibre and Phase 93.48 supplies strict global restart termination.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
