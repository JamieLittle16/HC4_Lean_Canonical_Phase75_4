# Formalisation status after Phase 78 candidate

## Previously green

* Phase 75.2: complementary-edge rigidity, endpoint form.
* Phase 76: rank-three logarithmic Hessian -> autonomous scalar equation.
* Phase 77.3: quadratic autonomous coefficient rigidity and the two terminal
  coefficient cases used in rank-three rigidity.

## Phase 78 candidate

Exact local pole-order coefficients at a translated nonzero root:

* `coeff_n_shiftedEuler_X_pow_succ_mul`;
* `coeff_two_n_shiftedEtaNumerator_X_pow_succ_mul`;
* corresponding nonvanishing theorems.

## Still missing for full rank-three edge rigidity

1. assemble these local coefficients into the statement that an autonomous
   polynomial right-hand side has degree exactly two;
2. connect the rank-three rational function to that polynomial right-hand
   side (pole removal / denominator constancy, reusing RationalRigidity);
3. assemble the unequal-degree rank-three cases with the already-green pencil
   terminal cases;
4. equal-degree rank-three branch still depends on the GN/torus step.


### Phase 78.1 candidate
The initial Phase 78 build exposed one local rewrite-order failure in the shifted Euler factorisation. Phase 78.1 repairs only that proof. This patch is not kernel-verified until the pinned local `./verify.sh` run passes.
