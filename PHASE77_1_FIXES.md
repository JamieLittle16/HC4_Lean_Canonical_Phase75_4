# Phase 77.1 fixes

This is a proof-engineering repair of the Phase-77 candidate.  No theorem
statement or mathematical hypothesis is changed.

Changes in `HC4/Polynomial/AutonomousODEQuadraticRigidity.lean`:

1. Normalise the `congrArg (fun p => p.coeff n)` hypotheses with explicit
   `change` statements before coefficient rewrites.  This fixes the two
   pattern-recognition failures at the least exponent and top degree.
2. Remove the unavailable `Polynomial.coeff_mul_of_nat_degree_le` calls.
   Instead prove that `E(phi)` and `E(E(phi))` retain natural degree `D` from
   their nonzero top coefficients, and use the established
   `Polynomial.coeff_mul_degree_add_degree` theorem.
3. In the `A = -1` branch, convert the scalar relation to a degree equality
   through `sub_eq_zero`, avoiding the brittle `linear_combination` cast goal.
4. Replace the recursive final `simp` by one explicit commutativity rewrite.
5. In the `J >= 2` branch, avoid `mod_cast` across truncated natural
   subtraction.  Prove `(J : K) - 1 != 0` from `J != 1`, use `Nat.cast_sub`
   under `1 <= J`, and derive the contradiction from the nonzero cast of a
   positive natural number.

The Phase-76 rank-three Hessian bridge and all previously green files are
unchanged.
