# Phase 87 changelog

## 87.1

Compile repairs in `LogarithmicInfinityCertificate.lean`:

- imported `HC4.Polynomial.AutonomousODEQuadraticRigidity` for the existing
  Euler natural-degree upper bound;
- normalised the top-coefficient index using the reduced-source degree equality;
- replaced an invalid `dvd_zero` inference with direct simplification of the
  canonical zero logarithmic source;
- replaced the predecessor-degree arithmetic step with a direct strict-degree
  proof from the vanished top coefficient.

No theorem statement changed.
