import HC4.Polynomial.HessianDeterminant

/-!
# Hessian compatibility import

The project Hessian definitions are canonically available through
`HC4.Polynomial.HessianDeterminant`.  Some restored Lake dependency metadata
still references the historical module path `HC4.Polynomial.Hessian`; retain
this thin import shim so cached and clean builds resolve the same API.

No declarations are introduced here.
-/
