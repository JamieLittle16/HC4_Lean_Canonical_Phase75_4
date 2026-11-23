import HC4.Polynomial.RankThreeCubicDetOnePrincipalCofactorKernelLine

/-!
# Compatibility import for the principal-cofactor kernel-line theorem

The original pivot-column proof duplicated the domain-level
principal-cofactor argument and used an ill-typed Pi.single term.
The canonical, source-neutral implementation is now
`RankThreeCubicDetOnePrincipalCofactorKernelLine`.

Keep this module as a compatibility import so callers of the old
module path receive the verified canonical results without
introducing duplicate theorem names.
-/
