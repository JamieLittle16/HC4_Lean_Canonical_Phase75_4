# Testing Phase 50

From the extracted project directory:

```bash
chmod +x verify.sh
./verify.sh
```

The new modules are:

- `HC4/Polynomial/WeightBounds.lean`
- `HC4/Polynomial/DerivativeBounds.lean`
- `HC4/Polynomial/TopProduct.lean`
- `HC4/Polynomial/MaximalHessianInitial.lean`
- `HC4/MongeAmpere/MaximalInitial.lean`
- `HC4/MongeAmpere/FirstContactMaximal.lean`

A successful run should include at least these new audit names:

```text
HC4.Polynomial.sub_initialForm_isWeightLT
HC4.Polynomial.IsWeightLE.pderiv
HC4.Polynomial.IsWeightLT.pderiv
HC4.Polynomial.initialForm_prod_eq_prod
HC4.Polynomial.initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
HC4.Polynomial.hessianDeterminant_initialForm_eq_zero_of_eq_zero
HC4.MongeAmpere.hasInitialHessianDeterminant_of_isWeightLE
HC4.MongeAmpere.maximal_initial_hessianDeterminant_eq_zero
HC4.MongeAmpere.maximal_initial_hessianDeterminant_eq_zero_of_zero
HC4.MongeAmpere.first_contact_scaled_hessianDeterminant_eq_zero_of_isWeightLE
HC4.MongeAmpere.first_contact_hessianDeterminant_eq_zero_of_isWeightLE
```

The authoritative status is the exit code and final message of `verify.sh`.
Phases 46–50 are not marked verified until the complete run succeeds locally.
