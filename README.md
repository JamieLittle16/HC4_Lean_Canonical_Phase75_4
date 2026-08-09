# HC4 Lean Phase 93.77 minimal patch

Apply over green Phase 93.76.1:

```bash
cd ~/HC4/lean
unzip -o ~/Downloads/HC4_Lean_Phase93_77_DefectRetainingDepartureFrontier_MinimalPatch.zip
cp -a HC4_Lean_Phase93_77_DefectRetainingDepartureFrontier/. HC4_Lean_Canonical_Phase75_2/
cd HC4_Lean_Canonical_Phase75_2
./verify.sh
```

Added:
- `HC4/Valuation/DefectRetainingDepartureFrontier.lean`

Modified:
- `HC4.lean`
