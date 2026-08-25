import HC4.Newton.GeneralFourBlockSchur

/-!
# General four-block compatibility import

The canonical `GeneralFourBlock` structure and its denominator-cleared Schur
identities live in `GeneralFourBlockSchur`.  Some of the older closing stack
imports the historical umbrella module `HC4.Newton.GeneralFourBlock`; keep this
thin re-export so the full A18 final-assembly dependency graph is buildable.

No definitions or theorems are duplicated here.
-/
