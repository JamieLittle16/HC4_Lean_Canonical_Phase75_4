# Phase 93.41 — well-founded mixed-departure interface

This patch strengthens `HC4.Newton.MixedDepartureAdapter` at the exact
boundary needed by the global restart assembly.

The previous green file already proved:

* the preterminal mixed-vs-affine/separated dichotomy;
* rank-one -> rank-two `RepairProgress` at fixed finite complexity;
* the exact identity `det Hess_(U,V) P = -(P_UV)^2` in the mixed branch;
* strict decrease of the numerical repair measure for the promoted state.

Phase 93.41 packages those facts into two consumer-facing theorems:

* `preterminal_departure_strictRepair_or_affineSeparated`
* `preterminal_departure_strictRepair_with_source_or_affineSeparated`

The first says that a first preterminal departure is either already in the
explicit affine/separated channel, or is a certified strict step in the
existing finite repair relation together with a strict decrease of its
existing measure.

The second retains the exact negative-square determinant identity and its
nonvanishing certificate in the same result.

No new termination measure, axiom, or global restart hypothesis is added.
The remaining global task is to construct/consume the actual restart chain;
this patch makes the mixed-departure leg ready for that assembly.
