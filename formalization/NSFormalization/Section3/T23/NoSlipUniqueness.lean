import NSFormalization.Section3.T23.DifferenceEnergy

/-! Public entry point for no-slip velocity uniqueness.

`noSlip_uniqueness_box` proves U7 for the Spec's open Euclidean boxes.
`noSlip_uniqueness_of_ibp` proves the full conclusion under the explicit scalar
boundary identity `IBP Ω`. Its regular-level-domain instance remains the sole
analytic residual; see `research/T23/SPEC_ISSUES.md`, G1.

The canonical domain vocabulary and raw solution record are in `DomainSolution`.
-/
