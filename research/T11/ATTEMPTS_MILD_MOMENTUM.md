

## 6. Discharging the force-side persistence (codex review point 1)

The codex review (`REVIEW_327-T11-U9d2b-momentum.md`, gap 1) rejected the lane
for carrying `hF : PersistenceInput T F` alongside the single allowed
`PersistenceInput T u`.  It is now a **theorem**:

```lean
theorem persistenceInput_force_of_smooth {T : ℝ} {g : SpaceTimeField}
    {F : ℝ → PeriodicSobolev 3} (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hFg : IsPeriodicSobolevPath 3 g F) : PersistenceInput T F
```

Proof: `CriterionBridge.exists_periodicDatum_smooth (m : ℝ)` gives an order-`m`
datum of `g(t,·)` at each `t` (smooth + periodic slice), `choose` turns that into
a path, `T10/ForcePaths.continuous_datum_path m hg` makes the path continuous
(it needs the datum property at *every* real time, which `choose` supplies), and
both physical coefficients are `periodicFourierCoeff (fun x ↦ (g(t,x) i : ℂ)) k`
by `torusPhysicalCoeff_eq` applied to `hG t` and to `hFg t ht.1`.

Consequently **no declaration of this module assumes `PersistenceInput` for the
force path any more**.  Every theorem that used `hF` now takes the three ordinary
data facts `(hg : ContDiff ℝ ∞ g)`, `(hgp : IsPeriodicOn univ g)`,
`(hFg : IsPeriodicSobolevPath 3 g F)` instead — which the momentum theorems
already assumed, so their hypothesis count went *down*:
`persistence_force_decay`, `mildDerivCoeff_decay`, `mildDerivCoeff_summable`,
`mildTimeDerivative_contDiff`, `mildTimeDerivative_coeff`,
`torusPhysicalVelocity_hasDerivAt`, `temporalDerivative_torusPhysicalVelocity`,
`temporalDerivative_torusPhysicalVelocity'`, `momentum_of_pressure`,
`projected_of_pressure`, `momentum_of_mildPressure`, `projected_of_mildPressure`.
`PersistenceInput T u` remains the single named input, exactly as the brief
allows.  Declaration count 66 → 67.

Review gap 2 (the joint `ContDiffOn ℝ ∞` fields) is the documented residual of
§3.1/§3.2 and is being closed by a separate lane; gap 3's negative control is
kept as `research/T11/probes/rev327_mutation.lean`, updated to the new
signatures so that its single error is still exactly the flipped diffusion sign.
