# C01 attempts and decisions

Lane 031, task C01 ("Ordinary energy and `H¹` absorption"). Companion to
`research/C01/Spec.lean` and `research/C01/COMPARISON.md`.

## Review fixes

Applied against `research/C01/REVIEW.md` (verdict **ACCEPT-WITH-NOTES**). One
entry per finding: what changed, and for anything left alone, why.

### Finding 1 (MEDIUM) — trilinear fields' hypothesis class

**Changed.** `trilinearHolder` and `trilinearAbsorbed` now take
`SmoothSquareIntegrableJets z` instead of `MemHInfty z`:

```lean
-  trilinearHolder    : ∀ z : SpatialField, MemHInfty z → …
+  trilinearHolder    : ∀ z : SpatialField, SmoothSquareIntegrableJets z → …
-  trilinearAbsorbed  : ∀ z : SpatialField, MemHInfty z → …
+  trilinearAbsorbed  : ∀ z : SpatialField, SmoothSquareIntegrableJets z → …
```

This is the review's first option, not the "add a general bridge field" one. The
registered clause these two feed, `gradientL6.gradientLSix`
(`verification/Contracts/V1/GradientL6.lean:138-139`), runs on
`SmoothSquareIntegrableJets`, and the datum ⟹ jet direction is open
(`BoundedRepresentative.lean:71-74`). With the jet hypothesis the derivation of
`trilinearAbsorbed` from `trilinearHolder` closes on the registered clause
alone, so the docstring's "not an independent assumption" claim is now true as
written. Adding a general `∀ z, MemHInfty z → SmoothSquareIntegrableJets z`
field instead would have imported D01 unit L2 at full generality into C01 — a
strictly larger obligation than `velocityJets`, for no gain, since the only
fields either clause is ever applied to are velocity slices and `velocityJets`
already hands out both forms for those.

Docstrings updated: `trilinearHolder` gains a paragraph "**The hypothesis is the
jet form, not `MemHInfty`**" giving this reasoning; `trilinearAbsorbed` records
the same and points at the new bridge.

### Finding 2 (MEDIUM) — missing `ℝ≥0∞ ↔ ℝ` bridge for `‖Δz‖₂²`

**Changed.** New field, placed immediately after `trilinearAbsorbed`:

```lean
  laplacianSqENorm :
    ∀ z : SpatialField, SmoothSquareIntegrableJets z →
      eLpNorm (laplacian z) 2 volume ^ (2 : ℝ) = ENNReal.ofReal (laplacianSq z)
```

Same `.toReal`-free style as `sobolevTwoFourier`. The structure now has 23
fields (was 22). Without it the two trilinear fields could not be fed into
`enstrophyDifferentialBound`, which is exactly the review's point that they were
documentary rather than load-bearing.

**Not added: the `L⁶` analogue.** The review offered it as optional ("though the
`L⁶` factor is only ever an intermediate"). It is left out because
`eLpNorm (gradientTensor z) 6 volume` appears in exactly one field,
`trilinearHolder`, and is eliminated by `gradientLSix` on the way to
`trilinearAbsorbed`; it occurs in no real-valued field, so it never has to
cross between the two number systems. The `laplacianSqENorm` docstring says
this explicitly, so a later reader does not read the asymmetry as an oversight.

**Not done: moving `criticalL3` or the `L⁶` norm to `ℝ`.** The review explicitly
warns against this and is right — the `ℝ≥0∞` hypothesis side is what makes
`‖u(t)‖₃ = ⊤` fail safe.

Proof route recorded in the new field's docstring: the `L²` case is already in
tree as `NSFormalization.Section4.I02.Energy.eLpNorm_two_eq_ofReal_sqrt`
(`formalization/NSFormalization/Section4/I02/Energy.lean:87`); squaring it gives
the field. Verified that lemma's statement and hypotheses directly.

### Finding 3 (LOW) — `forceTimeRegularity`

**Changed, both halves.**

* The two redundant `IntervalIntegrable` conjuncts are **dropped**. The field is
  now the two-conjunct `(∀ t ≥ 0, MemLp (slice f t) 2 volume) ∧ ContinuousOn
  (fun s => l2Norm (slice f s)) (Ici 0)`. The docstring records why the dropped
  conjuncts are recoverable: continuity on `Ici 0` gives continuity on each
  compact `[0,t]`, hence interval integrability there, and
  `l2Sq = l2Norm ^ 2` pointwise because `l2Sq` is an integral of squares.
* The prose overclaim is **fixed** by weakening the prose, not by adding global
  conjuncts. A new paragraph "**Local, not global**" says that
  `04-whole-space.tex:171`'s sentence is about global `(0,∞)` finiteness, that
  this is `MemForceR`'s own datum-path content (`Data.lean:549-551`), and that
  every consumer here evaluates the force integrals at a finite horizon `S`, so
  the local form is all that is needed and all that is claimed.

The "add the two `(0,∞)` conjuncts" branch was declined deliberately: transporting
the *global* datum-path finiteness to the physical slices is a strictly larger
obligation than anything eq:RL2, eq:RH1 or the assembly uses, and putting it in
the contract would have made C01 own a gap none of its consumers exercise.

### Finding 4 (LOW) — citation slips

All four **fixed**.

* `Spec.lean` module header, bridge 1: `BoundedRepresentative.lean:82-88` →
  `:71-74`. (The `velocityJets` field docstring already had `:71-74`; only the
  header was wrong — an earlier bulk edit missed it because that occurrence is
  spelled with the `verification/Contracts/V1/` prefix.)
* `Spec.lean`, `enstrophyIdentity`: `04-whole-space.tex:107` → `:106` for the
  prose "testing against `−Δu`", with the display cited separately as
  `:107-110`.
* `COMPARISON.md`: `CompactEnergy.energy_hasDerivAt` `:300` → `:302` (two
  occurrences).
* `COMPARISON.md` §2(a): the blanket "carries `HasCompactSupport`" is replaced by
  the split the review asked for — four theorems state it literally
  (`CompactEnergy.energy_balance:206`, `energy_rate_le:257`,
  `PacketEnergy.pde_energy_inequality:39`, `energy_balance_viscosity:57`), the
  other four use `IsCompact K` plus `∀ t ∈ Icc a b, tsupport (fun x => u (t,x)) ⊆ K`
  (`CompactEnergy.energy_hasDerivAt:303-304`, `hasDerivAt_energy_balance:325-328`,
  `PacketEnergy.packet_energy:145,149`, `packet_dissipation:235,239`), with
  `CompactEnergy.slice_compact:279` converting the second form to the first. The
  conclusion (none is reusable for a non-compactly-supported `H^∞` velocity) is
  unchanged and noted as unaffected.

### Finding 5 (INFORMATIONAL)

**Nothing changed**, by design — the review records these as checked and sound,
not as defects. For the record, and agreeing with the review:

* `enstrophyIntegralBound`'s hypothesis on `Ico 0 t` with a conclusion at `t` is
  the intentional strengthening.
* `h2TimeIntegralZeroDatum` not carrying `(fun _ => 0) ∈ initialClassR` is
  intentional: it keeps the field literally the shape `STATEMENTS.md:604-605`
  records, and the membership is trivial to supply at the call site.
* Nothing pins `C₁` from above; R43/R44 choose their `c` after `C₁`, so the
  constant chain flows correctly.
* `research/**/*.lean` is not compiled by CI (`experiments/build_changed_lean.py`
  maps only `verification/`, `formalization/`, `vendor/NavierStokesAndEuler/`).
  Pre-existing project pattern shared with the A02 and A05 drafts.

### Knock-on changes to `COMPARISON.md`

Not findings, but forced by the fixes above:

* New table row for `laplacianSqENorm`.
* `trilinearHolder` / `trilinearAbsorbed` rows record the jet hypothesis.
* `forceTimeRegularity` row records the local-not-global scope.
* Unit **U6** is renamed and now also discharges `laplacianSqENorm`; more
  importantly, **U6 no longer depends on U1**. With the trilinear fields stated
  on `SmoothSquareIntegrableJets`, nothing in U6 needs the open datum ⟹ jet
  direction, so U6 is now the one unit that can start immediately. **U8** picks
  up the U1 dependency instead, since it is where the trilinear clause is
  applied to an actual velocity slice. The dependency order line and the
  `A05.gradient_l6` note were updated to match.
* Unit **U2** drops the interval-integrability obligations.

## Open items not touched by this review

* **U1 remains the gate.** The datum ⟹ jet direction of D01 unit L2 is open;
  `velocityJets` owns it, and no clause of the contract is dischargeable without
  it. Finding 1's fix narrows what depends on it (U6 no longer does) but does not
  close it.
* **U10 remains the hardest unit inside C01's own scope**: the `H²` weight
  identity exists in tree only for compactly supported fields
  (`AngularGradientIdentity.lean:81,92`) and only for the literal-Fourier norm,
  whereas `sobolevTwoFourier`'s left side is D01's datum infimum
  `Data.sobolevENorm 2`.
* **`slice`.** The review notes that if C01 is promoted to a registered contract,
  `slice` should move into `Contracts/V1/Data.lean` rather than live in the
  consumer. Agreed; not done here, because this lane may not edit
  `verification/`.
