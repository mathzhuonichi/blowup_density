# T16 `lem:potential` — assembly (lane 358, Opus)

Target: `theorem localPotential : localPotentialStatement`
(`Section3/T16/LocalPotential.lean`), assembled from lanes 347/351/352.
Result: **all 26 fields closed**, module `Section3/T16/Assembly.lean`, green build,
every declaration `[propext, Classical.choice, Quot.sound]`.

## Concrete choices

* `potential := timePotential v x₀`; the three potential fields come from lane 351
  (`timePotential_contDiffOn_ball`, `centeredPotential_eq_integral`,
  `spatialCurl_timePotential_on_ball`) by `exact`, using `v` only on the chart
  cylinder.
* `correction ε := latticeLift (physicalCorrection v x₀ T θ η ε)` with the
  **original** `v` (not a truncated reference), so
  `hWformula : physicalCorrection v x₀ T θ η ε (t,x) = -curl(η_ε θ_ε (timePotential v x₀)) x`
  is `rfl` (definitional: `physicalCorrection = localCorrection = -spatialCurl(Φ)`,
  and `spatialCurl f (t,x) = curl (f(t,·)) x` definitionally).
* All seven `correction_*` fields come from lane 352's `correction_fields_of_chart`
  (the fixed local-cancellation interface, merged from `erenup/352-T16-lattice-lift`).

## The three chart facts that needed the *local* reference

`PhysicalRemoval.{physical_smooth, physical_divergence, physical_removes}` prove
exactly the shapes we need, but each takes `ContDiff ℝ ∞ v` on **all** of space
(and `physical_removes` also `∀ t x, div v = 0`); the T16 hypothesis gives `v`
only on `Ioo 0 (T+δ) ×ˢ ball x₀ r`.  We re-derived the three under the local
hypothesis:

* `cutoffPotential_contDiff`: the inner field `Φ = (η_ε θ_ε) • timePotential v x₀`
  is globally `C∞` by a **joint spacetime truncation**
  (`contDiff_cutoffSmul_of_ballSmooth`): on the open cylinder `A = timePotential v x₀`
  is smooth (lane 351), off `tsupport Φ` it vanishes.  `tsupport Φ` sits inside the
  cylinder because `tsupport(temporalCutoff η T ε) ⊆ Ioo(T-2ε²)(T+2ε²) ⊆ Ioo 0 (T+δ)`
  (`temporalCutoff_tsupport_Ioo`, from `eps_time`) and
  `tsupport(spatialCutoff θ x₀ ε) ⊆ ball x₀ (ε·θRadius) ⊆ ball x₀ r`
  (`spatialCutoff_tsupport_ball`, from `eps_space`), the product support bound
  `closure(support tc ×ˢ support sc) = tsupport tc ×ˢ tsupport sc` via
  `closure_prod_eq`.
* `physicalCorrection_contDiff` = `(contDiff_spatialCurl (cutoffPotential_contDiff …)).neg`.
* `physicalCorrection_divergence`: divergence of a curl, exactly the proof of
  `localCorrection_divergence` (`curl_neg`, `divergence_curl`) but with the global
  `timePotential_contDiff` replaced by the slice of the jointly-smooth `Φ`.
* `hWcompact := physical_compact`, `hWtsupp := physical_support` — reused verbatim
  (they never touch smoothness of `v`).

## Cancellation (`hWcancel`, the new local interface)

`physicalCorrection_cancels` produces the datum
`⟨O, IsOpen O, O ⊆ ball x₀ r, packet ⊆ periodicSet O, ∀ x ∈ O, v + W = 0⟩` with the
**scaled plateau** `O = spaceMap ε x₀ '' O_plateau = x₀ + ε•O_plateau` (where
`θ_ε = 1`):

* `O` open (preimage of the open plateau under `x ↦ ε⁻¹•(x-x₀)`), `O ⊆ ball x₀ r`
  (`O_plateau ⊆ ball 0 θRadius` since `θ = 1 ≠ 0` there, then scale by `ε`, use
  `eps_space`).
* cancellation on `O`: for `x = x₀+ε•z`, `θ_ε = 1` on the open `O` (so `= 1` near
  `x`) and `η_ε(t) = 1` for `t ∈ [T-ε², T)` (`eta_one`, `(t-T)/ε² ∈ [-1,0)`); hence
  `physicalCorrection = -curl(timePotential v x₀ (t,·)) x = -v(t,x)` via
  `curl_cutoff_eq` and the **local** curl identity `spatialCurl_timePotential_on_ball`
  (needs `t ∈ Ioo 0 (T+δ)`, `x ∈ ball x₀ r`, both discharged).
* packet bound `⊆ periodicSet O`: `periodicScaledPacket = latticeLift (scaledPacket)`
  where `scaledPacket = parabolicVelocity ε⁻¹ (T-ε²) x₀ (zeroPastField U)`.

## The packet-support subtlety (a real dead end resolved)

* `latticeLift_sliceSupport` (lane 352, ball target) and any all-time bound on the
  raw packet **fail**: for physical `t ≥ T` the rescaled reference time
  `(ε⁻¹)²(t-(T-ε²)) ≥ 1`, where `U(s,·)` is *unconstrained* (the statement bounds
  `U` only on `Ioo 0 1`), so `scaledPacket` has no uniform-in-time spatial support
  bound and `SupportedInCube` (needed for the lift's local finiteness) does not hold.
* Fix: **truncate in time**.  `w' z := if z.1 < T then scaledPacket z else 0` has an
  all-time slice bound `w'(s,·) ⊆ x₀+ε•K` (before `T-ε²` the packet is `0` by
  `zeroPast_dilate_early`; on `(T-ε², T)` the rescaled time lies in `(0,1)`, so
  `parabolic_support` + `zeroPastField_of_pos` + `hUsupp` apply), and `w'(t,·)`
  agrees with the packet at our `t < T`.  A **closed-support** slice lemma
  `latticeLift_sliceSupport_closed` (compact `C = x₀+ε•K`; `C` closed makes each
  translate's support exactly `C + lattice n`, so no `ρ < r` slack is needed) then
  gives `tsupport(packet slice) ⊆ periodicSet(x₀+ε•K) ⊆ periodicSet O`
  (`periodicSet_mono`, `x₀+ε•K ⊆ x₀+ε•O_plateau` since `K ⊆ O_plateau`).

## Negative notes / dead ends

* The **pre-fix** `correction_fields_of_chart` (whole-ball `hWcancel : ∀ x ∈ ball x₀ r,
  v + W = 0`) is unsatisfiable for the concrete correction: `W` is supported in the
  tiny scaled ball `ball x₀ (ε·θRadius)`, so `v + W = -v ≠ 0` wherever `θ_ε ≠ 1`.
  Waited for lane 352's local interface (`O ⊆ ball x₀ r`, `packet ⊆ periodicSet O`,
  cancellation on `O`) before assembling; merged `erenup/352-T16-lattice-lift`.
* Reusing `PhysicalRemoval.physical_smooth`/`physical_divergence`/`physical_removes`
  directly fails on the `ContDiff ℝ ∞ v`/global-`div` hypotheses — the local
  re-derivations above are required.
* Building `W` from a *globally-smooth truncated* reference `V = χ·v` was rejected:
  it would make `timePotential V ≠ timePotential v` off a smaller ball, so
  `hWformula` (needed on all of `ball x₀ r`) would only hold on a strictly smaller
  ball.  Using the original `v` keeps `hWformula` a `rfl`.
* `if_pos`/`if_neg` are deprecated in this toolchain but still functional and appear
  in existing source (`Source/PacketForceExtension.lean`); a `split_ifs` rewrite
  auto-discharges via the context contradiction and breaks the explicit branches, so
  the `if_pos`/`if_neg` form is kept.
