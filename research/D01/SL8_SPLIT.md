# SL8 assembly table — `SmoothSquareIntegrableJets (∇p(t,·))` from `h ∈ H^∞` (D01 · P2)

> **DONE (lane 117).**  The whole table (rows i.1 … iii.3) is assembled in
> `formalization/NSFormalization/Section4/D01/PressureJets.lean` (namespace
> `NSFormalization.Section4.D01`).  Row i.7 = `orderZeroDatum_pressureGradient_eq`; P2 =
> `pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`; plus the corollary
> `temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR` (`∂ₜu(t,·) ∈ H^∞`).  All three
> `#print axioms` = `[propext, Classical.choice, Quot.sound]`
> (`research/D01/axioms_sl8_assembly.lean`).  `hcurl` uses lane 111's in-tree
> `partialDeriv_pressureGradient_symm` (not lane 106's `A01.PressureGauge`), so the module does not
> import A01.  See `research/D01/ATTEMPTS_SL8_ASSEMBLY.md`.

> Lane 111.  Records the full route from the order-0 Plancherel seed to P2's target,
> `SmoothSquareIntegrableJets (fun x => pressureGradient u.pressure t x)` for
> `u : ClassicalSolutionR ν a f T`, `hf : MemForceR f`, `t ∈ Ioo 0 T`.  Companion to
> `P2_SPLIT.md` (SL0–SL8) and `REVIEW_ORDER_ZERO.md` §6.  Every prep lemma this lane needed is
> now in tree (Group 1 = `Section4/D01/OrderZeroAlgebra.lean`, Group 2 =
> `Section4/D01/MomentumSlice.lean`).  **Lanes 106 (PR #109) and 108 (PR #110) have since merged**
> into `origin/erenup/integration`: the order-0 longitudinal fix
> `Leray.lerayComplement_zero_orderZeroDatum_eq_self` (108) and the curl-free datum
> `A01.PressureGauge.hasSymmetricJacobian_pressureGradient` (106) are now in tree, so **row i.6 is a
> one-liner and no row of this table is blocked** — the whole route is `S`/`M`-assembly the
> follow-up lane writes against `origin/erenup/integration`.  The lane-111 reviewer already
> compiled the entire table end to end (`research/D01/probes/sl8_assembly_probe.lean`, with 108's
> corollary carried as a hypothesis in place of the not-yet-rebased module).

Notation.  `h := fun x => f (t,x) − advection u.velocity t x + ν • spatialLaplacian u.velocity t x`
(the `H^∞` momentum residual, `= f − (u·∇)u + νΔu`); `∂ₜu := fun x => temporalDerivative u.velocity t x`;
`∇p := fun x => pressureGradient u.pressure t x`.  Momentum (`Pressure.temporalDerivative_slice_eq`,
`Pressure.lean:196`): `∂ₜu = h − ∇p` pointwise on `Ioo 0 T`.  `datum⁰ z := orderZeroDatum (hz)`
(`OrderZeroDatum.lean:96`, needs `hz : MemLp z 2 volume`); `(I−P)₀ := Leray.lerayComplement 0`
(`LerayDatum.lean:255`, a `→L[ℝ]`); `(I−P)ₘ := Leray.lerayComplement (m:ℝ)`.

`h`, `∂ₜu` are `SmoothSquareIntegrableJets`/`MemLp` and `∇p` is `MemLp` (Group 2 below); so all three
`datum⁰ ·` are well-typed.  The residual `h` slice is now exported as
`MomentumSlice.smoothL2_momentumResidual_slice:64` (`hres`, `hres.memLp`), so rows i.1–i.4 do not
re-type it.

---

## (i) Order 0: `datum⁰ ∇p = (I−P)₀ (datum⁰ h)`

| # | Lean-ready statement | size | inputs (file:line) | blocker |
|---|----------------------|------|--------------------|---------|
| i.1 | `MemLp ∇p 2 volume`, `MemLp ∂ₜu 2 volume`, `SmoothL2 h` (⟹ `MemLp h`), `ContDiff ℝ ∞ ∂ₜu` | **DONE (111)** | `MomentumSlice.memLp_pressureGradient_slice:75`, `memLp_temporalDerivative_slice:82`, `contDiff_temporalDerivative_slice:97`; `h` via `smoothL2_momentumResidual_slice:64` + `A05.SmoothL2.memLp` (`SmoothJets.lean:52`) | — |
| i.2 | `datum⁰ ∂ₜu = datum⁰ h − datum⁰ ∇p` | **S** — DONE core (111) | `OrderZeroAlgebra.orderZeroDatum_sub:87` applied to `hres.memLp`,`∇p` MemLp + `isSobolevDatum_unique` (`ForceClass.lean:286`) to swap `orderZeroDatum (hₘₑₘ.sub ∇pₘₑₘ)` for `datum⁰ ∂ₜu` (same field by `temporalDerivative_slice_eq`, `funext`+uniqueness, **not `rfl`**) | — |
| i.3 | `∀ x, ∑ⱼ partialDeriv j ∂ₜu x j = 0` | **DONE (074/111)** | `MomentumSlice.sum_partialDeriv_temporalDerivative_eq_zero:116` (= `DivergenceTime.spatialDivergence_temporalDerivative_eq_zero:131` by `rfl`) | — |
| i.4 | `(I−P)₀ (datum⁰ ∂ₜu) = 0` | **S** — inputs DONE | `orderZeroDatum_transverse_of_divergence_free` (`OrderZeroSymbol.lean:532`) fed with i.1 (`ContDiff`+`MemLp` of `∂ₜu`) + i.3, giving transverse; then `lerayComplement_eq_zero_of_transverse 0 (datum⁰ ∂ₜu)` (`LerayDatum.lean:316`) | — |
| i.5 | `∀ i j x, partialDeriv i ∇p x j = partialDeriv j ∇p x i` (curl-free) | **DONE (111/106)** | `MomentumSlice.partialDeriv_pressureGradient_symm:188` (Clairaut via `ContDiffAt.isSymmSndFDerivAt`); after rebase prefer 106's `A01.PressureGauge.hasSymmetricJacobian_pressureGradient` (see i.6) | — |
| i.6 | `(I−P)₀ (datum⁰ ∇p) = datum⁰ ∇p` | **DONE (108)** — one term | `Leray.lerayComplement_zero_orderZeroDatum_eq_self (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z) (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i z x j = partialDeriv j z x i) : lerayComplement 0 (orderZeroDatum hz) = orderZeroDatum hz` (`OrderZeroCurl.lean:510`, namespace `NSFormalization.Section4.D01.Leray`, PR #110), fed with `contDiff_pressureGradient_slice` + `hcurl`.  **After rebase take `hcurl` from lane 106:** `(A01.PressureGauge.hasSymmetricJacobian_pressureGradient u.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩).2 x i j` (reviewer-verified `rfl`-equal to i.5, and strictly more general — works at `t = 0` and for any pressure field); `fun i j x => partialDeriv_pressureGradient_symm u ht i j x` (i.5) is the drop-in fallback | — |
| i.7 | `datum⁰ ∇p = (I−P)₀ (datum⁰ h)` | **S** — assembly | apply `(I−P)₀` to i.2 (`congrArg` + `map_sub`, i.e. `OrderZeroAlgebra.lerayComplement_orderZeroDatum_sub:106`'s content), then substitute i.4 (`(I−P)₀ datum⁰ ∂ₜu = 0`) and i.6 (`(I−P)₀ datum⁰ ∇p = datum⁰ ∇p`); solve `0 = (I−P)₀ datum⁰ h − datum⁰ ∇p` (`sub_eq_zero`) | — |

Net: **(i) is unblocked.**  Row i.6 is lane 108's merged `lerayComplement_zero_orderZeroDatum_eq_self`;
i.2/i.4/i.7 are the assembly around the two fibre facts, and every prep lemma they need is delivered
by lanes 074/094/106/108/111.

---

## (ii) Bootstrap to order `m`

`h` is `SmoothSquareIntegrableJets` (i.1 for `h`), so `memHInfty_iff_smoothSquareIntegrableJets.mpr`
(`DatumToJets.lean:298`) gives `MemHInfty h`, whose jet half is `∀ m, ∃ Aₘ, IsSobolevDatum (m:ℝ) h Aₘ`.
Fix `Aₘ` (h's order-`m` datum) and set `Bₘ := (I−P)ₘ Aₘ : RealVectorSobolev (m:ℝ)`.

| # | Lean-ready statement | size | inputs (file:line) | blocker |
|---|----------------------|------|--------------------|---------|
| ii.1 | `lowerVectorL m 0 h0m Aₘ = datum⁰ h` (`h0m : (0:ℝ) ≤ m`) | **S** | `isSobolevDatum_lower h0m hAₘ` (`LerayLowering.lean:202`) gives an order-0 datum of `h`; `isSobolevDatum_unique` (`ForceClass.lean:286`) identifies it with `datum⁰ h` | — |
| ii.2 | `lowerVectorL m 0 h0m Bₘ = (I−P)₀ (datum⁰ h)` | **S** | `lerayComplement_lowerVectorL m 0 h0m Aₘ` (`LerayLowering.lean:155`) intertwines: `lowerVectorL m 0 ((I−P)ₘ Aₘ) = (I−P)₀ (lowerVectorL m 0 Aₘ)`; rewrite **`← lerayComplement_lowerVectorL` then `ii.1`** | — |
| ii.3 | `IsSobolevDatum 0 ∇p (lowerVectorL m 0 h0m Bₘ)` | **S** | ii.2 + i.7 (`= datum⁰ ∇p`, an order-0 datum of `∇p` by `isSobolevDatum_orderZeroDatum`, `OrderZeroDatum.lean:103`) | — |
| ii.4 | `IsSobolevDatum (m:ℝ) ∇p Bₘ` | **≈10 lines** | `(isSobolevDatum_lower_iff h0m).mp ii.3` — **checked**: `isSobolevDatum_lower_iff {s r} (hrs : r ≤ s) {z} {A} : IsSobolevDatum r z (lowerVectorL s r hrs A) ↔ IsSobolevDatum s z A` (`LerayLowering.lean:214`), here `s=m, r=0, A=Bₘ`, so `.mp` sends the order-0 datum of the lowering to the order-`m` datum of `∇p` | — |

`isSobolevDatum_lower_iff` confirmed as exactly the shape claimed in the task
(`IsSobolevDatum r z (lowerVectorL s r hrs A) ↔ IsSobolevDatum s z A`); the bootstrap is the
≈10-line `.mp` in ii.4.  **Namespace caveat:** `lowerVectorL` (rows ii.1/ii.2/ii.4) lives in
`NSFormalization.Section4.D01`, **not** `D01.Leray` (`HalfOrder.lean:103`) — writing it unqualified
under `open …Leray` cost the reviewer one compile.

---

## (iii) All orders ⇒ `SmoothSquareIntegrableJets (∇p)` (= P2)

| # | Lean-ready statement | size | inputs (file:line) | blocker |
|---|----------------------|------|--------------------|---------|
| iii.1 | `∀ m : ℕ, ∃ A : RealVectorSobolev (m:ℝ), IsSobolevDatum (m:ℝ) ∇p A` | **S** | `fun m => ⟨Bₘ, ii.4⟩` | — |
| iii.2 | `MemHInfty ∇p` | **S** | `⟨contDiff_pressureGradient_slice u.pressure_smooth ⟨_,_⟩ (DatumToJets.lean:504), iii.1⟩` | — |
| iii.3 | `SmoothSquareIntegrableJets ∇p` | **S** | `memHInfty_iff_smoothSquareIntegrableJets.mp iii.2` (`DatumToJets.lean:298`) — **this is P2** | — |

Equivalent finish (cross-check, `P2_SPLIT.md` SL8): once `∂ₜu = P h` is established (the transverse
half), feed `Pressure.pressureGradient_slice_smoothSquareIntegrableJets:376`
(`SmoothSquareIntegrableJets ∂ₜu → SmoothSquareIntegrableJets ∇p`).  HeliCorgi's order-0
`r3HelmholtzPressure_gradient` (`R3HelmholtzPressure.lean:259`) is the order-0 cross-check for i.7,
not demoted.

---

## Status summary

- **DONE (lane 117).**  All rows are assembled in `Section4/D01/PressureJets.lean`; see the header
  note above for the theorem names.  Rows i.2/i.4/i.6/i.7 are the body of
  `orderZeroDatum_pressureGradient_eq`; rows ii.1–ii.4 + iii.1–iii.3 are the body of
  `pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`.  Every "S"/"≈10 lines" size held.
- **No blocker remains.**  Lane 108 (PR #110) merged its order-0 longitudinal fix
  `Leray.lerayComplement_zero_orderZeroDatum_eq_self` (`OrderZeroCurl.lean:510`, `D01.Leray`), so
  row i.6 is now an in-tree one-liner; lane 106 (PR #109) merged
  `A01.PressureGauge.hasSymmetricJacobian_pressureGradient`, whose `.2 x i j` is the `hcurl` input
  (reviewer-verified `rfl`-equal to i.5's `partialDeriv_pressureGradient_symm`, and strictly more
  general).  The whole table (rows i.1 … iii.3) was re-assembled and compiled end-to-end by the
  lane-111 reviewer (`research/D01/probes/sl8_assembly_probe.lean`), producing P2 — the `M` size in
  row i.6 was 108's merged work, not the assembly lane's.
- Suggested follow-up (assembly) lane: rebase onto `origin/erenup/integration`, open a new
  `Section4/D01/PressureJets.lean` importing `OrderZeroAlgebra`, `MomentumSlice`, `OrderZeroCurl`
  (108), `OrderZeroSymbol`, `LerayLowering`, and `A01/PressureGauge` (106); assemble
  (i.7)→(ii)→(iii) as `pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR` (≈55 lines;
  the probe is the recipe), register it as the P2 contract field, and cross-check against
  `Pressure.pressureGradient_slice_smoothSquareIntegrableJets:376`.
- **Namespace caveats for the assembly lane:** `lowerVectorL` (rows ii.1/ii.2/ii.4) is
  `NSFormalization.Section4.D01.lowerVectorL`, **not** `D01.Leray.lowerVectorL`
  (`HalfOrder.lean:103`); `MemForceR` in these statements resolves to `D01.MemForceR`, which is
  `rfl`-equal to `A02.MemForceR` (F-5).  Row i.2's uniqueness step is genuinely needed (the two
  `MemLp` witnesses are for syntactically different functions), and `leray_datum_lower`
  (`LerayLowering.lean:229`) does **not** shortcut ii.2+ii.3 (it needs an order-`m` transverse
  statement that is unavailable), so the `lerayComplement_lowerVectorL` + `isSobolevDatum_unique`
  route is the correct one.
