# A01 · unit P1 — radial potential differentiates back to its gradient

Module: `formalization/NSFormalization/Section4/A01/RadialPotential.lean`
Paper: `paper/sections/02-preliminaries.tex:96-100`. Target shape: `research/A01/Spec.lean:227`
(`ManuscriptLocalRegularity.pressure_potential`, the gauge-equivalence packaging of the
pointwise gradient identity), D01 unit L9(b).

## What is proved

- `hasFDerivAt_radialPotential` : for `G : Space → Space` with `HasSymmetricJacobian G` and
  `ContDiff ℝ ∞ G`,
  `HasFDerivAt (fun y => ∫ r in 0..1, ⟪G (r • y), y⟫) (innerSL ℝ (G x)) x`, i.e. `∇p = G`.
- `pressureGradient_pressurePotential` : if `G' (t, ·) = G` then the upstream
  `pressureGradient (pressurePotential G') t x = G x`.
- `inner_fderiv_symm` : `⟪DG(z) v, w⟫ = ⟪DG(z) w, v⟫` from the componentwise symmetric Jacobian.

Axioms: `propext, Classical.choice, Quot.sound` only (`research/A01/axioms_p1.lean`).

## Route that worked

1. Integrand `F : Space × ℝ → ℝ := fun p => ⟪G (p.2 • p.1), p.1⟫`, `ContDiff ℝ ∞ F` from
   `ContDiff.inner` + `ContDiff.comp` + `contDiff_snd.smul contDiff_fst`.
2. **Differentiation under the integral**: reused
   `EulerCompactParameterIntegral.integral_hasFDerivAt` (`vendor/NavierStokesAndEuler/Euler/CompactParameterIntegral.lean`).
   - Signature: `(a b : ℝ) (hab : a ≤ b) (F : X × ℝ → E) (hF : ContDiff ℝ ∞ F) (x) :`
     `HasFDerivAt (fun y => ∫ t in a..b, F (y,t)) (∫ t in a..b, parameterDerivative F (x,t)) x`.
   - **Side condition: `ContDiff ℝ ∞ F`.** This is why the theorem takes `ContDiff ℝ ∞ G`
     rather than the `Differentiable`-only `HasSymmetricJacobian`. (Same machinery the vendor's
     own `Paper1/RadialPotential.lean` uses for the vector potential.)
3. Evaluate the CLM integral at `v` with `ContinuousLinearMap.intervalIntegral_apply` (needs the
   integrand interval-integrable — from continuity of `parameterDerivative F`).
4. `parameterDerivative F (x,t) = fderiv ℝ (fun y => F (y,t)) x` proved via
   `HasFDerivAt.comp` with the section map `fun y => (y,t)` (`inl`), then `.fderiv.symm`.
5. Slice derivative `fderiv (fun y => ⟪G(t•y), y⟫) x v = ⟪G(t•x), v⟫ + t * ⟪DG(t•x) x, v⟫`,
   via `fderiv_inner_apply`, the chain rule for `y ↦ G(t•y)` (`HasFDerivAt.const_smul`), and
   `inner_fderiv_symm` (symmetric Jacobian) to swap `⟪DG(t•x) v, x⟫ → ⟪DG(t•x) x, v⟫`.
6. FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) on `ψ(s) = s * ⟪G(s•x), v⟫`:
   `ψ'(s) = ⟪G(s•x),v⟫ + s * ⟪DG(s•x) x, v⟫` (product rule), `ψ(1) - ψ(0) = ⟪G x, v⟫`.
7. Corollary: `pressurePotential G' (t,·)` slice-equals the scalar potential of `G`
   (`intervalIntegral.integral_congr` + `hslice`); then `∇` picks components
   `⟪G x, e_i⟫ = (G x) i` and `∑ i (G x) i • e_i = G x` (`Fin.sum_univ_three`).

## Failed / rejected approaches and why

- **`HasSymmetricJacobian` (`Differentiable` only) as the sole hypothesis.** Insufficient for
  the reused `integral_hasFDerivAt`, which is **stated** at `ContDiff ℝ ∞ F`. So `ContDiff ℝ ∞ G`
  was added; conclusion unchanged.
  **Correction (lane-101 review, Finding 1):** `ContDiff ℝ ∞` is *not* the minimal hypothesis.
  The vendor proof of `integral_hasFDerivAt` uses only `hF.continuous`, `hF.differentiable` and
  `Continuous (fderiv ℝ F)`, all available at `ContDiff ℝ 1` — the reviewer transcribed that
  proof **verbatim with `∞ → 1`** and it compiles unchanged (22 lines; `CompleteSpace E` also
  unneeded). The rest of `hasFDerivAt_radialPotential` likewise only uses `.continuous`,
  `.differentiable`, `.fderiv_right`, each with a level-1 counterpart, so the minimal
  hypothesis for the whole theorem is `ContDiff ℝ 1 G`. We nonetheless **keep `∞`**: it is not
  worth forking a vendor lemma to save one derivative order, the consumer supplies `∞`
  (`ClassicalSolutionR.pressure_smooth`, `ContDiffOn ℝ ∞`, `Spec.lean:117`), and the
  manuscript's own hypothesis is `H^∞` (`02-preliminaries.tex:91`). A C¹ variant is a
  vendor-side change, not extra bookkeeping in this lane. (The earlier claim here that a C¹
  route "would require re-deriving differentiation under the integral from
  `hasFDerivAt_integral_of_dominated_of_fderiv_le` with a manual bound" was wrong: the bound is
  already in the vendor proof and transcribes directly.)
- **`inner_fderiv_symm` by reducing `inner` to `∑ i, a i * b i` then reconstructing
  `u = ∑ i, u i • e_i` as a `Finset` sum.** The `EuclideanSpace = PiLp = WithLp` `.ofLp`
  wrapper made `(∑ i, u i • single i 1).ofLp j = u.ofLp j` fight `simp` (max recursion / unused
  args). Replaced with the **explicit three-term** basis expansion
  `u = u 0 • e0 + u 1 • e1 + u 2 • e2` (`ext i; fin_cases i <;> simp [coordinateVector]`, the
  vendor file's own idiom) plus bilinear `inner_add_*` / `real_inner_smul_*` and
  `EuclideanSpace.inner_single_right`. Key detail: pull the scalars out with a **first** `simp`
  (`real_inner_smul_left/right`, `inner_add_*`, `map_add/map_smul`), then a **second** `simp
  [basis_inner]` — a single combined `simp` let `basis_inner` fire on `⟪c • u, e_j⟫` first,
  leaving `(c • u).ofLp j` that `hsym'`'s `rw` could not match.
- **`hc : HasFDerivAt (fun y => ⟪G(t•y),y⟫) (parameterDerivative F (x,t)) x` by ascribing the
  `.comp` output.** Elaborator left `?g ∘ (fun y=>(y,t))` and could not solve the higher-order
  unification against `fun y => ⟪G(t•y),y⟫`. Fixed by proving the **CLM-level** equality
  `parameterDerivative F (x,t) = fderiv ℝ (fun y => …) x` as `(… .comp x hin).fderiv.symm`
  (defeq handles `F ∘ (fun y=>(y,t)) ≡ fun y => F(y,t)` and `parameterDerivative ≡ _.comp inl`).
- **`ψ'` via `HasDerivAt.smul` on the `Space`-valued `s ↦ s • G(s•x)`.** Failed on a
  **function-form and summand-order** mismatch (corrected per lane-101 review Finding 2 — this
  was *not* a `PiLp`/`WithLp` instance diamond): `.smul` produced
  `HasDerivAt (id • fun s => G (s • x)) (t • DG(t•x) x + G (t•x)) t`, whereas the stated target
  was `HasDerivAt (fun s => s • G (s•x)) (G (t•x) + t • DG(t•x) x) t` — `id • f` vs `fun s => s • f s`
  and the two summands in the opposite order, which `simpa` could not bridge. Abandoned in
  favour of the scalar `.mul` route below.
- **`ψ'` via `simpa using (hasDerivAt_id t).mul hginner` with the target stated as
  `fun s => s * …`.** `.mul` returns the function as `id * h` (Pi-mul) and the value with a
  `Real.normedCommRing.toAddCommGroup` path, so `simpa` reported the residual
  `@HasDerivAt … Real.normedCommRing.toAddCommGroup … (id * fun s => ⟪G (s•x), v⟫) …` vs
  `… Real.instAddCommGroup Semiring.toModule … (fun s => s * ⟪G (s•x), v⟫) …` — the ℝ
  instance-path mismatch.
  Fixed by giving `hmul` an **explicit type** `HasDerivAt (fun s => s * ⟪G(s•x),v⟫)
  (1 * ⟪G(t•x),v⟫ + t * ⟪DG(t•x) x, v⟫) t := (hasDerivAt_id t).mul hginner` — the ascription
  forces the defeq resolution of both the function form and the ℝ instances — then `simpa`
  only clears the `1 *`.
- **`rw [hslice]` inside the corollary's `integral_congr` goal.** The integrand was left as an
  unreduced `(fun x => …) r`; `rw` could not find `G' (t, ?)`. Fixed with `simp only [hslice]`
  (beta-reduces and closes by rfl).

## Commands run

- `cd verification && lake env lean ../research/A01/draft_p1.lean` → silent (exit 0).
- `cd verification && lake build NSFormalization.Section4.A01.RadialPotential` → success.
- `cd verification && lake env lean ../formalization/.../RadialPotential.lean` → silent.
- `cd verification && lake env lean ../research/A01/axioms_p1.lean` → the three standard axioms.
- `make check` (from worktree root) → OK.
