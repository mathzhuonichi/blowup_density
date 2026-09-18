# U-B3 attempts (`Section3/T22/CutoffDatum.lean`)

Lane 409. Second pass (Opus) after a first codex pass that delivered no theorem; the
codex text is kept verbatim at the bottom under "Superseded".

## What worked

**(a) `exists_cutoff`.** Mathlib's *smooth Urysohn* lemma in model-space form:

* `exists_compact_between hK hΩ hKΩ` (`Mathlib/Topology/Compactness/LocallyCompact.lean:172`)
  gives a compact `L` with `K ⊆ interior L` and `L ⊆ Ω`.
* `exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, Space)) (M := Space) (n := ⊤)`
  (`Mathlib/Geometry/Manifold/PartitionOfUnity.lean:527`) applied to the closed set `K` and
  `K ⊆ interior L` gives `f : C^⊤⟮𝓘(ℝ,Space), Space; 𝓘(ℝ), ℝ⟯` with `∀ᶠ x in 𝓝ˢ K, f x = 1`,
  `∀ x ∉ L, f x = 0`, `f x ∈ Icc 0 1`.
* `contMDiff_iff_contDiff.mp f.contMDiff` turns the manifold smoothness back into
  `ContDiff ℝ ∞ f` (`Space = EuclideanSpace ℝ (Fin 3)` is its own model space, and the
  instances `T2Space`, `NormalSpace`, `SigmaCompactSpace`, `FiniteDimensional`,
  `IsManifold 𝓘(ℝ, Space) ∞ Space` are all found by typeclass search — verified by an
  `#check` probe before writing any proof).
* `support f ⊆ L` from the vanishing clause, hence `tsupport f ⊆ closure L = L ⊆ Ω`
  (`IsCompact.isClosed.closure_subset`) and `HasCompactSupport f` from
  `IsCompact.of_isClosed_subset`.

`exists_cutoff_isOpen` is `mem_nhdsSet_iff_exists` applied to the `𝓝ˢ` clause.

**(b) `isCutoffDatum_realizes_zeroExtension`.** Three ingredients:

1. `SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ))` **is** pointwise multiplication here:
   `HasCompactSupport.hasTemperateGrowth` (`Mathlib/Analysis/Distribution/TemperateGrowth.lean:121`)
   on the complexified `χ`, then `SchwartzMap.smulLeftCLM_apply_apply`
   (`Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:747`). This discharges risk 5 of
   `T22_SPLIT.md §3`.
2. `χ·ψ` is a `DomainTest Ω`: `support (χψ) ⊆ support χ`, so `tsupport (χψ) ⊆ tsupport χ ⊆ Ω`
   and `HasCompactSupport (χψ)` by `IsCompact.of_isClosed_subset` against `HasCompactSupport χ`.
3. The pointwise identity `(χψ) x * z x i = ψ x * (E₀z) x i` holds **at every `x`**, so the
   two integrals match after one `setIntegral_eq_integral_of_forall_compl_eq_zero` (same
   lemma lane 383 used, no measurability of `Ω` required) and one `integral_congr_ae`:
   * `x ∈ tsupport (E₀z) ⊆ K`: `χ x = 1` by `Filter.Eventually.self_of_nhdsSet`; and
     `χ x = 1 ≠ 0` puts `x ∈ support χ ⊆ tsupport χ ⊆ Ω`, so `E₀z x = z x`.
   * `x ∉ tsupport (E₀z)`, `x ∈ Ω`: `E₀z x = 0` and `E₀z x = z x`, so `z x = 0`; both sides `0`.
   * `x ∉ tsupport (E₀z)`, `x ∉ Ω`: `x ∉ tsupport χ`, so `χ x = 0`; both sides `0`.

Consequences worth recording for U-Z1: the theorem needs **neither `IsOpen Ω` nor `K ⊆ Ω`**,
but it **does** need `HasCompactSupport χ` (the brief's signature for (b) omitted it). Without
it `χ·ψ` need not have compact support, so it is not a `DomainTest Ω` and `hA` cannot be
applied. (a) supplies exactly that hypothesis.

## What did not work / was rejected

* **`exists_smooth_tsupport_subset`, `exists_contDiff_one_nhds_of_subset`** — genuinely not
  identifiers under this pin, but that is a *rename*, not a gap. The vector-space bump API is
  `exists_contDiff_tsupport_subset` and `IsOpen.exists_contDiff_support_eq`
  (`Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:45,79`). **Neither closes (a):**
  the first produces a bump that is `1` at a *single point*, the second a function whose
  *support equals* a given open set (no `= 1` clause at all). Building `χ` from them would need
  a finite subcover of `K` plus a smooth `max`/`1-∏(1-fᵢ)` clamp; the manifold Urysohn lemma
  does the whole job in five lines, so that route was abandoned before any code was written.
* **`ContDiffBump` directly** — only gives balls; `Ω` and `K` here are arbitrary. The repo's
  existing cutoffs (`Section3/T12/Cutoff.lean`, `Section3/T16/BallPotential.lean`,
  `vendor/.../R3CutoffSobolev.lean`) are all ball-centred and none of them states the
  compact-in-open form, so nothing was reusable.
* **Mollifier/convolution route** (bump `⋆` indicator of a thickening of `K`) — correct but
  ~40 lines of support/constancy/smoothness bookkeeping; not needed once the manifold lemma
  was confirmed to elaborate on `Space`.
* **Restricting the (b) integral with `setIntegral_congr_fun`** — would have forced a
  `MeasurableSet Ω` (hence `IsOpen Ω`) hypothesis. Avoided by noticing the pointwise identity
  is global, not merely valid on `Ω`.
* The claim that "the T22 import tree has no bridge for the zero-extension pairing" is false:
  `IsSobolevDatum` unfolds directly to the pairing `∫ x, ψ x * (z x i : ℂ)` and
  `restrictDatum`/`restrictField` unfold definitionally, so the whole of (b) is one `calc`.
* The codex run never built the closure, so its probe failed on a missing `Domain.olean`
  (`lake build NSFormalization.Section3.T22.Domain` from `verification/` fixes that; it is a
  build-order fact, not a Lean fact).

## Superseded — the lane's first (codex) attempts file, verbatim

> # U-B3 attempts
>
> The lane started with a clean worktree; no partial implementation was present.
>
> Under the pinned Mathlib (Lean v4.34.0-rc2), `#check exists_smooth_tsupport_subset`
> and `#check exists_contDiff_one_nhds_of_subset` both fail with `unknown identifier`.
> The requested `isCutoffDatum_realizes_zeroExtension` also needs a theorem identifying
> integration against the zero extension from `tsupport` hypotheses; no such bridge is
> present in the imported T22 modules. I did not add `sorry`, `axiom`, or `native_decide`.
