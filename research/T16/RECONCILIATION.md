# T16 (lem:potential, `03-torus.tex:176-192`) — reconciliation of the double-blind drafts A (lane 271, gpt-5.6-sol) and B (lane 272, gpt-6-astra)

Lead: erenup, 2026-09-17 (UTC 21:05). Drafts: `.claude/worktrees/271-SPEC-t16-draft-a/research/T16/DraftA.lean`, `.claude/worktrees/272-SPEC-t16-draft-b/research/T16/DraftB.lean`.

## 1. Agreement
Both state the same clause list (near field-for-field): a smooth compactly supported spatial Urysohn cutoff `θ` with values in `[0,1]`, `θ = 1` on an open plateau containing the prescribed compact `K_*`, support in a fixed ball of radius `θRadius`; a smooth compactly supported time cutoff `η` with values in `[0,1]`, `η = 1` on `[−1,1]`, support in `(−2,2)`; a scale threshold `ε₀ > 0` with `2ε² < min T δ` and `ε·θRadius < r` for `ε ≤ ε₀`; the radial vector potential `A` (`∇×A = v` on the ball, smooth, explicit formula); the correction `w_ε = −∇×(η_ε θ_ε A)`: smooth, unit-periodic, divergence-free, supported in the ball (space) and in the time window, and the cancellation `eq:bgzero` on `[T−ε², T)` (the corrected background `v + w_ε` vanishes where the packet lives).

## 2. Differences and rulings
| point | A | B | ruling |
|---|---|---|---|
| packaging | `structure LocalDivergenceFreeCutoffAPI (T δ r v x₀ Kstar localizedVelocity θ plateau θRadius η ε₀ potential correction) : Prop` — every object a parameter | data record `CutoffData` (`θ, plateau, θRadius, η, ε₀, potential, correction`) + `structure LocalPotentialAPI (v U K) (D : CutoffData) : Prop` | **B's data record** (mirrors Section 4's I02 `CorrectionAPI`, where the correction's data live in a record and the API states their properties; the eventual contract is "∃ D, LocalPotentialAPI v U K D"). |
| range clauses | `theta_nonneg`, `theta_le_one` (two fields) | `theta_range : θ x ∈ Icc 0 1` | **B** (one field each for `θ`, `η`). |
| vocabulary | own `VelocityField`, `IsPeriodic` | own `VelocityField`, `IsPeriodic` | **T10's** `SpaceTimeField`/`SpatialField`, `IsPeriodicSpatial`/`IsPeriodicOn` (`research/T10/Spec.lean`) — copy verbatim with the provenance banner, as lane 278 does for T13. |
| paper citations | precise (`:167-174,181,212`) | coarser | merge A's citations into B's fields. |
| the packet `U`/`localizedVelocity` | parameter `localizedVelocity : ℝ → VelocityField` | parameter `U : VelocityField` | **B** (the packet is T14's object; T16 only needs it for `correction_cancels`); name it `U` and note it must match T14's packet name at registration. |

## 3. Decisions
Field names and order as B (`theta_*`, `plateau_*`, `eta_*`, `eps_*`, `potential_*`, `correction_*` incl. `correction_cancels` = `eq:bgzero`), citations from A, T10 vocabulary. Section 4 counterpart for the registration lane: I02's `CorrectionAPI`/`Bindings/Correction.lean` (`correction (P) {T δ r}` constructor) — the torus proof lane should reuse `Paper1.CorrectionProfile.physicalCorrection` / `CorrectionVectorNorms` where SECTION3_PLAN §2 says so.

## 4. Next
Lane 279: reconciled `research/T16/Spec.lean` (on the T10 vocabulary) + merged `COMPARISON.md`; then the proof lane (M, sol).
