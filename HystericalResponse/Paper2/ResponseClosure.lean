import Mathlib
import HystericalResponse.Paper2.BallisticHalo

/-
TeX: `2_galactic_modelling/paper_2_galactic_modelling.tex`, Section “Long-range response closure and flat rotation”.

Primary IR modelling assumption is the linear Poisson closure ∇²Φ_resp = κ n
(TeX Assumption poisson), which with the ballistic halo yields g_resp = C Q / r.
Separate-field / unified-field language are brief physical readings of that IR law,
not co-equal free assumptions that each introduce C Q / r.

Also certifies the classical radial Laplacian identities used to match
`∇² ln r = r⁻²` to the monopole halo.
-/

set_option autoImplicit false

namespace Paper2

noncomputable section

/-- Common long-range response magnitude g_resp = C Q / r (derived in TeX from Poisson + halo). -/
def responseAcceleration (C Q r : ℝ) : ℝ :=
  C * Q / r

/-- Response-law prefactor `C = κ / (4π v)`. -/
def responsePrefactor (κ v : ℝ) : ℝ :=
  κ / (4 * Real.pi * v)

/-- Logarithmic potential amplitude `V_Q² = κ Q / (4π v)`. -/
def VQ_sq_monopole (κ v Q : ℝ) : ℝ :=
  κ * Q / (4 * Real.pi * v)

/--
Classical radial Laplacian in 3D (away from the origin):
`Δ_rad f = f'' + (2/r) f'`.
-/
def radialLaplacian3D (f' f'' r : ℝ) : ℝ :=
  f'' + (2 / r) * f'

/-- TeX classical identity: `∇² ln r = r⁻²` via the radial formula. -/
theorem laplacian_log_r
    (r : ℝ)
    (hr : r ≠ 0) :
    radialLaplacian3D (1 / r) (-(1 / r ^ 2)) r = 1 / r ^ 2 := by
  unfold radialLaplacian3D
  field_simp [hr]
  ring

/-- TeX classical identity: `∇²(r⁻²) = 2 r⁻⁴` via the radial formula. -/
theorem laplacian_inv_sq
    (r : ℝ)
    (hr : r ≠ 0) :
    radialLaplacian3D (-(2 / r ^ 3)) (6 / r ^ 4) r = 2 / r ^ 4 := by
  unfold radialLaplacian3D
  field_simp [hr]
  ring

/--
Poisson matching for the monopole halo: if `n = Q/(4π v r²)` and
`Φ = V_Q² ln r` with `V_Q² = κ Q/(4π v)`, then the radial Laplacian of `Φ`
equals `κ n`.
-/
theorem poisson_monopole_matches_log
    (κ v Q r : ℝ)
    (hr : r ≠ 0) :
    radialLaplacian3D
        (VQ_sq_monopole κ v Q / r)
        (-(VQ_sq_monopole κ v Q / r ^ 2)) r =
      κ * haloMonopoleDensity v Q r := by
  unfold radialLaplacian3D VQ_sq_monopole haloMonopoleDensity
  field_simp [hr]
  ring

/--
TeX Eq. gresp: Poisson + monopole halo ⇒ `g_resp = C Q / r` with
`C = κ/(4π v)` and `g_resp = |∇Φ| = V_Q² / r` for `Φ = V_Q² ln r`.
-/
theorem g_resp_from_poisson_monopole
    (κ v Q r : ℝ)
    (hv : v ≠ 0)
    (hr : r ≠ 0) :
    (VQ_sq_monopole κ v Q = responsePrefactor κ v * Q) ∧
      (VQ_sq_monopole κ v Q / r =
        responseAcceleration (responsePrefactor κ v) Q r) ∧
      (responsePrefactor κ v = κ / (4 * Real.pi * v)) := by
  refine ⟨?_, ?_, rfl⟩
  · unfold VQ_sq_monopole responsePrefactor
    field_simp [hv]
  · unfold VQ_sq_monopole responsePrefactor responseAcceleration
    field_simp [hv, hr]

/-- PHYSICS: primary linear Poisson response closure ∇²Φ_resp = κ n (TeX Assumption poisson). -/
axiom physics_poisson_response_closure : Prop

/--
PHYSICAL READING (not an independent CQ/r postulate): separate long-range response field
compatible with the same IR law from `physics_poisson_response_closure`.
-/
axiom physics_separate_response_field_reading : Prop

/--
PHYSICAL READING (not an independent CQ/r postulate): unified/modified gravity
compatible with the same IR law from `physics_poisson_response_closure`.
-/
axiom physics_unified_gravity_reading : Prop

/--
TeX: thm:flat-rotation — Flat response rotation.
If circular balance is `v_c² / r = C Q / r` with nonzero radius, then `v_c² = C Q`.
-/
theorem thm_flat_rotation
    (C Q r vc : ℝ)
    (hr : r ≠ 0)
    (hbalance : vc^2 / r = C * Q / r) :
    vc^2 = C * Q := by
  field_simp [hr] at hbalance
  exact hbalance

/-- Alias used by older scaffolding. -/
theorem flat_rotation
    (C Q r vc : ℝ)
    (hr : r ≠ 0)
    (hbalance : vc^2 / r = C * Q / r) :
    vc^2 = C * Q :=
  thm_flat_rotation C Q r vc hr hbalance

/-- Flat law packaged with the Poisson+monopole prefactor identification. -/
theorem thm_flat_rotation_from_poisson_halo
    (κ v Q r vc : ℝ)
    (_hv : v ≠ 0)
    (hr : r ≠ 0)
    (hbalance :
      vc^2 / r =
        responseAcceleration (responsePrefactor κ v) Q r) :
    vc^2 = responsePrefactor κ v * Q := by
  unfold responseAcceleration at hbalance
  exact thm_flat_rotation (responsePrefactor κ v) Q r vc hr hbalance

end

end Paper2
