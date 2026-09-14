import Mathlib

/-
TeX: `15_btfr_zero_point/paper_15_btfr_zero_point.tex`,
Section “IR memory acceleration”.
-/

set_option autoImplicit false

namespace Paper15

noncomputable section

/-- TeX: lit:period — Euclidean/KMS period β = 2π/κ. -/
axiom literature_euclidean_horizon_period : True

/-- TeX: lit:cosmo-kappa — cosmological horizon κ = H₀. -/
axiom literature_cosmo_horizon_surface_gravity : True

/--
TeX: thm:aIR — a_IR = c/β with β = 2π/κ and κ = H₀ gives a_IR = H₀ c / 2π.
-/
theorem thm_aIR
    (H0 c β κ aIR : ℝ)
    (hβ : β = (2 * Real.pi) / κ)
    (hκ : κ = H0)
    (hpos : κ ≠ 0)
    (ha : aIR = c / β) :
    aIR = H0 * c / (2 * Real.pi) := by
  have hβ' : β = (2 * Real.pi) / H0 := by simp [hβ, hκ]
  have hH0 : H0 ≠ 0 := by simpa [hκ] using hpos
  calc
    aIR = c / β := ha
    _ = c / ((2 * Real.pi) / H0) := by rw [hβ']
    _ = c * (H0 / (2 * Real.pi)) := by field_simp [hH0]
    _ = H0 * c / (2 * Real.pi) := by ring

end

end Paper15
