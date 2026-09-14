import Mathlib

/-!
TeX: `11_hawking_radiation/paper_11_horizon_hysterical_response.tex`,
Section “Horizon regularity fixes the response temperature”.

`thm_temp`: algebraic identity T = κ/(2π) from β = 2π/κ.
Euclidean regularity is a literature hypothesis (not proved here).
-/

set_option autoImplicit false

namespace Paper11

noncomputable section

/-- TeX: lit:period — Euclidean regularity ⇒ KMS period (literature). -/
axiom literature_euclidean_period : True

/-- Temperature from inverse period. -/
def temperatureFromBeta (beta : ℝ) : ℝ := 1 / beta

/-- TeX: thm:temp — Hawking temperature from the Euclidean period. -/
theorem thm_temp {kappa beta : ℝ}
    (hk : kappa ≠ 0) (hbeta : beta = 2 * Real.pi / kappa) :
    temperatureFromBeta beta = kappa / (2 * Real.pi) := by
  unfold temperatureFromBeta
  rw [hbeta]
  field_simp

/-- Schwarzschild specialization: κ = 1/(4M) ⇒ T = 1/(8πM). -/
theorem schwarzschild_temperature {M kappa T : ℝ}
    (hM : M ≠ 0) (hk : kappa = 1 / (4 * M))
    (hT : T = kappa / (2 * Real.pi)) :
    T = 1 / (8 * Real.pi * M) := by
  rw [hT, hk]
  field_simp
  ring

end

end Paper11
