import Mathlib

/-!
TeX: `11_hawking_radiation/paper_11_horizon_hysterical_response.tex`,
Section “Backreaction as feedback”.

`thm_evap` and `prop_feedback` algebraic consequences of Ḋ = -C/M².
-/

set_option autoImplicit false

namespace Paper11

/-- Candidate integrated solution of dM/dt = -C/M². -/
def massCube (M0 C t : ℝ) : ℝ := M0 ^ 3 - 3 * C * t

/-- TeX: thm:evap — extinction time of the cubic mass law. -/
theorem thm_evap {M0 C : ℝ} (hC : C ≠ 0) :
    massCube M0 C (M0 ^ 3 / (3 * C)) = 0 := by
  unfold massCube
  field_simp
  ring

theorem massCube_increment (M0 C t dt : ℝ) :
    massCube M0 C (t + dt) = massCube M0 C t - 3 * C * dt := by
  unfold massCube
  ring

/-- TeX: prop:feedback — smaller mass is hotter. -/
theorem prop_smaller_mass_hotter {theta Msmall Mlarge : ℝ}
    (ht : 0 < theta) (hs : 0 < Msmall) (hl : 0 < Mlarge)
    (hm : Msmall < Mlarge) :
    theta / Mlarge < theta / Msmall :=
  (div_lt_div_iff₀ hl hs).2 (by nlinarith)

/-- TeX: prop:feedback — smaller mass radiates more power ∝ 1/M². -/
theorem prop_smaller_mass_more_power {C Msmall Mlarge : ℝ}
    (hC : 0 < C) (hs : 0 < Msmall) (hl : 0 < Mlarge)
    (hsq : Msmall ^ 2 < Mlarge ^ 2) :
    C / Mlarge ^ 2 < C / Msmall ^ 2 := by
  rw [div_lt_div_iff₀ (sq_pos_of_pos hl) (sq_pos_of_pos hs)]
  nlinarith

end Paper11
