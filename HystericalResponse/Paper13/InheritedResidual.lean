/-
TeX: `13_ew_cooling_baryogenesis/paper_13_ew_cooling_baryogenesis.tex`
Section “Inherited electroweak residual” / Model debye.
-/

import Mathlib

set_option autoImplicit false

namespace Paper13

noncomputable section

/-- Debye plasma stiffness ∝ T². -/
def kX (αX T : ℝ) : ℝ := αX * T ^ 2

def kY (αY T : ℝ) : ℝ := αY * T ^ 2

/-- Reciprocal Hessian determinant Δ = k_X k_Y − g². -/
def Delta (αX αY g T : ℝ) : ℝ := kX αX T * kY αY T - g ^ 2

theorem Delta_eq (αX αY g T : ℝ) :
    Delta αX αY g T = αX * αY * T ^ 4 - g ^ 2 := by
  unfold Delta kX kY
  ring

end

end Paper13
