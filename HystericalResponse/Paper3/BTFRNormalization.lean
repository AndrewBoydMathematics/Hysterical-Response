import Mathlib
import HystericalResponse.Paper3.AxisymmetricRadial

/-!
TeX: `3_milky_way_fit/paper_3_milky_way_response_model.tex`, Section “Normalization and the Solar circle”.

Algebraic BTFR normalization and quadrature Solar-circle identities for the
Milky Way application. Numerical Gaia comparisons and fitted \(a_{0,\mathrm{eff}}\)
are physics / observational inputs — not Lean theorems.
-/

set_option autoImplicit false

namespace Paper3

noncomputable section

/--
TeX BTFR normalization \(V_Q^4 = G a_0 M_b\) (definitional algebraic form).
Self-contained for the MW application; cf. Paper2 BTFR attractor algebra.
-/
def VQ_fourth (G a0 Mb : ℝ) : ℝ :=
  G * a0 * Mb

/-- Definitional unpacking: \(V_Q^4 = G a_0 M_b\). -/
theorem btfr_normalization_def (G a0 Mb VQ : ℝ) (h : VQ ^ 4 = G * a0 * Mb) :
    VQ ^ 4 = VQ_fourth G a0 Mb := by
  simpa [VQ_fourth] using h

/--
If \(V_Q^2 = \mathcal C Q\) and \(Q^2 = (G a_0 / \mathcal C^2) M_b\) in the BTFR
closure used by TeX, then \(V_Q^4 = G a_0 M_b\).
-/
theorem btfr_VQ_fourth_from_CQ
    (C G a0 Mb Q VQ : ℝ)
    (hC : C ≠ 0)
    (hVQ : VQ ^ 2 = C * Q)
    (hQ : Q ^ 2 = (G * a0 / C ^ 2) * Mb) :
    VQ ^ 4 = G * a0 * Mb := by
  calc
    VQ ^ 4 = (VQ ^ 2) ^ 2 := by ring
    _ = (C * Q) ^ 2 := by rw [hVQ]
    _ = C ^ 2 * Q ^ 2 := by ring
    _ = C ^ 2 * ((G * a0 / C ^ 2) * Mb) := by rw [hQ]
    _ = G * a0 * Mb := by field_simp [hC]

/-- Quadrature combination of baryonic and response circular-speed contributions. -/
def Vc_sq (Vb2 Vresp2 : ℝ) : ℝ :=
  Vb2 + Vresp2

/-- TeX: \(V_c^2 = V_b^2 + V_{\mathrm{resp}}^2\). -/
theorem Vc_sq_quadrature (Vb Vresp : ℝ) :
    Vc_sq (Vb ^ 2) (Vresp ^ 2) = Vb ^ 2 + Vresp ^ 2 :=
  rfl

/--
Solar-circle prediction identity under a given transition factor \(\mathcal T(R_0)\):
\(V_{\mathrm{resp}}^2(R_0)=V_Q^2\,\mathcal T(R_0)\) and
\(V_c(R_0)=\sqrt{V_b^2+V_{\mathrm{resp}}^2}\).
-/
theorem solar_circle_prediction
    (VQ Vb T_R0 : ℝ)
    (Vresp2 Vc : ℝ)
    (hVresp : Vresp2 = VQ ^ 2 * T_R0)
    (hVc : Vc ^ 2 = Vb ^ 2 + Vresp2) :
    Vc ^ 2 = Vb ^ 2 + VQ ^ 2 * T_R0 := by
  rw [hVc, hVresp]

/--
Specialization with exponential \(\mathcal T_d\): Solar-circle identity
\(V_c^2 = V_b^2 + V_Q^2\,\mathcal T_d(R_0/R_d)\).
-/
theorem solar_circle_prediction_Td
    (VQ Vb Rd R0 : ℝ)
    (Vc : ℝ)
    (hVc : Vc ^ 2 = Vb ^ 2 + V_resp_sq (VQ ^ 2) Rd R0) :
    Vc ^ 2 = Vb ^ 2 + VQ ^ 2 * Td (R0 / Rd) := by
  simpa [V_resp_sq] using hVc

/--
PHYSICS: adopted MW baryonic mass, \(a_0\), and Solar-circle baryonic speed are
observational / modelling inputs (TeX § Baryonic Milky Way model, Normalization).
Lean does not certify numerical Gaia Cepheid values or the quoted Solar-circle speeds.
-/
axiom physics_mw_btfr_inputs : Prop

end

end Paper3
