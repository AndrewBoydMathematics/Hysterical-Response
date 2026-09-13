import Mathlib

/-!
TeX: `4_solar_system/paper_4_solar_system_null_test.tex`,
Section “Subcritical point-source response”.

Ports the Solar specialization of the far-field response law
`g_resp = V_⊙² / r`, the fractional response `ε(r)`, and the equivalent
enclosed-mass identity `M_resp(<r) = V_⊙² r / G`.
-/

set_option autoImplicit false

namespace Paper4

noncomputable section

/-- TeX Eq. gresp: Solar residual acceleration `g_resp = V² / r`. -/
def gResp (V2 r : ℝ) : ℝ :=
  V2 / r

/-- Newtonian Solar acceleration `g_N = GM / r²`. -/
def gN (GM r : ℝ) : ℝ :=
  GM / r ^ 2

/-- TeX Eq. epsilon: fractional response `ε(r) = V² r / (GM)`. -/
def epsilon (V2 GM r : ℝ) : ℝ :=
  V2 * r / GM

/-- TeX Definition mresp: equivalent enclosed response mass. -/
def Mresp (V2 G r : ℝ) : ℝ :=
  V2 * r / G

/--
TeX: specialization of `g_resp = V²/r` matching `ε = g_resp / g_N`.

Faithful algebraic port of `ε(r) = V² r / (GM)` from the quotient of the two
accelerations (away from `r = 0`).
-/
theorem epsilon_eq_gResp_div_gN
    (V2 GM r : ℝ) (hr : r ≠ 0) :
    epsilon V2 GM r = gResp V2 r / gN GM r := by
  unfold epsilon gResp gN
  field_simp [hr]

/--
TeX Definition mresp: `g_resp = G M_resp / r²` rearranges to
`M_resp = V² r / G` when `g_resp = V² / r`.
-/
theorem gResp_eq_G_Mresp_div_r_sq
    (V2 G r : ℝ) (hr : r ≠ 0) (hG : G ≠ 0) :
    gResp V2 r = G * Mresp V2 G r / r ^ 2 := by
  unfold gResp Mresp
  field_simp [hr, hG]

end

end Paper4
