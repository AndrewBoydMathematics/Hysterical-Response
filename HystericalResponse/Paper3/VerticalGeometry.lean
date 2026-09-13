import Mathlib
import HystericalResponse.Paper2.OblateGeometry
import HystericalResponse.Paper3.AxisymmetricRadial

/-!
TeX: `3_milky_way_fit/paper_3_milky_way_response_model.tex`, Section “Analytic vertical geometry”
(and the algebraic near-plane \(\rho_{\mathrm{eff}}\) identity from § Vertical-geometry experiment).

Reuses Paper2 `q_eff` / exponential-disc moment algebra. Does **not** formalize Gaia
density fits, \(q_{\mathrm{fit}}\), or observational intervals.
-/

set_option autoImplicit false

namespace Paper3

noncomputable section

open Paper2

/--
Leading exponential-disc flattening estimate
\(q_{\mathrm{eff}}(R)=\bigl[1+6(R_d/R)^2\bigr]^{-1/2}\).
-/
def q_eff_exp (Rd R : ℝ) : ℝ :=
  Real.sqrt (1 / (1 + 6 * (Rd / R) ^ 2))

/--
From Paper2 `cor_qeff` with \(s=6 R_d^2\):
\(q_{\mathrm{eff}}^{-2}=1+6(R_d/R)^2\).
-/
theorem q_eff_inv_sq_exp
    (Rd R : ℝ) (hR : R ≠ 0) :
    qEffInvSq R ((1 + (6 * Rd ^ 2) / R ^ 2) / R) 1 =
      1 + 6 * (Rd / R) ^ 2 := by
  rw [cor_qeff R (6 * Rd ^ 2) hR]
  field_simp [hR]

/-- Algebraic rewrite of the TeX boxed leading estimate. -/
theorem q_eff_exp_sq_inv
    (Rd R : ℝ) :
    q_eff_exp Rd R ^ 2 = 1 / (1 + 6 * (Rd / R) ^ 2) := by
  unfold q_eff_exp
  have hnonneg : 0 ≤ 1 / (1 + 6 * (Rd / R) ^ 2) := by
    apply div_nonneg
    · norm_num
    · nlinarith [sq_nonneg (Rd / R)]
  exact Real.sq_sqrt hnonneg

/--
If \(q\neq 0\) and \(1/q^2=1+6(R_d/R)^2\), then \(q^2=q_{\mathrm{eff}}^2\)
(TeX leading quadrupole estimate, squared form).
-/
theorem q_eff_exp_matches_inv_sq
    (Rd R q : ℝ)
    (hq : q ≠ 0)
    (hinv : 1 / q ^ 2 = 1 + 6 * (Rd / R) ^ 2) :
    q ^ 2 = q_eff_exp Rd R ^ 2 := by
  rw [q_eff_exp_sq_inv, ← hinv, one_div]
  field_simp [hq]

/-- Exponential-disc second moment reused from Paper2. -/
theorem exp_disc_s_eq_six_Rd_sq
    (Rd : ℝ) (hRd : 0 < Rd) :
    (∫ r in Set.Ioi (0 : ℝ), r ^ 3 * Real.exp (-r / Rd)) /
      (∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r / Rd)) =
      6 * Rd ^ 2 :=
  cor_exp_disc Rd hRd

/--
Near-plane equivalent density for an oblate logarithmic response
\(\rho_{\mathrm{eff}}(q)=V_{\mathrm{resp}}^2/(4\pi G q^2 R_0^2)\).
-/
def rho_eff (Vresp2 G q R0 : ℝ) : ℝ :=
  Vresp2 / (4 * Real.pi * G * q ^ 2 * R0 ^ 2)

/-- Algebraic identity matching TeX \(K_z\simeq 4\pi G\rho_{\mathrm{eff}} z\). -/
theorem rho_eff_of_near_plane_Kz
    (Vresp2 G q R0 : ℝ)
    (hq : q ≠ 0) (hR0 : R0 ≠ 0) (hG : G ≠ 0) :
    Vresp2 / (q ^ 2 * R0 ^ 2) = 4 * Real.pi * G * rho_eff Vresp2 G q R0 := by
  unfold rho_eff
  field_simp [hq, hR0, hG]

/--
TeX: prop:rho-eff — Near-plane equivalent density.
From the oblate logarithmic response \(K_z\simeq V_{\mathrm{resp}}^2 z/(q^2 R_0^2)\)
matched to \(K_z\simeq 4\pi G\rho_{\mathrm{eff}} z\), one has
\(\rho_{\mathrm{eff}}=V_{\mathrm{resp}}^2/(4\pi G q^2 R_0^2)\).
-/
theorem prop_rho_eff
    (Vresp2 G q R0 : ℝ)
    (hq : q ≠ 0) (hR0 : R0 ≠ 0) (hG : G ≠ 0) :
    Vresp2 / (q ^ 2 * R0 ^ 2) = 4 * Real.pi * G * rho_eff Vresp2 G q R0 :=
  rho_eff_of_near_plane_Kz Vresp2 G q R0 hq hR0 hG

/-- TeX: cor:qth algebraic form (leading exponential-disc estimate). -/
theorem cor_qth
    (Rd R : ℝ) (hR : R ≠ 0) :
    qEffInvSq R ((1 + (6 * Rd ^ 2) / R ^ 2) / R) 1 =
      1 + 6 * (Rd / R) ^ 2 :=
  q_eff_inv_sq_exp Rd R hR

/--
PHYSICS: Gaia K-dwarf vertical density, geometric \(q_{\mathrm{fit}}\), and numerical
\(\rho_{\mathrm{eff}}\) at \(q_{\mathrm{th}}=0.80\) are observational / numerical
experiment outputs (TeX § Vertical-geometry experiment). Not Lean theorems.
-/
axiom physics_gaia_vertical_experiment : Prop

end

end Paper3
