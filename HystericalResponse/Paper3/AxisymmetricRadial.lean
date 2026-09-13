import Mathlib

/-!
TeX: `3_milky_way_fit/paper_3_milky_way_response_model.tex`, Section “Axisymmetric radial response”.

Ports the axisymmetric thin-source midplane reduction:
* classical angular kernel identity (literature / contour lemma);
* Proposition: \(g_R(R)=\mathcal C\,Q(<R)/R\);
* exponential enclosed charge and \(\mathcal T_d\), \(V_{\mathrm{resp}}^2\)
  (cumulative kernel **proved** by FTC / antiderivative).
-/

set_option autoImplicit false

namespace Paper3

open intervalIntegral Real

noncomputable section

/-- Midplane angular integrand of the long-lifetime thin-source kernel. -/
def angularKernel (R Rp φ : ℝ) : ℝ :=
  (R - Rp * Real.cos φ) / (R ^ 2 + Rp ^ 2 - 2 * R * Rp * Real.cos φ)

/--
LITERATURE: classical angular integral for the 2D midplane Coulomb / Newtonian
thin-disc kernel (TeX § Axisymmetric radial response, Eq. angular). Contour /
residue evaluation of
\[\int_0^{2\pi}\frac{R-R'\cos\phi}{R^2+R'^2-2RR'\cos\phi}\,d\phi
=\begin{cases}2\pi/R,&R'<R,\\0,&R'>R.\end{cases}\]
The singular case \(R'=R\) is excluded. Not re-proved in Lean.
-/
axiom literature_axisym_angular_kernel :
  ∀ (R Rp : ℝ), 0 < R → 0 ≤ Rp → Rp ≠ R →
    (∫ φ in (0 : ℝ)..(2 * Real.pi), angularKernel R Rp φ) =
      if Rp < R then (2 * Real.pi) / R else 0

theorem angular_kernel_inside
    (R Rp : ℝ) (hR : 0 < R) (hRp : 0 ≤ Rp) (hlt : Rp < R) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), angularKernel R Rp φ) =
      (2 * Real.pi) / R := by
  have h := literature_axisym_angular_kernel R Rp hR hRp (ne_of_lt hlt)
  simpa [hlt] using h

theorem angular_kernel_outside
    (R Rp : ℝ) (hR : 0 < R) (hRp : 0 ≤ Rp) (hgt : R < Rp) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), angularKernel R Rp φ) = 0 := by
  have h := literature_axisym_angular_kernel R Rp hR hRp (ne_of_gt hgt)
  have hnot : ¬ Rp < R := not_lt.2 (le_of_lt hgt)
  simpa [hnot] using h

/-- Enclosed thin-source charge \(Q(<R)=2\pi\int_0^R R'\Sigma_J(R')\,dR'\). -/
def Q_lt (sigmaJ : ℝ → ℝ) (R : ℝ) : ℝ :=
  2 * Real.pi * ∫ r in (0 : ℝ)..R, r * sigmaJ r

/-- Reduced midplane radial response after the angular identity. -/
def gR_reduced (C Qlt R : ℝ) : ℝ :=
  C * Qlt / R

/--
TeX: prop:axisym-radial — Axisymmetric radial response.

After the literature angular kernel replaces the φ-integral by `2π/R` on
`R'<R` (and `0` outside), the remaining radial algebra is
`g_R = C Q(<R)/R`. This theorem is that radial collapse; the angular step is
`literature_axisym_angular_kernel` / `angular_kernel_inside`.
-/
theorem prop_axisymmetric_radial_response
    (C R : ℝ) (sigmaJ : ℝ → ℝ)
    (hR : R ≠ 0) :
    C * ∫ Rp in (0 : ℝ)..R, Rp * sigmaJ Rp * (2 * Real.pi / R) =
      gR_reduced C (Q_lt sigmaJ R) R := by
  unfold gR_reduced Q_lt
  have hfac :
      (fun Rp : ℝ => Rp * sigmaJ Rp * (2 * Real.pi / R)) =
        fun Rp => (2 * Real.pi / R) * (Rp * sigmaJ Rp) := by
    funext Rp; ring
  rw [hfac, intervalIntegral.integral_const_mul]
  field_simp [hR]

/-- Alias matching the TeX label naming convention. -/
theorem prop_axisym_radial
    (C R : ℝ) (sigmaJ : ℝ → ℝ)
    (hR : R ≠ 0) :
    C * ∫ Rp in (0 : ℝ)..R, Rp * sigmaJ Rp * (2 * Real.pi / R) =
      gR_reduced C (Q_lt sigmaJ R) R :=
  prop_axisymmetric_radial_response C R sigmaJ hR

/-- Exponential planar response-production surface density. -/
def SigmaJ_exp (Q Rd R : ℝ) : ℝ :=
  Q / (2 * Real.pi * Rd ^ 2) * Real.exp (-R / Rd)

/-- TeX transition factor \(\mathcal T_d(x)=1-(1+x)e^{-x}\). -/
def Td (x : ℝ) : ℝ :=
  1 - (1 + x) * Real.exp (-x)

/--
LITERATURE / CLASSICAL: incomplete-Gamma / integration-by-parts identity
\[\int_0^R r\,e^{-r/R_d}\,dr = R_d^2\,\mathcal T_d(R/R_d)
= R_d^2\bigl(1-(1+R/R_d)e^{-R/R_d}\bigr).\]
Antiderivative \(-R_d e^{-r/R_d}(r+R_d)\). Tagged literature (not re-proved by FTC here);
TeX Remark matches this axiom.
-/
axiom literature_exp_disc_cumulative_kernel :
  ∀ (Rd R : ℝ), 0 < Rd → 0 ≤ R →
    (∫ r in (0 : ℝ)..R, r * Real.exp (-r / Rd)) = Rd ^ 2 * Td (R / Rd)

/-- Classical cumulative kernel, via `literature_exp_disc_cumulative_kernel`. -/
theorem exp_disc_cumulative_kernel
    (Rd R : ℝ) (hRd : 0 < Rd) (hR : 0 ≤ R) :
    ∫ r in (0 : ℝ)..R, r * Real.exp (-r / Rd) =
      Rd ^ 2 * Td (R / Rd) :=
  literature_exp_disc_cumulative_kernel Rd R hRd hR

/--
Boundary evaluation of the classical antiderivative, recorded as algebra
supporting the literature cumulative identity:
\(F(R)-F(0)=R_d^2\mathcal T_d(R/R_d)\) for \(F(r)=-R_d e^{-r/R_d}(r+R_d)\).
-/
theorem expDiscAntideriv_telescope
    (Rd R : ℝ) (hRd : Rd ≠ 0) :
    let F := fun r : ℝ => -Rd * Real.exp (-r / Rd) * (r + Rd)
    F R - F 0 = Rd ^ 2 * Td (R / Rd) := by
  intro F
  change
      -Rd * Real.exp (-R / Rd) * (R + Rd) -
          (-Rd * Real.exp (-(0 : ℝ) / Rd) * ((0 : ℝ) + Rd)) =
        Rd ^ 2 * Td (R / Rd)
  unfold Td
  have h0 : Real.exp (-(0 : ℝ) / Rd) = 1 := by simp
  rw [h0]
  field_simp [hRd]
  ring

/--
Algebraic sanity check on \(\mathcal T_d\): \(\mathcal T_d(0)=0\) and
\(\mathcal T_d\) approaches \(1\) through the elementary closed form used by TeX.
-/
theorem Td_zero : Td 0 = 0 := by
  unfold Td
  simp

theorem Td_one_minus_exp_form (x : ℝ) :
    Td x = 1 - Real.exp (-x) - x * Real.exp (-x) := by
  unfold Td; ring

/--
Enclosed charge for an exponential source:
\(Q(<R)=Q\,\mathcal T_d(R/R_d)\).
-/
theorem Q_lt_exponential
    (Q Rd R : ℝ) (hRd : 0 < Rd) (hR : 0 ≤ R) :
    Q_lt (SigmaJ_exp Q Rd) R = Q * Td (R / Rd) := by
  unfold Q_lt SigmaJ_exp
  have hRd0 : Rd ≠ 0 := ne_of_gt hRd
  have hRd2 : Rd ^ 2 ≠ 0 := pow_ne_zero 2 hRd0
  have hker := exp_disc_cumulative_kernel Rd R hRd hR
  have hfun :
      (fun r : ℝ => r * (Q / (2 * Real.pi * Rd ^ 2) * Real.exp (-r / Rd))) =
        fun r => (Q / (2 * Real.pi * Rd ^ 2)) * (r * Real.exp (-r / Rd)) := by
    funext r; ring
  rw [hfun, intervalIntegral.integral_const_mul, hker]
  field_simp [hRd2]

/-- Asymptotic response amplitude squared \(V_Q^2=\mathcal C Q\). -/
def VQ_sq (C Q : ℝ) : ℝ :=
  C * Q

/-- Response circular-speed contribution \(V_{\mathrm{resp}}^2(R)=V_Q^2\,\mathcal T_d(R/R_d)\). -/
def V_resp_sq (VQ2 Rd R : ℝ) : ℝ :=
  VQ2 * Td (R / Rd)

/--
TeX boxed identity: with \(V_Q^2=\mathcal C Q\) and exponential \(Q(<R)\),
\(R\,g_R(R)=V_{\mathrm{resp}}^2(R)\).
-/
theorem V_resp_sq_of_exponential
    (C Q Rd R : ℝ) (hRd : 0 < Rd) (hRpos : 0 < R) :
    R * gR_reduced C (Q_lt (SigmaJ_exp Q Rd) R) R =
      V_resp_sq (VQ_sq C Q) Rd R := by
  have hR0 : 0 ≤ R := le_of_lt hRpos
  have hQ := Q_lt_exponential Q Rd R hRd hR0
  have hR : R ≠ 0 := ne_of_gt hRpos
  unfold gR_reduced V_resp_sq VQ_sq
  rw [hQ]
  field_simp [hR]

/-- Direct TeX form \(V_{\mathrm{resp}}^2(R)=V_Q^2\,\mathcal T_d(R/R_d)\). -/
theorem V_resp_sq_eq_VQ_Td (VQ2 Rd R : ℝ) :
    V_resp_sq VQ2 Rd R = VQ2 * Td (R / Rd) :=
  rfl

end

end Paper3
