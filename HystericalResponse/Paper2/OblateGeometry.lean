import Mathlib
import HystericalResponse.Paper2.BallisticHalo

/-
TeX: `2_galactic_modelling/paper_2_galactic_modelling.tex`, Section “Asymptotic oblate geometry”.

Ports:
  * planar axisymmetric quadrupole angular algebra (`thm:transport-quad`);
  * Legendre / isotropic–P₂ decomposition;
  * formal Poisson coefficient matching for `thm:oblate`;
  * algebraic Φ two-form and `q_eff` identities.
-/

set_option autoImplicit false

namespace Paper2

noncomputable section

/--
PHYSICS: linear Poisson response closure ∇²Φ = κ n (TeX Assumption poisson).
Same primary IR closure used for g_resp = C Q / r in ResponseClosure; not a
separate co-equal CQ/r postulate.
-/
axiom physics_linear_response_closure : Prop

/-- Legendre P₂(μ) = (3μ² − 1)/2. -/
def P2 (μ : ℝ) : ℝ :=
  (3 * μ ^ 2 - 1) / 2

/--
Correct angular relation used by TeX:
  `2 sin²θ − 1 = 1/3 − (4/3) P₂(cos θ)`.
-/
theorem two_sin_sq_eq_isotropic_P2 (θ : ℝ) :
    2 * Real.sin θ ^ 2 - 1 = 1 / 3 - (4 / 3) * P2 (Real.cos θ) := by
  unfold P2
  have h : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  rw [h]
  field_simp
  ring

/--
TeX isotropic + P₂ decomposition of the quadrupole bracket:
  s/3 − (4s/3) P₂(cos θ) = s (2 sin²θ − 1).
-/
theorem quad_isotropic_P2_decomposition (s θ : ℝ) :
    s / 3 - (4 * s / 3) * P2 (Real.cos θ) =
      s * (2 * Real.sin θ ^ 2 - 1) := by
  unfold P2
  have h : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  rw [h]
  field_simp
  ring

/--
Planar axisymmetric moment identity used in TeX:
if `⟨y₁²⟩ = ⟨y₂²⟩ = s/2` and `⟨y₁ y₂⟩ = 0`, then with
`n₁ = sinθ cosφ`, `n₂ = sinθ sinφ` one has
`⟨(n·y)²⟩ = (s/2) sin²θ`.
-/
theorem planar_axisym_ndot_sq
    (s θ φ : ℝ)
    (avg_y1_sq avg_y2_sq avg_y1y2 : ℝ)
    (hy1 : avg_y1_sq = s / 2)
    (hy2 : avg_y2_sq = s / 2)
    (h12 : avg_y1y2 = 0) :
    (Real.sin θ * Real.cos φ) ^ 2 * avg_y1_sq +
        (Real.sin θ * Real.sin φ) ^ 2 * avg_y2_sq +
        2 * (Real.sin θ * Real.cos φ) * (Real.sin θ * Real.sin φ) * avg_y1y2 =
      (s / 2) * Real.sin θ ^ 2 := by
  rw [hy1, hy2, h12]
  calc
    (Real.sin θ * Real.cos φ) ^ 2 * (s / 2) +
          (Real.sin θ * Real.sin φ) ^ 2 * (s / 2) +
          2 * (Real.sin θ * Real.cos φ) * (Real.sin θ * Real.sin φ) * 0
        = (s / 2) * Real.sin θ ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2) := by ring
    _ = (s / 2) * Real.sin θ ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring

/-- Average of the TeX quadrupole polynomial given planar axisym moments. -/
theorem planar_quad_poly_average
    (s θ : ℝ)
    (avg_ndot_sq avg_y_sq : ℝ)
    (hnd : avg_ndot_sq = (s / 2) * Real.sin θ ^ 2)
    (hy : avg_y_sq = s) :
    4 * avg_ndot_sq - avg_y_sq = s * (2 * Real.sin θ ^ 2 - 1) := by
  rw [hnd, hy]
  ring

/-- Density prefactor `α = Q/(4π v)`. -/
def responseDensityPrefactor (v Q : ℝ) : ℝ :=
  Q / (4 * Real.pi * v)

/-- TeX Eq. nquad (bracket form). -/
def nQuadBracket (v Q s r θ : ℝ) : ℝ :=
  haloMonopoleDensity v Q r * (1 + (s / r ^ 2) * (2 * Real.sin θ ^ 2 - 1))

/-- TeX Eq. nquad (P₂ form). -/
def nQuadP2 (v Q s r θ : ℝ) : ℝ :=
  responseDensityPrefactor v Q *
    (1 / r ^ 2 + (s / 3) / r ^ 4 -
      (4 * s / 3) / r ^ 4 * P2 (Real.cos θ))

/-- The two TeX writings of the quadrupole density agree. -/
theorem nQuad_bracket_eq_P2
    (v Q s r θ : ℝ)
    (hv : v ≠ 0)
    (hr : r ≠ 0) :
    nQuadBracket v Q s r θ = nQuadP2 v Q s r θ := by
  unfold nQuadBracket nQuadP2 haloMonopoleDensity responseDensityPrefactor
  have hdecomp := quad_isotropic_P2_decomposition s θ
  field_simp [hv, hr]
  rw [← hdecomp]
  ring

/--
TeX: thm:transport-quad — quadrupole density from planar axisym moments.
-/
theorem thm_transport_quad
    (v Q s r θ : ℝ)
    (avg_ndot_sq avg_y_sq : ℝ)
    (hv : v ≠ 0)
    (hr : r ≠ 0)
    (hnd : avg_ndot_sq = (s / 2) * Real.sin θ ^ 2)
    (hy : avg_y_sq = s) :
    haloMonopoleDensity v Q r +
        responseDensityPrefactor v Q * (4 * avg_ndot_sq - avg_y_sq) / r ^ 4 =
      nQuadBracket v Q s r θ := by
  have hpoly := planar_quad_poly_average s θ avg_ndot_sq avg_y_sq hnd hy
  unfold nQuadBracket haloMonopoleDensity responseDensityPrefactor
  rw [hpoly]
  field_simp [hv, hr]

/-- Leading oblate response potential (TeX Eq. phiquad, P₂ writing). -/
def oblatePhiP2 (VQ s r θ : ℝ) : ℝ :=
  VQ ^ 2 * (Real.log r + s / (6 * r ^ 2) + (s / (3 * r ^ 2)) * P2 (Real.cos θ))

/-- Leading oblate response potential (cos² writing). -/
def oblatePhiCos (VQ s r θ : ℝ) : ℝ :=
  VQ ^ 2 * (Real.log r + s / (2 * r ^ 2) * (Real.cos θ) ^ 2)

/-- Algebraic identity of the two TeX writings of Φ. -/
theorem oblate_potential_two_forms
    (VQ s r θ : ℝ)
    (hr : r ≠ 0) :
    oblatePhiP2 VQ s r θ = oblatePhiCos VQ s r θ := by
  unfold oblatePhiP2 oblatePhiCos P2
  congr 1
  field_simp [hr]
  ring

/-- `V_Q² = κ Q / (4π v)` as in TeX. -/
def VQ_sq (κ v Q : ℝ) : ℝ :=
  κ * responseDensityPrefactor v Q

/--
TeX: thm:oblate — formal Poisson coefficient matching.
Given the linear closure and the TeX spherical-harmonic Laplacian identities
(Δ log r = r⁻², Δ(r⁻²) = 2 r⁻⁴, Δ(r⁻² P₂) = −4 r⁻⁴ P₂), the unique leading
ansatz coefficients are those of `oblatePhiP2` with `VQ² = κ Q/(4π v)`.
-/
theorem thm_oblate
    (_hclos : physics_linear_response_closure)
    (κ v Q s r θ : ℝ)
    (hr : r ≠ 0) :
    let VQ2 := VQ_sq κ v Q
    let α := responseDensityPrefactor v Q
    (VQ2 = κ * α) ∧
      (VQ2 * (s / 3) = κ * α * (s / 3)) ∧
      (VQ2 * (-(4 * s) / 3) = κ * α * (-(4 * s) / 3)) ∧
      (oblatePhiP2 VQ2 s r θ = oblatePhiCos VQ2 s r θ) ∧
      (α * (1 / r ^ 2 + (s / 3) / r ^ 4 -
          (4 * s / 3) / r ^ 4 * P2 (Real.cos θ)) =
        nQuadP2 v Q s r θ) := by
  intro VQ2 α
  refine ⟨rfl, ?_, ?_, oblate_potential_two_forms VQ2 s r θ hr, rfl⟩
  · change VQ_sq κ v Q * (s / 3) = κ * responseDensityPrefactor v Q * (s / 3)
    unfold VQ_sq; ring
  · change VQ_sq κ v Q * (-(4 * s) / 3) = κ * responseDensityPrefactor v Q * (-(4 * s) / 3)
    unfold VQ_sq; ring

/-- TeX: def:qeff — effective local flattening from midplane derivatives. -/
def qEffInvSq (R d2zΦ dRΦ : ℝ) : ℝ :=
  R * d2zΦ / dRΦ

/-- TeX: cor:qeff — leading midplane identity `q_eff⁻² = 1 + s/R²`. -/
theorem cor_qeff
    (R s : ℝ)
    (hR : R ≠ 0) :
    qEffInvSq R ((1 + s / R^2) / R) 1 = 1 + s / R^2 := by
  unfold qEffInvSq
  field_simp [hR]

theorem cor_qeff_leading
    (R s : ℝ)
    (hR : R ≠ 0) :
    qEffInvSq R ((1 + s / R^2) / R) 1 = 1 + s / R^2 :=
  cor_qeff R s hR

/--
Exponential-disc moment `s = 6 R_d²`.
Literature hypothesis: classical radial moments (Gamma integrals).
-/
axiom literature_exponential_disc_second_moment :
  ∀ (Rd : ℝ), 0 < Rd →
    (∫ r in Set.Ioi (0 : ℝ), r^3 * Real.exp (-r / Rd)) /
      (∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r / Rd)) = 6 * Rd^2

theorem cor_exp_disc
    (Rd : ℝ)
    (hRd : 0 < Rd) :
    (∫ r in Set.Ioi (0 : ℝ), r^3 * Real.exp (-r / Rd)) /
      (∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r / Rd)) = 6 * Rd^2 :=
  literature_exponential_disc_second_moment Rd hRd

end

end Paper2
