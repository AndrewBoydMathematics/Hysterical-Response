import Mathlib

/-!
TeX: `6_cosmological_constant/paper_6_late_universe.tex`,
Section “Nonlinear cosmological attractor”.

Cubic pitchfork algebra and dilution-cancellation identities.
Compiler certification: `lake build HystericalResponse.Paper6_LateUniverse_Spec`.
-/

set_option autoImplicit false

namespace Paper6

noncomputable section

/-- Cubic normal-form vector field f(phi)=r*phi-u*phi^3. -/
def cubicField (r u φ : ℝ) : ℝ := r * φ - u * φ ^ 3

/-- TeX: the neutral state is always an equilibrium. -/
theorem thm_neutral_equilibrium (r u : ℝ) : cubicField r u 0 = 0 := by
  simp [cubicField]

/-- TeX: thm:pitchfork — algebraic nonzero equilibria from φ² = r/u. -/
theorem thm_nonzero_equilibrium_of_square
    {r u φ : ℝ} (hu : u ≠ 0) (hφ : φ ^ 2 = r / u) :
    cubicField r u φ = 0 := by
  rw [cubicField]
  have hru : u * φ ^ 2 = r := by
    rw [hφ]
    field_simp
  calc
    r * φ - u * φ ^ 3 = r * φ - (u * φ ^ 2) * φ := by ring
    _ = 0 := by rw [hru]; ring

/-- TeX: branch linearization r − 3uφ² = −2r on a nonzero pitchfork branch. -/
theorem thm_branch_linearization
    {r u φ : ℝ} (h : u * φ ^ 2 = r) :
    r - 3 * u * φ ^ 2 = -2 * r := by
  calc
    r - 3 * u * φ ^ 2 = r - 3 * (u * φ ^ 2) := by ring
    _ = r - 3 * r := by rw [h]
    _ = -2 * r := by ring

/-- TeX: for r > 0 the linearization on a nonzero branch is negative. -/
theorem thm_branch_stable_sign
    {r u φ : ℝ} (hr : 0 < r) (h : u * φ ^ 2 = r) :
    r - 3 * u * φ ^ 2 < 0 := by
  rw [thm_branch_linearization h]
  linarith

/-- Dilution-driven gain G=(a/ac)^3. -/
def gain (a ac : ℝ) : ℝ := (a / ac) ^ 3

/-- Squared adiabatic branch amplitude. -/
def phiSqStar (r0 u a ac : ℝ) : ℝ := (r0 / u) * (gain a ac - 1)

/-- Matter density normalized as rho_m0 a^-3. -/
def rhoM (rhoM0 a : ℝ) : ℝ := rhoM0 / a ^ 3

/-- Quadratic gravitational response closure on the branch. -/
def rhoHStar (C rhoM0 r0 u a ac : ℝ) : ℝ :=
  C * rhoM rhoM0 a * phiSqStar r0 u a ac

/-- TeX: thm:attractor — main dilution-cancellation identity. -/
theorem thm_rhoHStar_identity
    {C rhoM0 r0 u a ac : ℝ}
    (ha : a ≠ 0) (hac : ac ≠ 0) (hu : u ≠ 0) :
    rhoHStar C rhoM0 r0 u a ac =
      C * rhoM0 * (r0 / u) * (1 / ac ^ 3 - 1 / a ^ 3) := by
  simp [rhoHStar, rhoM, phiSqStar, gain]
  field_simp

/-- TeX: present-to-asymptotic fraction is 1 − a_c³ when a₀ = 1. -/
theorem thm_present_fraction_identity
    {ac : ℝ} (hac : ac ≠ 0) :
    (1 / ac ^ 3 - 1) / (1 / ac ^ 3) = 1 - ac ^ 3 := by
  field_simp

/-- Effective equation of state −1 − 1/(G−1). -/
def wEff (G : ℝ) : ℝ := -1 - 1 / (G - 1)

/-- TeX: thm:w — effective equation of state below −1 for supercritical gain. -/
theorem thm_wEff_lt_neg_one {G : ℝ} (hG : 1 < G) : wEff G < -1 := by
  unfold wEff
  have hpos : 0 < G - 1 := sub_pos.mpr hG
  have hinv : 0 < 1 / (G - 1) := one_div_pos.mpr hpos
  linarith

/-- The coefficient combination B required by a present ratio X0. -/
def requiredB (X0 zc : ℝ) : ℝ := X0 / ((1 + zc) ^ 3 - 1)

/-- TeX: calibration identity for required B. -/
theorem thm_requiredB_calibrates
    {X0 zc : ℝ} (h : (1 + zc) ^ 3 - 1 ≠ 0) :
    requiredB X0 zc * ((1 + zc) ^ 3 - 1) = X0 := by
  unfold requiredB
  field_simp

example : (1 + (2 : ℝ)) ^ 3 = 27 := by norm_num
example : (1 + (3 : ℝ)) ^ 3 = 64 := by norm_num
example : 1 - 1 / ((1 + (2 : ℝ)) ^ 3) = 26 / 27 := by norm_num
example : 1 - 1 / ((1 + (3 : ℝ)) ^ 3) = 63 / 64 := by norm_num
example : wEff ((1 + (2 : ℝ)) ^ 3) = -(27 : ℝ) / 26 := by norm_num [wEff]
example : wEff ((1 + (3 : ℝ)) ^ 3) = -(64 : ℝ) / 63 := by norm_num [wEff]

end

end Paper6
