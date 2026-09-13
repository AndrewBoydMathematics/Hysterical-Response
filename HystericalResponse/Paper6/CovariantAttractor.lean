import Mathlib

/-!
TeX: `6_cosmological_constant/paper_6_late_universe.tex`,
Section “Critical density and covariant positivity”.

Scalar algebraic skeleton: critical density, attractor density, constant pressure,
active gravitational density, and emergent cosmological term.
Compiler certification: `lake build HystericalResponse.Paper6_LateUniverse_Spec`.
-/

set_option autoImplicit false

namespace Paper6

noncomputable section

/-- Linear-gap critical density n_c = Gamma / K. -/
def criticalDensity (Gamma K : ℝ) : ℝ := Gamma / K

/-- Leading attractor coefficient A = C2 * m * r0 / u. -/
def attractorCoeff (C2 m r0 u : ℝ) : ℝ := C2 * m * r0 / u

/-- Broken-phase Hysterical mass density A (n_c - n). -/
def rhoH (A nc n : ℝ) : ℝ := A * (nc - n)

/-- Asymptotic Hysterical mass density A n_c. -/
def rhoInf (A nc : ℝ) : ℝ := A * nc

/-- Effective pressure in c=1 units. -/
def pH (A nc : ℝ) : ℝ := -(A * nc)

/-- Active FLRW gravitational density rho + 3 p in c=1 units. -/
def activeDensity (A nc n : ℝ) : ℝ := rhoH A nc n + 3 * pH A nc

/-- Algebraic cosmological constant in units where the prefactor is kappa > 0. -/
def lambdaH (kappa A nc : ℝ) : ℝ := kappa * rhoInf A nc

/-- TeX: thm:critical-density — positivity of n_c = Γ/K. -/
theorem thm_criticalDensity_pos {Gamma K : ℝ}
    (hG : 0 < Gamma) (hK : 0 < K) :
    0 < criticalDensity Gamma K := by
  unfold criticalDensity
  positivity

theorem thm_pitchfork_branch_sq {r0 u G : ℝ}
    (hu : u ≠ 0) :
    u * ((r0 / u) * (G - 1)) = r0 * (G - 1) := by
  field_simp

/-- TeX: thm:positive-attractor — attractor reduction away from n = 0. -/
theorem thm_attractor_reduction
    (C2 m r0 u nc n : ℝ) (hn : n ≠ 0) (hu : u ≠ 0) :
    C2 * (m * n) * ((r0 / u) * (nc / n - 1)) =
      attractorCoeff C2 m r0 u * (nc - n) := by
  unfold attractorCoeff
  field_simp [hn, hu]

theorem thm_rhoH_eq (A nc n : ℝ) :
    rhoH A nc n = rhoInf A nc - A * n := by
  simp [rhoH, rhoInf]
  ring

theorem thm_pressure_constant (A nc n : ℝ) :
    (-A) * n - rhoH A nc n = pH A nc := by
  simp [rhoH, pH]
  ring

theorem thm_activeDensity_formula (A nc n : ℝ) :
    activeDensity A nc n = -A * (2 * nc + n) := by
  simp [activeDensity, rhoH, pH]
  ring

theorem thm_rhoH_pos {A nc n : ℝ}
    (hA : 0 < A) (hn : n < nc) :
    0 < rhoH A nc n := by
  unfold rhoH
  positivity

theorem thm_rhoInf_pos {A nc : ℝ}
    (hA : 0 < A) (hnc : 0 < nc) :
    0 < rhoInf A nc := by
  unfold rhoInf
  positivity

theorem thm_pressure_neg {A nc : ℝ}
    (hA : 0 < A) (hnc : 0 < nc) :
    pH A nc < 0 := by
  unfold pH
  have : 0 < A * nc := mul_pos hA hnc
  linarith

theorem thm_activeDensity_neg {A nc n : ℝ}
    (hA : 0 < A) (hnc : 0 < nc) (hn : 0 ≤ n) :
    activeDensity A nc n < 0 := by
  rw [thm_activeDensity_formula]
  have hsum : 0 < 2 * nc + n := by linarith
  have : 0 < A * (2 * nc + n) := mul_pos hA hsum
  linarith

theorem thm_attractorCoeff_pos {C2 m r0 u : ℝ}
    (hC : 0 < C2) (hm : 0 < m) (hr : 0 < r0) (hu : 0 < u) :
    0 < attractorCoeff C2 m r0 u := by
  unfold attractorCoeff
  positivity

/-- TeX: thm:Lambda — magnitude identity in the linear-gap class. -/
theorem thm_emergentMagnitude_linearGap (C2 m r0 u Gamma K : ℝ) :
    rhoInf (attractorCoeff C2 m r0 u) (criticalDensity Gamma K) =
      C2 * m * (r0 / u) * (Gamma / K) := by
  unfold rhoInf attractorCoeff criticalDensity
  field_simp

theorem thm_lambdaH_pos {kappa A nc : ℝ}
    (hk : 0 < kappa) (hA : 0 < A) (hnc : 0 < nc) :
    0 < lambdaH kappa A nc := by
  unfold lambdaH rhoInf
  positivity

/-- Effective equation-of-state ratio in c=1 units. -/
def wH (nc n : ℝ) : ℝ := -nc / (nc - n)

/-- TeX: cor:w-n — effective w < −1 in the broken phase. -/
theorem thm_wH_lt_neg_one {nc n : ℝ}
    (_hnc : 0 < nc) (hn : 0 < n) (hbelow : n < nc) :
    wH nc n < -1 := by
  unfold wH
  have hden : 0 < nc - n := sub_pos.mpr hbelow
  rw [div_lt_iff₀ hden]
  linarith

end

end Paper6
