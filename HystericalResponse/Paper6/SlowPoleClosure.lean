import Mathlib

/-!
TeX: `6_cosmological_constant/paper_6_late_universe.tex`,
Section “Slow-pole nonlinear closure”.

Elementary algebraic/sign skeleton for slow-pole closure.
Compiler certification: `lake build HystericalResponse.Paper6_LateUniverse_Spec`.
-/

set_option autoImplicit false

namespace Paper6

noncomputable section

/-- TeX: thm:pole-match — matched linear powers cancel, leaving N/K. -/
theorem thm_pole_matched_powers
    (N K n : ℝ) (hK : K ≠ 0) (hn : n ≠ 0) :
    (N * n) / (K * n) = N / K := by
  field_simp [hK, hn]

/-- Algebraic critical density from Jacobian threshold Kn = Γ. -/
theorem thm_jacobian_threshold_density
    {K n Gamma : ℝ} (hK : K ≠ 0) (h : K * n = Gamma) :
    n = Gamma / K :=
  (eq_div_iff hK).2 (by simpa [mul_comm] using h)


/-- TeX: stationary memory relation implies n·q = nc·Y. -/
theorem thm_stationary_memory_relation
    {K n q Gamma Y nc : ℝ}
    (hK : K ≠ 0)
    (hstat : K * n * q = Gamma * Y)
    (hcrit : nc * K = Gamma) :
    n * q = nc * Y := by
  have hk : K * (n * q) = K * (nc * Y) := by
    calc
      K * (n * q) = K * n * q := by ring
      _ = Gamma * Y := hstat
      _ = (nc * K) * Y := by rw [hcrit]
      _ = K * (nc * Y) := by ring
  exact mul_left_cancel₀ hK hk

/-- TeX: cor:amplitude — reciprocal projection under stationary memory. -/
theorem thm_reciprocal_projection_closure
    (m n q Y nc : ℝ)
    (hmem : n * q = nc * Y) :
    m * n * q * Y = m * nc * (Y * Y) := by
  calc
    m * n * q * Y = m * (n * q) * Y := by ring
    _ = m * (nc * Y) * Y := by rw [hmem]
    _ = m * nc * (Y * Y) := by ring

/-- Saturated Y² = 1 gives ρ_∞ = m·nc. -/
theorem thm_saturated_density
    (m nc Y2 : ℝ) (hY : Y2 = 1) :
    m * nc * Y2 = m * nc := by
  rw [hY]
  ring

/-- Pole amplitude matching ρ_∞·K = m·Γ. -/
theorem thm_pole_amplitude_matching
    (m nc K Gamma rhoInf : ℝ)
    (hcrit : nc * K = Gamma)
    (hrho : rhoInf = m * nc) :
    rhoInf * K = m * Gamma := by
  rw [hrho]
  calc
    (m * nc) * K = m * (nc * K) := by ring
    _ = m * Gamma := by rw [hcrit]

/-- Residue ratio unity when N₁ = m·Γ. -/
theorem thm_residue_ratio_one
    {N1 m Gamma : ℝ}
    (hm : m ≠ 0) (hG : Gamma ≠ 0)
    (hN : N1 = m * Gamma) :
    N1 / (m * Gamma) = 1 := by
  rw [hN]
  field_simp

/-- Near-critical identity: m nc · 3(G-1)/G³ = 3m(nc - nc/G)/G². -/
theorem thm_near_critical_slope_identity
    (m nc G : ℝ) (hG : G ≠ 0) :
    m * nc * (3 * (G - 1) / G ^ 3) =
      (3 * m * (nc - nc / G)) / G ^ 2 := by
  field_simp [hG]

/-- At G = 1 the local coefficient is B = 3. -/
theorem thm_local_B_limit :
    (fun G : ℝ => 3 / G ^ 2) 1 = 3 := by
  norm_num


/-- Positive vacuum asymptotic response density. -/
theorem thm_positive_vacuum_density
    {m nc : ℝ} (hm : 0 < m) (hn : 0 < nc) :
    0 < m * nc :=
  mul_pos hm hn

/-- Positive effective cosmological-constant numerator. -/
theorem thm_positive_lambda_numerator
    {grav m nc : ℝ} (hg : 0 < grav) (hm : 0 < m) (hn : 0 < nc) :
    0 < grav * (m * nc) :=
  mul_pos hg (mul_pos hm hn)

/-- Algebraic pressure point p/c² = n ρ' − ρ. -/
def pressureMassPoint (rho nRhoPrime : ℝ) : ℝ := nRhoPrime - rho

theorem thm_vacuum_pressure_limit_point
    {rhoInf : ℝ} : pressureMassPoint rhoInf 0 = -rhoInf := by
  unfold pressureMassPoint
  ring

/-- Redshift master relation ρ_∞ = m n₀ (1+z)³ as an algebraic identity in z. -/
theorem thm_redshift_master_relation
    (m n0 z1 : ℝ) :
    m * (n0 * (z1 * z1 * z1)) = m * n0 * (z1 * z1 * z1) := by
  ring

end

end Paper6
