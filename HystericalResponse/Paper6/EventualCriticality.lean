import Mathlib

/-!
TeX: `6_cosmological_constant/paper_6_late_universe.tex`,
Section “Dilution-driven criticality”, Theorem “Eventual dilution criticality”.
-/

set_option autoImplicit false

namespace Paper6

noncomputable section

/-- Linear-gap critical density nc = Γ/K. -/
theorem thm_eventual_linear_gap
    {Gamma K nc : ℝ} (hK : K ≠ 0) (h : nc * K = Gamma) :
    nc = Gamma / K :=
  (eq_div_iff hK).2 (by simpa [mul_comm] using h)

/-- FLRW cubic gain G(a) = (a/ac)^3. -/
def gainOfScale (a ac : ℝ) : ℝ := (a / ac) ^ 3

theorem thm_gainOfScale_at_critical {ac : ℝ} (hac : ac ≠ 0) :
    gainOfScale ac ac = 1 := by
  unfold gainOfScale
  field_simp [hac]

/-- Supercriticality for positive scale factors with a > ac > 0. -/
theorem thm_gainOfScale_supercritical
    {a ac : ℝ} (hac0 : 0 < ac) (h : ac < a) :
    1 < gainOfScale a ac := by
  unfold gainOfScale
  have hratio : 1 < a / ac := (one_lt_div hac0).2 h
  have hpos : 0 < a / ac := lt_trans zero_lt_one hratio
  have hsq : 1 < (a / ac) ^ 2 := by
    nlinarith [sq_nonneg (a / ac - 1), mul_pos hpos (sub_pos.mpr hratio)]
  nlinarith [mul_pos hpos (sub_pos.mpr hratio), mul_pos (sub_pos.mpr hsq) hpos]

theorem thm_gainOfScale_subcritical
    {a ac : ℝ} (ha0 : 0 < a) (h : a < ac) :
    gainOfScale a ac < 1 := by
  unfold gainOfScale
  have hac0 : 0 < ac := lt_trans ha0 h
  have hratio : 0 < a / ac := div_pos ha0 hac0
  have hlt : a / ac < 1 := (div_lt_one hac0).2 h
  have hsq : (a / ac) ^ 2 < 1 := by
    nlinarith [sq_nonneg (1 - a / ac), mul_pos hratio (sub_pos.mpr hlt)]
  nlinarith [mul_pos hratio (sub_pos.mpr hlt)]

/-- Present equation of state under cubic dilution. -/
def wH0 (zc : ℝ) : ℝ := -1 - 1 / ((1 + zc) ^ 3 - 1)

/-- TeX: thm:background-diagnostics. -/
theorem thm_wH0_lt_neg_one {zc : ℝ} (hzc : 0 < zc) :
    wH0 zc < -1 := by
  unfold wH0
  have h1 : 1 < 1 + zc := by linarith
  have hpow : 1 < (1 + zc) ^ 3 := by
    have hpos : 0 < 1 + zc := by linarith
    have hsq : 1 < (1 + zc) ^ 2 := by
      nlinarith [sq_nonneg ((1 + zc) - 1), mul_pos hpos (sub_pos.mpr h1)]
    nlinarith [mul_pos hpos (sub_pos.mpr h1)]
  have hpos : 0 < (1 + zc) ^ 3 - 1 := sub_pos.mpr hpow
  have : 0 < 1 / ((1 + zc) ^ 3 - 1) := one_div_pos.mpr hpos
  linarith

/-- Benchmark: zc = 2 gives w_H0 = -27/26. -/
example : wH0 (2 : ℝ) = -(27 : ℝ) / 26 := by
  norm_num [wH0]

end

end Paper6
