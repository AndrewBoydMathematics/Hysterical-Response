import Mathlib

/-!
TeX: `6_cosmological_constant/paper_6_late_universe.tex`,
Section “Finite-amplitude crossing”.

Constant-rate crossing, dilution exponent Φ, conditional w = −p/3,
homogeneous charge conservation, and frozen-coefficient EM threshold algebra.
Compiler certification: `lake build HystericalResponse.Paper6_LateUniverse_Spec`.
-/

set_option autoImplicit false

namespace Paper6

noncomputable section

/-- Crossing time for X(t) = Xi exp(lam t). -/
def crossingTime (Xi Xstar lam : ℝ) : ℝ :=
  Real.log (Xstar / Xi) / lam

/-- TeX: thm:crossing — constant-rate exponential reaches the target. -/
theorem thm_crossing_constant_rate
    {Xi Xstar lam : ℝ}
    (hXi : 0 < Xi) (hXstar : 0 < Xstar) (hlam : lam ≠ 0) :
    Xi * Real.exp (lam * crossingTime Xi Xstar lam) = Xstar := by
  unfold crossingTime
  have hratio : 0 < Xstar / Xi := div_pos hXstar hXi
  have hmul : lam * (Real.log (Xstar / Xi) / lam) = Real.log (Xstar / Xi) := by
    field_simp [hlam]
  rw [hmul, Real.exp_log hratio]
  field_simp [ne_of_gt hXi]

/-- TeX: logarithmic crossing time is positive under standard hypotheses. -/
theorem thm_crossing_time_pos
    {Xi Xstar lam : ℝ}
    (hXi : 0 < Xi) (hgt : Xi < Xstar) (hlam : 0 < lam) :
    0 < crossingTime Xi Xstar lam := by
  unfold crossingTime
  have hratio : 1 < Xstar / Xi := (lt_div_iff₀ hXi).2 (by simpa using hgt)
  have hlog : 0 < Real.log (Xstar / Xi) := Real.log_pos hratio
  exact div_pos hlog hlam

/-- Dimensionless accumulated exponent after criticality, with x = a/a_c. -/
def Phi (x : ℝ) : ℝ := (x ^ 3 - 1) / 3 - Real.log x

@[simp] theorem Phi_one : Phi 1 = 0 := by
  unfold Phi
  simp

/-- Derivative of Phi on positive x. -/
theorem hasDerivAt_Phi {x : ℝ} (hx : 0 < x) :
    HasDerivAt Phi (x ^ 2 - x⁻¹) x := by
  unfold Phi
  convert (((hasDerivAt_pow 3 x).sub_const 1).div_const 3).sub
      (Real.hasDerivAt_log hx.ne') using 1
  ring

/-- The derivative is strictly positive after criticality x > 1. -/
theorem Phi_deriv_pos {x : ℝ} (hx : 1 < x) :
    0 < x ^ 2 - x⁻¹ := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hx3 : 1 < x ^ 3 := by
    nlinarith [mul_pos hx0 hx0, mul_pos (mul_pos hx0 hx0) hx0]
  have hquot : 0 < (x ^ 3 - 1) / x := div_pos (sub_pos.mpr hx3) hx0
  have heq : x ^ 2 - x⁻¹ = (x ^ 3 - 1) / x := by
    field_simp [hx0.ne']
  rwa [heq]

/-- TeX: prop:Phi — Phi is strictly positive for x > 1. -/
theorem Phi_pos {x : ℝ} (hx : 1 < x) : 0 < Phi x := by
  have hcont : ContinuousOn Phi (Set.Icc (1 : ℝ) x) := by
    unfold Phi
    apply ContinuousOn.sub
    · exact ((continuous_pow 3).continuousOn.sub continuousOn_const).div_const _
    · exact Real.continuousOn_log.comp continuousOn_id fun y hy =>
        (lt_of_lt_of_le zero_lt_one hy.1).ne'
  have hderiv : ∀ y ∈ interior (Set.Icc (1 : ℝ) x), 0 < deriv Phi y := by
    intro y hy
    have hyIoo : y ∈ Set.Ioo (1 : ℝ) x := by
      have hEq : interior (Set.Icc (1 : ℝ) x) = Set.Ioo (1 : ℝ) x := interior_Icc
      rwa [hEq] at hy
    have hy0 : 0 < y := lt_trans zero_lt_one hyIoo.1
    rw [(hasDerivAt_Phi hy0).deriv]
    exact Phi_deriv_pos hyIoo.1
  have hmono : StrictMonoOn Phi (Set.Icc (1 : ℝ) x) :=
    strictMonoOn_of_deriv_pos (convex_Icc (1 : ℝ) x) hcont hderiv
  have hlt := hmono ⟨le_rfl, le_of_lt hx⟩ ⟨le_of_lt hx, le_rfl⟩ hx
  simpa [Phi_one] using hlt

/-- Present-epoch accumulated exponent is positive for 0 < a_c < 1. -/
theorem present_exponent_pos {ac : ℝ} (hac0 : 0 < ac) (hac1 : ac < 1) :
    0 < Phi (1 / ac) := by
  apply Phi_pos
  exact (lt_div_iff₀ hac0).2 (by simpa using hac1)

/-- If rho_H scales as a^(p-3), matching it to a^(-3(1+w)) gives w=-p/3. -/
def effectiveW (p : ℝ) : ℝ := -p / 3

@[simp] theorem cubic_susceptibility_gives_w_minus_one :
    effectiveW 3 = -1 := by
  unfold effectiveW
  norm_num

theorem exponent_match (p : ℝ) :
    p - 3 = -3 * (1 + effectiveW p) := by
  unfold effectiveW
  ring

/-- TeX: thm:no-charge — conservation preserves a zero homogeneous charge. -/
theorem thm_conserved_zero_charge
    {Qinitial Qfinal : ℝ}
    (hcons : Qfinal = Qinitial)
    (hzero : Qinitial = 0) :
    Qfinal = 0 := by
  calc
    Qfinal = Qinitial := hcons
    _ = 0 := hzero

/-- Frozen-coefficient EM characteristic polynomial. -/
def emCharPoly (gamma H omega2 beta sigma lam : ℝ) : ℝ :=
  (lam + gamma) * (lam ^ 2 + 2 * H * lam + omega2) - beta * sigma * omega2

/-- TeX: supercritical EM feedback makes P(0) negative. -/
theorem thm_em_charPoly_zero_neg
    {gamma H omega2 beta sigma : ℝ}
    (homega : 0 < omega2)
    (hfeedback : gamma < beta * sigma) :
    emCharPoly gamma H omega2 beta sigma 0 < 0 := by
  unfold emCharPoly
  have := mul_pos homega (sub_pos.mpr hfeedback)
  nlinarith

end

end Paper6
