/-
TeX: `13_ew_cooling_baryogenesis/paper_13_ew_cooling_baryogenesis.tex`
Section / corollary cor:restabilize — full Higgs-band restabilization witness.
Ported from the retired electroweak baryon companion (Paper 7) and completed.
-/

import Mathlib
import HystericalResponse.Paper13.InheritedResidual

set_option autoImplicit false

namespace Paper13

noncomputable section

/-- Mean-field Higgs factor: 1 − T²/Tc² below Tc, else 0. -/
def higgsFactor (Tc T : ℝ) : ℝ :=
  if Tc ≤ T then 0 else 1 - T ^ 2 / Tc ^ 2

def kY_full (αY βY mW0 Tc T : ℝ) : ℝ :=
  αY * T ^ 2 + βY * mW0 ^ 2 * higgsFactor Tc T

/-- Full broken-phase Hessian determinant. -/
def Delta_full (αX αY βY mW0 Tc g T : ℝ) : ℝ :=
  kX αX T * kY_full αY βY mW0 Tc T - g ^ 2

/-- Quadratic in u = T² for broken-phase Δ (T < Tc). -/
def deltaQuad (αX αY βY mW0 Tc g u : ℝ) : ℝ :=
  let c1 := αX * αY
  let c2 := αX * βY * mW0 ^ 2
  (c1 - c2 / Tc ^ 2) * u ^ 2 + c2 * u - g ^ 2

theorem Delta_full_eq_quad {αX αY βY mW0 Tc g T : ℝ}
    (hTc : Tc ≠ 0) (hlt : T < Tc) :
    Delta_full αX αY βY mW0 Tc g T =
      deltaQuad αX αY βY mW0 Tc g (T ^ 2) := by
  have hif : ¬ (Tc ≤ T) := not_le.mpr hlt
  unfold Delta_full kX kY_full higgsFactor deltaQuad
  simp [hif]
  field_simp [hTc]
  ring

/-! ### Explicit two-root witness

Coefficients: αX=αY=1, βY=12, mW0=1, Tc=2, g²=17.
Then for u=T² < 4,
  Δ = -2 u² + 12 u - 17
with roots u = 3 ± √(1/2), both in (0,4).
-/

def restab_αX : ℝ := 1
def restab_αY : ℝ := 1
def restab_βY : ℝ := 12
def restab_mW0 : ℝ := 1
def restab_Tc : ℝ := 2
def restab_g : ℝ := Real.sqrt 17
def restab_s : ℝ := Real.sqrt (1 / 2)
def restab_uSmall : ℝ := 3 - restab_s
def restab_uLarge : ℝ := 3 + restab_s

theorem restab_s_sq : restab_s ^ 2 = 1 / 2 := by
  unfold restab_s
  exact Real.sq_sqrt (by norm_num)

theorem restab_g_sq : restab_g ^ 2 = 17 := by
  unfold restab_g
  exact Real.sq_sqrt (by norm_num)

theorem restab_roots_sum_prod :
    restab_uSmall + restab_uLarge = 6 ∧
    restab_uSmall * restab_uLarge = 17 / 2 := by
  unfold restab_uSmall restab_uLarge
  constructor
  · ring
  · have hs := restab_s_sq
    nlinarith

theorem deltaQuad_restab (u : ℝ) :
    deltaQuad restab_αX restab_αY restab_βY restab_mW0 restab_Tc restab_g u =
      -2 * u ^ 2 + 12 * u - 17 := by
  unfold deltaQuad restab_αX restab_αY restab_βY restab_mW0 restab_Tc
  rw [restab_g_sq]
  norm_num

theorem cor_restabilize_quad_at_roots :
    deltaQuad restab_αX restab_αY restab_βY restab_mW0 restab_Tc restab_g restab_uSmall = 0 ∧
    deltaQuad restab_αX restab_αY restab_βY restab_mW0 restab_Tc restab_g restab_uLarge = 0 := by
  have hs := restab_s_sq
  constructor
  · rw [deltaQuad_restab]
    unfold restab_uSmall
    have : (3 - restab_s) ^ 2 - 6 * (3 - restab_s) + 17 / 2 = 0 := by
      nlinarith [hs]
    nlinarith
  · rw [deltaQuad_restab]
    unfold restab_uLarge
    have : (3 + restab_s) ^ 2 - 6 * (3 + restab_s) + 17 / 2 = 0 := by
      nlinarith [hs]
    nlinarith

theorem cor_restabilize_mid_pos :
    0 < deltaQuad restab_αX restab_αY restab_βY restab_mW0 restab_Tc restab_g 3 := by
  rw [deltaQuad_restab]
  norm_num

theorem restab_s_lt_one : restab_s < 1 := by
  unfold restab_s
  rw [← Real.sqrt_one]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem restab_u_order :
    0 < restab_uSmall ∧ restab_uSmall < restab_uLarge ∧ restab_uLarge < restab_Tc ^ 2 := by
  unfold restab_uSmall restab_uLarge restab_Tc
  have hs : 0 < restab_s := by
    unfold restab_s
    exact Real.sqrt_pos.2 (by norm_num)
  have hsb := restab_s_lt_one
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- TeX: cor:restabilize — parameters with 0 < T_re < T_d < T_c and two zeros of Δ_full. -/
theorem cor_restabilize :
    ∃ (αX αY βY mW0 Tc g Tre Td : ℝ),
      0 < αX ∧ 0 < αY ∧ 0 < βY ∧ 0 < mW0 ∧ 0 < g ∧
      0 < Tre ∧ Tre < Td ∧ Td < Tc ∧
      Delta_full αX αY βY mW0 Tc g Tre = 0 ∧
      Delta_full αX αY βY mW0 Tc g Td = 0 ∧
      0 < Delta_full αX αY βY mW0 Tc g (Real.sqrt 3) := by
  let Tre := Real.sqrt restab_uSmall
  let Td := Real.sqrt restab_uLarge
  have hord := restab_u_order
  have hs0 : 0 ≤ restab_uSmall := le_of_lt hord.1
  have hl0 : 0 ≤ restab_uLarge := le_of_lt (lt_trans hord.1 hord.2.1)
  have hTre_pos : 0 < Tre := Real.sqrt_pos.2 hord.1
  have hTd_pos : 0 < Td := Real.sqrt_pos.2 (lt_trans hord.1 hord.2.1)
  have hTre_Td : Tre < Td := Real.sqrt_lt_sqrt hs0 hord.2.1
  have hTd_Tc : Td < restab_Tc := by
    have hsq : Td ^ 2 < restab_Tc ^ 2 := by
      change Real.sqrt restab_uLarge ^ 2 < restab_Tc ^ 2
      rw [Real.sq_sqrt hl0]
      exact hord.2.2
    have hTc0 : 0 ≤ restab_Tc := by norm_num [restab_Tc]
    have habs : |Td| < |restab_Tc| :=
      (sq_lt_sq).1 (by
        simpa [abs_of_nonneg (le_of_lt hTd_pos), abs_of_nonneg hTc0] using hsq)
    simpa [abs_of_nonneg (le_of_lt hTd_pos), abs_of_nonneg hTc0] using habs
  have hroots := cor_restabilize_quad_at_roots
  have hTre_lt_Tc : Tre < restab_Tc := lt_trans hTre_Td hTd_Tc
  have hTd_lt_Tc : Td < restab_Tc := hTd_Tc
  have hTc_ne : restab_Tc ≠ 0 := by norm_num [restab_Tc]
  have hΔTre : Delta_full restab_αX restab_αY restab_βY restab_mW0 restab_Tc restab_g Tre = 0 := by
    have := Delta_full_eq_quad (αX := restab_αX) (αY := restab_αY) (βY := restab_βY)
      (mW0 := restab_mW0) (Tc := restab_Tc) (g := restab_g) (T := Tre) hTc_ne hTre_lt_Tc
    rw [this]
    change deltaQuad _ _ _ _ _ _ (Real.sqrt restab_uSmall ^ 2) = 0
    rw [Real.sq_sqrt hs0]
    exact hroots.1
  have hΔTd : Delta_full restab_αX restab_αY restab_βY restab_mW0 restab_Tc restab_g Td = 0 := by
    have := Delta_full_eq_quad (αX := restab_αX) (αY := restab_αY) (βY := restab_βY)
      (mW0 := restab_mW0) (Tc := restab_Tc) (g := restab_g) (T := Td) hTc_ne hTd_lt_Tc
    rw [this]
    change deltaQuad _ _ _ _ _ _ (Real.sqrt restab_uLarge ^ 2) = 0
    rw [Real.sq_sqrt hl0]
    exact hroots.2
  have hmidT : Real.sqrt 3 < restab_Tc := by
    have : (Real.sqrt 3) ^ 2 < restab_Tc ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num [restab_Tc]
    have h3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    have hTc0 : 0 ≤ restab_Tc := by norm_num [restab_Tc]
    have habs : |Real.sqrt 3| < |restab_Tc| :=
      (sq_lt_sq).1 (by simpa [abs_of_nonneg h3, abs_of_nonneg hTc0] using this)
    simpa [abs_of_nonneg h3, abs_of_nonneg hTc0] using habs
  have hΔmid :
      0 < Delta_full restab_αX restab_αY restab_βY restab_mW0 restab_Tc restab_g (Real.sqrt 3) := by
    have := Delta_full_eq_quad (αX := restab_αX) (αY := restab_αY) (βY := restab_βY)
      (mW0 := restab_mW0) (Tc := restab_Tc) (g := restab_g) (T := Real.sqrt 3) hTc_ne hmidT
    rw [this, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    exact cor_restabilize_mid_pos
  refine ⟨restab_αX, restab_αY, restab_βY, restab_mW0, restab_Tc, restab_g, Tre, Td, ?_⟩
  refine ⟨by norm_num [restab_αX], by norm_num [restab_αY], by norm_num [restab_βY],
    by norm_num [restab_mW0], Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 17),
    hTre_pos, hTre_Td, hTd_Tc, hΔTre, hΔTd, hΔmid⟩

end

end Paper13
