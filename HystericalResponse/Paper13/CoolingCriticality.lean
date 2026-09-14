/-
TeX: `13_ew_cooling_baryogenesis/paper_13_ew_cooling_baryogenesis.tex`
Section “Forced cooling criticality” — thm:cooling, cor:restabilize witness.
-/

import Mathlib
import HystericalResponse.Paper13.InheritedResidual

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Paper13

noncomputable section

/-- TeX: eq:Td — unique positive critical temperature. -/
def Tdiamond (αX αY g : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (g ^ 2 / (αX * αY)))

theorem Tdiamond_nonneg (αX αY g : ℝ) :
    0 ≤ Tdiamond αX αY g := by
  unfold Tdiamond
  exact Real.sqrt_nonneg _

/-- Fourth-power identity for T_♦ under positive stiffnesses. -/
theorem Tdiamond_pow4 {αX αY g : ℝ}
    (hαX : 0 < αX) (hαY : 0 < αY) :
    Tdiamond αX αY g ^ 4 = g ^ 2 / (αX * αY) := by
  unfold Tdiamond
  have hden : 0 < αX * αY := mul_pos hαX hαY
  have harg : 0 ≤ g ^ 2 / (αX * αY) :=
    div_nonneg (sq_nonneg g) hden.le
  have hs : 0 ≤ Real.sqrt (g ^ 2 / (αX * αY)) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (g ^ 2 / (αX * αY))) ^ 2 = g ^ 2 / (αX * αY) :=
    Real.sq_sqrt harg
  calc
    (Real.sqrt (Real.sqrt (g ^ 2 / (αX * αY)))) ^ 4
        = ((Real.sqrt (Real.sqrt (g ^ 2 / (αX * αY)))) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt (g ^ 2 / (αX * αY))) ^ 2 := by rw [Real.sq_sqrt hs]
    _ = g ^ 2 / (αX * αY) := hsq

theorem Delta_Tdiamond {αX αY g T : ℝ}
    (hαX : 0 < αX) (hαY : 0 < αY) :
    Delta αX αY g T =
      αX * αY * (T ^ 4 - Tdiamond αX αY g ^ 4) := by
  rw [Delta_eq, Tdiamond_pow4 hαX hαY]
  have hden : αX * αY ≠ 0 := (mul_pos hαX hαY).ne'
  field_simp [hden]

/-- TeX: thm:cooling (i) — critical at T_♦. -/
theorem thm_cooling_critical {αX αY g : ℝ}
    (hαX : 0 < αX) (hαY : 0 < αY) :
    Delta αX αY g (Tdiamond αX αY g) = 0 := by
  rw [Delta_Tdiamond hαX hαY]
  ring

/-- TeX: thm:cooling (ii) — subcritical for T > T_♦ (via T⁴ comparison). -/
theorem thm_cooling_subcritical_pow {αX αY g T : ℝ}
    (hαX : 0 < αX) (hαY : 0 < αY)
    (hp : Tdiamond αX αY g ^ 4 < T ^ 4) :
    0 < Delta αX αY g T := by
  rw [Delta_Tdiamond hαX hαY]
  exact mul_pos (mul_pos hαX hαY) (sub_pos.mpr hp)

/-- TeX: thm:cooling (iii) — supercritical for 0 < T < T_♦ (via T⁴ comparison). -/
theorem thm_cooling_supercritical_pow {αX αY g T : ℝ}
    (hαX : 0 < αX) (hαY : 0 < αY)
    (hp : T ^ 4 < Tdiamond αX αY g ^ 4) :
    Delta αX αY g T < 0 := by
  rw [Delta_Tdiamond hαX hαY]
  exact mul_neg_of_pos_of_neg (mul_pos hαX hαY) (sub_neg.mpr hp)

/-- Uniqueness of the positive root of Δ(T)=0. -/
theorem thm_cooling_unique {αX αY g T : ℝ}
    (hαX : 0 < αX) (hαY : 0 < αY)
    (hT : 0 ≤ T) (hΔ : Delta αX αY g T = 0) :
    T = Tdiamond αX αY g := by
  have hfac : αX * αY * (T ^ 4 - Tdiamond αX αY g ^ 4) = 0 := by
    rw [← Delta_Tdiamond hαX hαY, hΔ]
  have hdiff : T ^ 4 - Tdiamond αX αY g ^ 4 = 0 := by
    have hα : αX * αY ≠ 0 := (mul_pos hαX hαY).ne'
    exact (mul_eq_zero.mp hfac).resolve_left hα
  have hpow : T ^ 4 = Tdiamond αX αY g ^ 4 := sub_eq_zero.mp hdiff
  have hTd : 0 ≤ Tdiamond αX αY g := Tdiamond_nonneg αX αY g
  exact (pow_left_inj₀ hT hTd (by norm_num : (4:ℕ) ≠ 0)).1 hpow

/-- Packaged cooling theorem matching TeX thm:cooling. -/
theorem thm_cooling {αX αY g : ℝ}
    (hαX : 0 < αX) (hαY : 0 < αY) (hg : g ≠ 0) :
    Delta αX αY g (Tdiamond αX αY g) = 0 ∧
      (∀ T, Tdiamond αX αY g ^ 4 < T ^ 4 → 0 < Delta αX αY g T) ∧
      (∀ T, T ^ 4 < Tdiamond αX αY g ^ 4 → Delta αX αY g T < 0) ∧
      0 < Tdiamond αX αY g := by
  refine ⟨thm_cooling_critical hαX hαY,
    fun T hp => thm_cooling_subcritical_pow hαX hαY hp,
    fun T hp => thm_cooling_supercritical_pow hαX hαY hp, ?_⟩
  have hden : 0 < αX * αY := mul_pos hαX hαY
  have harg : 0 < g ^ 2 / (αX * αY) :=
    div_pos (sq_pos_of_ne_zero hg) hden
  unfold Tdiamond
  exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr harg)

/-- TeX: cor:restabilize — β_Y = 0 specialization recovers criticality at T_♦. -/
theorem cor_restabilize_beta0 {αX αY g : ℝ}
    (hαX : 0 < αX) (hαY : 0 < αY) :
    Delta αX αY g (Tdiamond αX αY g) = 0 :=
  thm_cooling_critical hαX hαY

end

end Paper13
