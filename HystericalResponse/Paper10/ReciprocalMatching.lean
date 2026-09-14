import Mathlib

/-!
TeX: `10_cyclic_cosmology/paper_10_hysterical_ccc.tex`,
Section “Reciprocal conformal matching”.

Faithful algebraic ports of cold/hot density scaling, reciprocal momenta,
exact de~Sitter reciprocity leading term, and radiation-era identity
`a² = 2 C t`.

Reduced abstraction for Thm.~radiation: Lean certifies the exact leading-term
and exact linear ansatz `a = C η`; the little-o remainder in TeX~(eq:dS) is
not re-proved here (disclosed in the TeX status table).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Paper10

noncomputable section

/-- Physical densities from a common conformal density. -/
def rhoOut (rhoHat aMinus : ℝ) : ℝ := rhoHat / aMinus ^ 4
def rhoIn (rhoHat aPlus : ℝ) : ℝ := rhoHat / aPlus ^ 4

/-- TeX: prop:mom. -/
theorem prop_mom (k aMinus aPlus : ℝ)
    (_haM : aMinus ≠ 0) (hrec : aPlus * aMinus = 1) :
    k / aPlus = k * aMinus := by
  have haP : aPlus ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrec
    exact (one_ne_zero : (1 : ℝ) ≠ 0) hrec.symm
  have hinv : aPlus⁻¹ = aMinus :=
    inv_eq_of_mul_eq_one_left (by simpa [mul_comm] using hrec)
  calc
    k / aPlus = k * aPlus⁻¹ := div_eq_mul_inv k aPlus
    _ = k * aMinus := by rw [hinv]

/-- TeX: thm:hot-cold ratio with general reciprocity constant `C₀`. -/
theorem thm_hot_cold_C0 (rhoHat OmMinus OmPlus C0 : ℝ)
    (hr : rhoHat ≠ 0) (hOm : OmMinus ≠ 0) (hC0 : C0 ≠ 0)
    (hrec : OmPlus * OmMinus = C0) :
    (rhoHat / OmPlus ^ 4) / (rhoHat / OmMinus ^ 4) = OmMinus ^ 8 / C0 ^ 4 := by
  have hOmP : OmPlus ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrec
    exact hC0 hrec.symm
  field_simp [hr, hOm, hOmP, hC0]
  calc
    C0 ^ 4 = (OmPlus * OmMinus) ^ 4 := by rw [hrec]
    _ = OmPlus ^ 4 * OmMinus ^ 4 := by ring

/-- TeX: thm:hot-cold — unit reciprocity `a₊ a₋ = 1` gives `ρ₊/ρ₋ = a₋⁸`. -/
theorem thm_hot_cold (rhoHat aMinus aPlus : ℝ)
    (hr : rhoHat ≠ 0) (haM : aMinus ≠ 0)
    (hrec : aPlus * aMinus = 1) :
    rhoIn rhoHat aPlus / rhoOut rhoHat aMinus = aMinus ^ 8 := by
  unfold rhoIn rhoOut
  have h := thm_hot_cold_C0 rhoHat aMinus aPlus 1 hr haM (by norm_num) (by simpa using hrec)
  simpa using h

theorem thm_hot_cold_ratio (rhoHat aMinus aPlus : ℝ)
    (hr : rhoHat ≠ 0) (haM : aMinus ≠ 0)
    (hrec : aPlus * aMinus = 1) :
    (rhoHat / aPlus ^ 4) / (rhoHat / aMinus ^ 4) = aMinus ^ 8 := by
  simpa [rhoIn, rhoOut] using thm_hot_cold rhoHat aMinus aPlus hr haM hrec

/-- Cold outgoing / hot incoming for `a₋ > 1` under unit reciprocity. -/
theorem thm_hot_cold_limits {rhoHat aMinus aPlus : ℝ}
    (hr : 0 < rhoHat) (haM : 1 < aMinus)
    (hrec : aPlus * aMinus = 1) :
    rhoOut rhoHat aMinus < rhoHat ∧ rhoHat < rhoIn rhoHat aPlus := by
  have haM0 : 0 < aMinus := lt_trans zero_lt_one haM
  have haP_eq : aPlus = aMinus⁻¹ :=
    inv_eq_iff_eq_inv.mp
      (inv_eq_of_mul_eq_one_left (by simpa [mul_comm] using hrec))
  have haP0 : 0 < aPlus := by
    rw [haP_eq]
    exact inv_pos.mpr haM0
  have hpow : 1 < aMinus ^ 4 := by
    have h2 : 1 < aMinus ^ 2 := by nlinarith [mul_pos haM0 haM0]
    nlinarith
  constructor
  · unfold rhoOut
    exact (div_lt_iff₀ (pow_pos haM0 4)).2 (by nlinarith)
  · unfold rhoIn
    have haP_lt : aPlus < 1 := by
      rw [haP_eq]
      exact inv_lt_one_of_one_lt₀ haM
    have hpowP : aPlus ^ 4 < 1 := by
      have h2 : aPlus ^ 2 < 1 := by nlinarith [mul_pos haP0 haP0]
      nlinarith
    exact (lt_div_iff₀ (pow_pos haP0 4)).2 (by nlinarith)

/-- TeX: thm:radiation — exact linear ansatz. -/
theorem thm_radiation (C eta t a : ℝ)
    (ha : a = C * eta) (ht : t = C * eta ^ 2 / 2) :
    a ^ 2 = 2 * C * t := by
  rw [ha, ht]
  ring

/-- Exact leading-term reciprocity: if `a₋ = 1/(H η)` for `η > 0`, then `a₊ = H η`. -/
theorem thm_radiation_reciprocal_leading
    (H eta : ℝ) (hH : 0 < H) (heta : 0 < eta) :
    1 / (1 / (H * eta)) = H * eta := by
  field_simp [ne_of_gt hH, ne_of_gt heta]

/-- Radiation-era exponent: `a = C η`, `t = C η²/2`, `C > 0`, `η > 0` ⇒ `a = √(2 C t)`. -/
theorem thm_radiation_sqrt
    (C eta t a : ℝ) (hC : 0 < C) (heta : 0 < eta)
    (ha : a = C * eta) (ht : t = C * eta ^ 2 / 2) :
    a = Real.sqrt (2 * C * t) := by
  have habs : a ^ 2 = 2 * C * t := thm_radiation C eta t a ha ht
  have ha_pos : 0 < a := by
    rw [ha]
    exact mul_pos hC heta
  have ht_pos : 0 < 2 * C * t := by
    have : 0 < t := by
      rw [ht]
      positivity
    positivity
  have habs' : 2 * C * t = a * a := by
    simpa [pow_two] using habs.symm
  exact ((Real.sqrt_eq_iff_mul_self_eq (le_of_lt ht_pos) (le_of_lt ha_pos)).2 habs').symm

/-- Packaged TeX: thm:radiation leading-term + radiation identity. -/
theorem thm_radiation_full
    (H eta t a : ℝ) (hH : 0 < H) (heta : 0 < eta)
    (ha : a = H * eta) (ht : t = H * eta ^ 2 / 2) :
    1 / (1 / (H * eta)) = H * eta ∧
      a ^ 2 = 2 * H * t ∧
      a = Real.sqrt (2 * H * t) :=
  ⟨thm_radiation_reciprocal_leading H eta hH heta,
    thm_radiation H eta t a ha ht,
    thm_radiation_sqrt H eta t a hH heta ha ht⟩

end

end Paper10
