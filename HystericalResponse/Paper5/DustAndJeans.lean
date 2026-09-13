import Mathlib
import HystericalResponse.Paper5.CosmologicalJacobian

/-!
TeX: `5_early_galactic_formation/paper_5_early_universe.tex`,
Sections “Enhancement over ordinary dust” and “Pressure extension”.

Ports Proposition [Strict enhancement of the growing rate] and
Proposition [Sufficient response-induced Jeans crossing].
-/

set_option autoImplicit false

namespace Paper5

noncomputable section

/-- Ordinary pressureless dust root `λ_b = -H + √(H²+A)`. -/
def dustRoot (H A : ℝ) : ℝ :=
  -H + Real.sqrt (H ^ 2 + A)

theorem dustRoot_nonneg {H A : ℝ} (hH : 0 ≤ H) (hA : 0 < A) :
    0 < dustRoot H A := by
  unfold dustRoot
  have : H ^ 2 < H ^ 2 + A := by nlinarith
  have hgt : Real.sqrt (H ^ 2) < Real.sqrt (H ^ 2 + A) :=
    Real.sqrt_lt_sqrt (sq_nonneg H) this
  have : H < Real.sqrt (H ^ 2 + A) := by
    simpa [Real.sqrt_sq hH] using hgt
  linarith

theorem dustRoot_charEq {H A : ℝ} (hA : 0 ≤ A) :
    dustRoot H A ^ 2 + 2 * H * dustRoot H A - A = 0 := by
  unfold dustRoot
  set s := Real.sqrt (H ^ 2 + A)
  have hs2 : s ^ 2 = H ^ 2 + A := Real.sq_sqrt (by nlinarith [sq_nonneg H])
  nlinarith [hs2]

theorem charPoly_at_dustRoot
    {H A gamma C : ℝ} (hA : 0 ≤ A) :
    charPoly H A gamma C (dustRoot H A) = -A * C := by
  unfold charPoly
  have h := dustRoot_charEq (H := H) (A := A) hA
  rw [h]
  ring

theorem charPoly_pos_of_ge_bracket
    {H A gamma C M : ℝ}
    (hH : 0 ≤ H) (hA : 0 < A) (hgamma : 0 ≤ gamma) (hC : 0 < C)
    (hM : instabilityBracket A C ≤ M) :
    0 < charPoly H A gamma C M := by
  have hMpos : 0 < M :=
    lt_of_lt_of_le (instabilityBracket_pos hA hC) hM
  have hMA : 1 + A ≤ M := by
    have : 1 + A ≤ instabilityBracket A C := by
      unfold instabilityBracket; nlinarith [hC]
    exact le_trans this hM
  have hM2Age1 : 1 ≤ M ^ 2 - A := by
    have hsq : (1 + A) ^ 2 ≤ M ^ 2 :=
      sq_le_sq' (by nlinarith [hMpos]) hMA
    nlinarith
  have hlower :
      M * (M ^ 2 - A) ≤ (M + gamma) * (M ^ 2 + 2 * H * M - A) := by
    have h1 : M ≤ M + gamma := by nlinarith [hgamma]
    have h2 : M ^ 2 - A ≤ M ^ 2 + 2 * H * M - A := by nlinarith [hH, hMpos]
    exact mul_le_mul h1 h2 (by nlinarith [hM2Age1]) (by nlinarith [hMpos])
  have hbig : A * C < M * (M ^ 2 - A) := by
    have hAC : A * C < instabilityBracket A C := by
      unfold instabilityBracket; nlinarith [hA]
    have hLge : A * C < M := lt_of_lt_of_le hAC hM
    have : M ≤ M * (M ^ 2 - A) := by nlinarith [hMpos, hM2Age1]
    exact lt_of_lt_of_le hLge this
  unfold charPoly
  have : A * C < (M + gamma) * (M ^ 2 + 2 * H * M - A) :=
    lt_of_lt_of_le hbig hlower
  linarith

/--
TeX: prop:enhancement — Strict enhancement of the growing rate.
-/
theorem prop_enhancement
    {H A gamma beta sigma : ℝ}
    (hH : 0 ≤ H) (hA : 0 < A) (hgamma : 0 ≤ gamma)
    (hbeta : 0 < beta) (hsigma : 0 < sigma) :
    ∃ lam, dustRoot H A < lam ∧
      charPoly H A gamma (coupling beta sigma) lam = 0 := by
  set C := coupling beta sigma
  have hC : 0 < C := mul_pos hbeta hsigma
  set lb := dustRoot H A
  have hlbpos : 0 < lb := dustRoot_nonneg hH hA
  have hneg : charPoly H A gamma C lb < 0 := by
    rw [charPoly_at_dustRoot (hA := le_of_lt hA)]; nlinarith
  set L := max (lb + 1) (instabilityBracket A C)
  have hLgt : lb < L := by
    have : lb < lb + 1 := by linarith
    exact lt_of_lt_of_le this (le_max_left _ _)
  have hpos : 0 < charPoly H A gamma C L :=
    charPoly_pos_of_ge_bracket hH hA hgamma hC (le_max_right _ _)
  obtain ⟨lam, hgt, _, hP⟩ :=
    exists_root_of_neg_pos hLgt (continuous_charPoly H A gamma C) hneg hpos
  exact ⟨lam, hgt, hP⟩

/-- TeX Eq. Pk: pressured characteristic polynomial. -/
def charPolyPressure (H A gamma C Bk lam : ℝ) : ℝ :=
  (lam + gamma) * (lam ^ 2 + 2 * H * lam + Bk - A) - A * C

theorem charPolyPressure_zero (H A gamma C Bk : ℝ) :
    charPolyPressure H A gamma C Bk 0 = gamma * (Bk - A) - A * C := by
  unfold charPolyPressure
  ring

theorem continuous_charPolyPressure (H A gamma C Bk : ℝ) :
    Continuous (charPolyPressure H A gamma C Bk) := by
  unfold charPolyPressure
  continuity

theorem charPolyPressure_bracket_pos
    {H A gamma C Bk : ℝ}
    (hH : 0 ≤ H) (hA : 0 < A) (hgamma : 0 ≤ gamma) (hC : 0 < C)
    (hBk : 0 ≤ Bk) :
    0 < charPolyPressure H A gamma C Bk (instabilityBracket A C) := by
  set L := instabilityBracket A C
  have hbase : 0 < charPoly H A gamma C L :=
    charPoly_bracket_pos hH hA hgamma hC
  have hdiff :
      charPolyPressure H A gamma C Bk L - charPoly H A gamma C L =
        (L + gamma) * Bk := by
    unfold charPolyPressure charPoly; ring
  have hLpos : 0 < L := instabilityBracket_pos hA hC
  have hge : charPoly H A gamma C L ≤ charPolyPressure H A gamma C Bk L := by
    have : 0 ≤ (L + gamma) * Bk :=
      mul_nonneg (by nlinarith [hgamma, hLpos]) hBk
    linarith [hdiff]
  exact lt_of_lt_of_le hbase hge

/--
TeX: prop:jeans — Sufficient response-induced Jeans crossing.
-/
theorem prop_jeans
    {H A gamma beta sigma Bk : ℝ}
    (hH : 0 ≤ H) (hA : 0 < A) (hgamma : 0 ≤ gamma)
    (hbeta : 0 < beta) (hsigma : 0 < sigma) (hBk : 0 ≤ Bk)
    (hcond : gamma * (Bk - A) < A * coupling beta sigma) :
    ∃ lam, 0 < lam ∧
      charPolyPressure H A gamma (coupling beta sigma) Bk lam = 0 := by
  set C := coupling beta sigma
  have hC : 0 < C := mul_pos hbeta hsigma
  have hLpos : 0 < instabilityBracket A C := instabilityBracket_pos hA hC
  have hneg : charPolyPressure H A gamma C Bk 0 < 0 := by
    rw [charPolyPressure_zero]; linarith
  have hpos := charPolyPressure_bracket_pos hH hA hgamma hC hBk
  obtain ⟨lam, h0, _, hP⟩ :=
    exists_root_of_neg_pos hLpos (continuous_charPolyPressure H A gamma C Bk)
      hneg hpos
  exact ⟨lam, h0, hP⟩

end

end Paper5
