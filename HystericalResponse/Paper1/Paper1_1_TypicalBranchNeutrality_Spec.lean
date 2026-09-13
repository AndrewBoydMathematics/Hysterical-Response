import Mathlib

/-!
TeX: `1_hysterical_response/paper_1_hysterical_response.tex`
Section: **Hysterical neutrality and gravitational survival**
(typical-branch / sequence form of `thm:neutrality`).

Route: susceptibility envelope → weighted channel bounds → two-level
`|B|≤|δf|/2` inheritance → `thm:neutrality` sequence form
(`hysterical_neutrality_bound`, `hysterical_neutrality_limit`).
-/

namespace Paper1_1

open scoped BigOperators
open Filter Metric

noncomputable section

/-! ## 1. Paper-1 single-channel continuity bound, abstracted -/

/-- A stable response channel is controlled by its semigroup factor M/γ,
    the norm of the force functional on that channel, and the source norm. -/
def SusceptibilityEnvelope (M γ forceNorm sourceNorm : ℝ) : ℝ :=
  (M / γ) * forceNorm * sourceNorm

/-- Once the Paper-1 resolvent estimate has supplied `|χ| ≤ envelope`, a
    neutral channel (`forceNorm = 0`) has zero susceptibility. -/
theorem susceptibility_zero_of_forceNorm_zero
    (M γ sourceNorm χ : ℝ)
    (_hγ : γ ≠ 0)
    (hχ : |χ| ≤ SusceptibilityEnvelope M γ 0 sourceNorm) :
    χ = 0 := by
  have henv : SusceptibilityEnvelope M γ 0 sourceNorm = 0 := by
    simp [SusceptibilityEnvelope]
  rw [henv] at hχ
  exact abs_eq_zero.mp (le_antisymm hχ (abs_nonneg χ))

/-! ## 2. Finite channel aggregation -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If every channel susceptibility is bounded by a nonnegative envelope,
    the absolute total response is bounded by the weighted sum of envelopes. -/
theorem weighted_response_bound
    (w χ env : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hχ : ∀ i, |χ i| ≤ env i) :
    |∑ i, w i * χ i| ≤ ∑ i, w i * env i := by
  calc
    |∑ i, w i * χ i|
        ≤ ∑ i, |w i * χ i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |χ i| := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [abs_mul, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w i * env i := by
          apply Finset.sum_le_sum
          intro i _hi
          exact mul_le_mul_of_nonneg_left (hχ i) (hw i)

/-- Paper-1 two-level inheritance. -/
theorem twoLevel_neutrality_bound
    (w B δf : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hB : ∀ i, |B i| ≤ |δf i| / 2) :
    |∑ i, w i * B i| ≤ (∑ i, w i * |δf i|) / 2 := by
  have hmain := weighted_response_bound w B (fun i => |δf i| / 2) hw hB
  calc
    |∑ i, w i * B i| ≤ ∑ i, w i * (|δf i| / 2) := hmain
    _ = ∑ i, (w i * |δf i|) / 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (∑ i, w i * |δf i|) / 2 := (Finset.sum_div Finset.univ (fun i => w i * |δf i|) 2).symm

/-- Exact finite-N neutrality corollary. -/
theorem twoLevel_exact_neutrality
    (w B δf : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hB : ∀ i, |B i| ≤ |δf i| / 2)
    (hneutral : ∑ i, w i * |δf i| = 0) :
    ∑ i, w i * B i = 0 := by
  have h := twoLevel_neutrality_bound w B δf hw hB
  rw [hneutral, zero_div] at h
  exact abs_nonpos_iff.mp h

/-- Quantitative approximate-neutrality corollary. -/
theorem twoLevel_approx_neutrality
    (w B δf : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hB : ∀ i, |B i| ≤ |δf i| / 2)
    (ε : ℝ)
    (hneutral : ∑ i, w i * |δf i| ≤ ε) :
    |∑ i, w i * B i| ≤ ε / 2 := by
  calc
    |∑ i, w i * B i|
        ≤ (∑ i, w i * |δf i|) / 2 := twoLevel_neutrality_bound w B δf hw hB
    _ ≤ ε / 2 := by gcongr

/-! ## 3. "Typical branch" finite approximation -/

theorem typical_branch_L1_bound
    (w δf : ι → ℝ)
    (Typical : Finset ι)
    (ε η W : ℝ)
    (hε : 0 ≤ ε)
    (hw : ∀ i, 0 ≤ w i)
    (htyp : ∀ i ∈ Typical, |δf i| ≤ ε)
    (hweight : ∑ i ∈ Typical, w i ≤ W)
    (hexception : ∑ i ∈ Typicalᶜ, w i * |δf i| ≤ η) :
    ∑ i, w i * |δf i| ≤ ε * W + η := by
  have hsplit :
      ∑ i, w i * |δf i| =
        (∑ i ∈ Typical, w i * |δf i|) + ∑ i ∈ Typicalᶜ, w i * |δf i| :=
    (Finset.sum_add_sum_compl Typical (fun i => w i * |δf i|)).symm
  have htypSum : ∑ i ∈ Typical, w i * |δf i| ≤ ε * ∑ i ∈ Typical, w i := by
    calc
      ∑ i ∈ Typical, w i * |δf i|
          ≤ ∑ i ∈ Typical, w i * ε := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (htyp i hi) (hw i)
      _ = ∑ i ∈ Typical, ε * w i := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = ε * ∑ i ∈ Typical, w i := (Finset.mul_sum Typical w ε).symm
  rw [hsplit]
  calc
    (∑ i ∈ Typical, w i * |δf i|) + ∑ i ∈ Typicalᶜ, w i * |δf i|
        ≤ ε * (∑ i ∈ Typical, w i) + η := by linarith
    _ ≤ ε * W + η := by nlinarith

theorem typical_branch_hysterical_bound
    (w B δf : ι → ℝ)
    (Typical : Finset ι)
    (ε η W : ℝ)
    (hε : 0 ≤ ε)
    (hw : ∀ i, 0 ≤ w i)
    (hB : ∀ i, |B i| ≤ |δf i| / 2)
    (htyp : ∀ i ∈ Typical, |δf i| ≤ ε)
    (hweight : ∑ i ∈ Typical, w i ≤ W)
    (hexception : ∑ i ∈ Typicalᶜ, w i * |δf i| ≤ η) :
    |∑ i, w i * B i| ≤ (ε * W + η) / 2 := by
  have hL1 := typical_branch_L1_bound w δf Typical ε η W hε hw htyp hweight hexception
  exact twoLevel_approx_neutrality w B δf hw hB (ε * W + η) hL1

/-! ## 4. Hysterical Neutrality Theorem (sequence form, algebraic) -/

/-- External Hysterical force bound from susceptibility envelope. -/
theorem hysterical_neutrality_bound
    (M γ forceNorm sourceNorm C_star S_star : ℝ)
    (hγ : 0 < γ)
    (hforce : 0 ≤ forceNorm)
    (hsource : 0 ≤ sourceNorm)
    (hCstar : 0 ≤ C_star)
    (hC : M / γ ≤ C_star)
    (hS : sourceNorm ≤ S_star)
    (F_H : ℝ)
    (hFH : |F_H| ≤ (M / γ) * forceNorm * sourceNorm) :
    |F_H| ≤ C_star * S_star * forceNorm := by
  have h1 : (M / γ) * forceNorm * sourceNorm ≤ C_star * forceNorm * sourceNorm := by
    gcongr
  have h2 : C_star * forceNorm * sourceNorm ≤ C_star * forceNorm * S_star := by
    gcongr
  calc
    |F_H| ≤ (M / γ) * forceNorm * sourceNorm := hFH
    _ ≤ C_star * forceNorm * sourceNorm := h1
    _ ≤ C_star * forceNorm * S_star := h2
    _ = C_star * S_star * forceNorm := by ring

/-- If `|F_H n| ≤ K |F_ext n|` and `F_ext → 0`, then `F_H → 0`. -/
theorem hysterical_neutrality_limit
    (F_ext F_H : ℕ → ℝ) (K : ℝ)
    (_hK : 0 ≤ K)
    (hbound : ∀ n, |F_H n| ≤ K * |F_ext n|)
    (hlim : Tendsto F_ext atTop (nhds (0 : ℝ))) :
    Tendsto F_H atTop (nhds (0 : ℝ)) := by
  have hg : Tendsto (fun n => K * |F_ext n|) atTop (nhds (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul hlim.abs
  refine squeeze_zero_norm ?_ hg
  intro n
  simpa [Real.norm_eq_abs] using hbound n

/-- TeX: thm:neutrality — quantitative bound. -/
theorem thm_neutrality_bound
    (M γ forceNorm sourceNorm C_star S_star : ℝ)
    (hγ : 0 < γ)
    (hforce : 0 ≤ forceNorm)
    (hsource : 0 ≤ sourceNorm)
    (hCstar : 0 ≤ C_star)
    (hC : M / γ ≤ C_star)
    (hS : sourceNorm ≤ S_star)
    (F_H : ℝ)
    (hFH : |F_H| ≤ (M / γ) * forceNorm * sourceNorm) :
    |F_H| ≤ C_star * S_star * forceNorm :=
  hysterical_neutrality_bound M γ forceNorm sourceNorm C_star S_star
    hγ hforce hsource hCstar hC hS F_H hFH

/-- TeX: thm:neutrality — sequential limit form. -/
theorem thm_neutrality_limit
    (F_ext F_H : ℕ → ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hbound : ∀ n, |F_H n| ≤ K * |F_ext n|)
    (hlim : Tendsto F_ext atTop (nhds (0 : ℝ))) :
    Tendsto F_H atTop (nhds (0 : ℝ)) :=
  hysterical_neutrality_limit F_ext F_H K hK hbound hlim

end

end Paper1_1
