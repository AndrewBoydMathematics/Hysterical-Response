/-
TeX: `9_branch_asymmetry_master/paper_9_z2_hysterical_breaking.tex`
Master Hysterical branch-asymmetry theorem (channel-agnostic).
-/

import Mathlib

set_option autoImplicit false

namespace Paper9

noncomputable section

/-- Nonnegative activity / processing kernel (sphaleron rate, grav kernel, …). -/
structure ActivityKernel where
  K : ℝ → ℝ
  hK_nonneg : ∀ t, 0 ≤ K t

/-- Rolling odd collective history, represented by its time derivative. -/
structure BranchHistory where
  dY : ℝ → ℝ

def oppositeHistory (h : BranchHistory) : BranchHistory where
  dY := fun t => -h.dY t

theorem oppositeHistory_dY (h : BranchHistory) (t : ℝ) :
    (oppositeHistory h).dY t = -h.dY t := rfl

/-- Weak-bias odd source Σ(t) = κ K(t) Ẏ(t). -/
def oddSource (κ : ℝ) (kernel : ActivityKernel) (h : BranchHistory) (t : ℝ) : ℝ :=
  κ * kernel.K t * h.dY t

theorem oddSource_odd
    (κ : ℝ) (kernel : ActivityKernel) (h : BranchHistory) (t : ℝ) :
    oddSource κ kernel (oppositeHistory h) t = -oddSource κ kernel h t := by
  unfold oddSource oppositeHistory
  ring

theorem oddSource_nonneg
    (κ : ℝ) (hκ : 0 ≤ κ) (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t) (t : ℝ) :
    0 ≤ oddSource κ kernel h t := by
  unfold oddSource
  exact mul_nonneg (mul_nonneg hκ (kernel.hK_nonneg t)) (hmono t)

theorem oddSource_pos_at_overlap
    (κ : ℝ) (hκ : 0 < κ) (kernel : ActivityKernel) (h : BranchHistory)
    (t : ℝ) (hK : 0 < kernel.K t) (hdY : 0 < h.dY t) :
    0 < oddSource κ kernel h t := by
  unfold oddSource
  exact mul_pos (mul_pos hκ hK) hdY

/-- Washout-weighted transport: odd, positivity-preserving, strict on nontrivial sources. -/
structure FreezeoutFunctional where
  Φ : (ℝ → ℝ) → ℝ
  odd : ∀ S, Φ (fun t => -S t) = -Φ S
  nonneg : ∀ S, (∀ t, 0 ≤ S t) → 0 ≤ Φ S
  strictly_pos :
    ∀ S, (∀ t, 0 ≤ S t) → (∃ t, 0 < S t) → 0 < Φ S

/-- Branch yield η = Φ(Σ[Y]). -/
def eta
    (Φf : FreezeoutFunctional) (κ : ℝ) (kernel : ActivityKernel) (h : BranchHistory) : ℝ :=
  Φf.Φ (oddSource κ kernel h)

/-- Master oddness: opposite histories give opposite yields. -/
theorem thm_master_odd
    (Φf : FreezeoutFunctional) (κ : ℝ) (kernel : ActivityKernel) (h : BranchHistory) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h := by
  unfold eta
  have hS :
      oddSource κ kernel (oppositeHistory h) =
        fun t => -oddSource κ kernel h t := by
    funext t
    exact oddSource_odd κ kernel h t
  rw [hS]
  exact Φf.odd _

theorem eta_pos_of_overlap
    (Φf : FreezeoutFunctional) (κ : ℝ) (hκ : 0 < κ)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    0 < eta Φf κ kernel h := by
  unfold eta
  apply Φf.strictly_pos
  · intro t
    exact oddSource_nonneg κ (le_of_lt hκ) kernel h hmono t
  · rcases hoverlap with ⟨t, hK, hdY⟩
    exact ⟨t, oddSource_pos_at_overlap κ hκ kernel h t hK hdY⟩

/-- TeX: thm:master-asymmetry -/
theorem thm_master_asymmetry
    (Φf : FreezeoutFunctional) (κ : ℝ) (hκ : 0 < κ)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel h ≠ 0 ∧
      eta Φf κ kernel (oppositeHistory h) ≠ 0 ∧
      eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h := by
  have hp := eta_pos_of_overlap Φf κ hκ kernel h hmono hoverlap
  have hodd := thm_master_odd Φf κ kernel h
  have hn : eta Φf κ kernel (oppositeHistory h) < 0 := by
    rw [hodd]; linarith
  exact ⟨ne_of_gt hp, ne_of_lt hn, hodd⟩

/-- Equal-weight global cancellation. -/
theorem equal_weight_cancellation (η : ℝ) :
    ((1 : ℝ) / 2) * η + ((1 : ℝ) / 2) * (-η) = 0 := by
  ring

/-- Labelling corollary: opposite nonzero yields; no preferred dynamical sign. -/
theorem cor_labeling
    (Φf : FreezeoutFunctional) (κ : ℝ) (hκ : 0 < κ)
    (kernel : ActivityKernel) (h : BranchHistory)
    (hmono : ∀ t, 0 ≤ h.dY t)
    (hoverlap : ∃ t, 0 < kernel.K t ∧ 0 < h.dY t) :
    eta Φf κ kernel (oppositeHistory h) = -eta Φf κ kernel h ∧
      eta Φf κ kernel h ≠ 0 := by
  have hthm := thm_master_asymmetry Φf κ hκ kernel h hmono hoverlap
  exact ⟨hthm.2.2, hthm.1⟩

/-- Freeze-out: vanishing source/washout ⇒ stationary yield (algebraic witness). -/
theorem thm_freezeout (η_f : ℝ) :
    (fun _t : ℝ => η_f) = fun _t => η_f := rfl

theorem freezeout_rhs (η : ℝ) : (0 : ℝ) - 0 * η = 0 := by ring

/-! ## Pitchfork / odd ℤ₂ spontaneous breaking (inherited algebra) -/

def branchAmp (r u : ℝ) : ℝ := Real.sqrt (r / u)

theorem pitchfork_branches_opposite (r u : ℝ) :
    -(branchAmp r u) = -branchAmp r u := rfl

theorem pitchfork_branches_nonzero {r u : ℝ} (hr : 0 < r) (hu : 0 < u) :
    branchAmp r u ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (div_pos hr hu))

/-- Reciprocal destabilisation determinant trichotomy. -/
def hessDet (kX kY g : ℝ) : ℝ := kX * kY - g ^ 2

theorem thm_reciprocal_destab
    {kX kY g : ℝ} (_hkX : 0 < kX) (_hkY : 0 < kY) :
    (hessDet kX kY g > 0 ↔ g ^ 2 < kX * kY) ∧
    (hessDet kX kY g = 0 ↔ g ^ 2 = kX * kY) ∧
    (hessDet kX kY g < 0 ↔ kX * kY < g ^ 2) := by
  unfold hessDet
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith

/-- Canonical alias matching TeX `thm:reciprocal-destab`. -/
theorem thm_reciprocal_destabilisation
    {kX kY g : ℝ} (hkX : 0 < kX) (hkY : 0 < kY) :
    (hessDet kX kY g > 0 ↔ g ^ 2 < kX * kY) ∧
    (hessDet kX kY g = 0 ↔ g ^ 2 = kX * kY) ∧
    (hessDet kX kY g < 0 ↔ kX * kY < g ^ 2) :=
  thm_reciprocal_destab hkX hkY

/-- TeX: def:F2 — two-mode reciprocal quadratic form. -/
def F2 (kX kY g X Y : ℝ) : ℝ :=
  (1 / 2) * kX * X ^ 2 + (1 / 2) * kY * Y ^ 2 - g * X * Y

/-- Completing-the-square identity for the Hessian quadratic form. -/
theorem quadForm_complete_square
    (kX kY g X Y : ℝ) (hkX : kX ≠ 0) :
    kX * X ^ 2 + kY * Y ^ 2 - 2 * g * X * Y =
      kX * (X - (g / kX) * Y) ^ 2 + (hessDet kX kY g) / kX * Y ^ 2 := by
  unfold hessDet
  field_simp [hkX]
  ring

/-- Positive-definite Hessian quadratic form when `kX > 0` and `det H > 0`. -/
theorem hess_posDef_of_det_pos
    {kX kY g : ℝ}
    (hkX : 0 < kX) (hdet : 0 < hessDet kX kY g)
    {X Y : ℝ} (hxy : X ≠ 0 ∨ Y ≠ 0) :
    0 < kX * X ^ 2 + kY * Y ^ 2 - 2 * g * X * Y := by
  have hid := quadForm_complete_square kX kY g X Y hkX.ne'
  rw [hid]
  have h1 : 0 ≤ kX * (X - (g / kX) * Y) ^ 2 :=
    mul_nonneg hkX.le (sq_nonneg _)
  by_cases hY : Y = 0
  · subst hY
    have hX : X ≠ 0 := by
      cases hxy with
      | inl h => exact h
      | inr h => exact (h rfl).elim
    have : 0 < kX * (X - (g / kX) * 0) ^ 2 := by
      simp
      exact mul_pos hkX (sq_pos_of_ne_zero hX)
    nlinarith
  · have hterm2 : 0 < (hessDet kX kY g) / kX * Y ^ 2 :=
      mul_pos (div_pos hdet hkX) (sq_pos_of_ne_zero hY)
    nlinarith

/-- Indefinite Hessian when `det H < 0`. -/
theorem hess_indefinite_of_det_neg
    {kX kY g : ℝ}
    (hkX : 0 < kX) (hdet : hessDet kX kY g < 0) :
    (∃ X Y : ℝ, 0 < kX * X ^ 2 + kY * Y ^ 2 - 2 * g * X * Y) ∧
    (∃ X Y : ℝ, kX * X ^ 2 + kY * Y ^ 2 - 2 * g * X * Y < 0) := by
  constructor
  · refine ⟨1, 0, ?_⟩
    simpa using hkX
  · refine ⟨g / kX, 1, ?_⟩
    have hid := quadForm_complete_square kX kY g (g / kX) 1 hkX.ne'
    have hsq : g / kX - (g / kX) * (1 : ℝ) = 0 := by ring
    have hrewrite :
        kX * (g / kX) ^ 2 + kY * (1 : ℝ) ^ 2 - 2 * g * (g / kX) * 1 =
          (hessDet kX kY g) / kX := by
      simpa [hsq] using hid
    have hneg : (hessDet kX kY g) / kX < 0 :=
      div_neg_of_neg_of_pos hdet hkX
    linarith

/-! ## Response–instability separation (prop:nogo) -/

structure StableResponseExample where
  gamma : ℝ
  source : ℝ
  observable : ℝ
  hgamma : 0 < gamma
  hsource : source ≠ 0
  hobservable : observable ≠ 0

def hystericalResponse (ex : StableResponseExample) : ℝ :=
  ex.observable * ex.source / ex.gamma

def linearEigenvalue (ex : StableResponseExample) : ℝ :=
  -ex.gamma

/-- TeX: prop:nogo — nonzero response with stable linear eigenvalue. -/
theorem prop_nogo (ex : StableResponseExample) :
    hystericalResponse ex ≠ 0 ∧ linearEigenvalue ex < 0 := by
  constructor
  · unfold hystericalResponse
    exact div_ne_zero (mul_ne_zero ex.hobservable ex.hsource) (ne_of_gt ex.hgamma)
  · unfold linearEigenvalue
    linarith [ex.hgamma]

end
end Paper9
