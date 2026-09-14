import Mathlib
import HystericalResponse.Paper10.LinearEMSpectrum
import HystericalResponse.Paper10.ReciprocalMatching

/-!
TeX: `10_cyclic_cosmology/paper_10_hysterical_ccc.tex`,
Section “Active versus passive conformal cyclic cosmology”.

Algebraic packaging of Definition `def:active-bang`:
supercritical IR EM trigger + reciprocal hot incoming branch + radiation seed.
-/

set_option autoImplicit false

namespace Paper10

noncomputable section

/-- Minimal data for an active big-bang-like crossover at the algebraic abstraction. -/
structure ActiveCrossover where
  H_out : ℝ
  rhoHat : ℝ
  aMinus : ℝ
  aPlus : ℝ
  hH : 0 < H_out
  hRho : 0 < rhoHat
  hRec : aPlus * aMinus = 1
  hLarge : 1 < aMinus

/-- TeX: def:active-bang — hot incoming branch. -/
theorem thm_active_hot_branch (C : ActiveCrossover) :
    rhoOut C.rhoHat C.aMinus < C.rhoHat ∧
      C.rhoHat < rhoIn C.rhoHat C.aPlus :=
  thm_hot_cold_limits C.hRho C.hLarge C.hRec

/-- Incoming radiation-era identity under `a = H η`. -/
theorem thm_active_radiation_seed (C : ActiveCrossover) (eta t a : ℝ)
    (heta : 0 < eta)
    (ha : a = C.H_out * eta) (ht : t = C.H_out * eta ^ 2 / 2) :
    a ^ 2 = 2 * C.H_out * t ∧ a = Real.sqrt (2 * C.H_out * t) := by
  refine ⟨thm_radiation C.H_out eta t a ha ht, ?_⟩
  exact thm_radiation_sqrt C.H_out eta t a C.hH heta ha ht

/-- Supercritical zero-mode threshold as the active trigger. -/
def supercriticalEM (H gamma A : ℝ) : Prop :=
  2 * H * gamma < A

theorem thm_active_trigger {H gamma A : ℝ}
    (hH : 0 < H) (hg : 0 < gamma) (hsup : supercriticalEM H gamma A) :
    0 < 2 * H * A / gamma - 4 * H ^ 2 :=
  thm_band_nonempty hH hg hsup

/-- Combined algebraic spine of the active crossover claim. -/
theorem thm_active_crossover_spine
    (H gamma A : ℝ) (C : ActiveCrossover)
    (hH : 0 < H) (hg : 0 < gamma) (hsup : supercriticalEM H gamma A)
    (eta t a : ℝ) (heta : 0 < eta)
    (ha : a = C.H_out * eta) (ht : t = C.H_out * eta ^ 2 / 2) :
    (0 < 2 * H * A / gamma - 4 * H ^ 2) ∧
      (rhoOut C.rhoHat C.aMinus < C.rhoHat ∧ C.rhoHat < rhoIn C.rhoHat C.aPlus) ∧
      (a ^ 2 = 2 * C.H_out * t) ∧
      (a = Real.sqrt (2 * C.H_out * t)) := by
  refine ⟨thm_active_trigger hH hg hsup, thm_active_hot_branch C, ?_⟩
  exact thm_active_radiation_seed C eta t a heta ha ht

end

end Paper10
