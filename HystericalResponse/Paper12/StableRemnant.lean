import Mathlib
import HystericalResponse.Paper12.WakeDynamics
import HystericalResponse.Paper12.RemnantExistence
import HystericalResponse.Paper12.RemnantStability

/-!
TeX: `12_nonsingular_gravitational_collapse/paper_12_nonsingular_collapse.tex`,
Section “Nonsingular Gravitational Collapse Theorem”.
-/

set_option autoImplicit false

namespace Paper12

noncomputable section

open Filter Topology

/-- TeX: thm:remnant (1) — existence half. -/
theorem thm_remnant_existence (W : WakeHypotheses) :
    ∃ Rstar, 0 < Rstar ∧ W.G.H Rstar = W.G.GM / Rstar ^ 2 ∧
      netForce W.G Rstar = 0 := by
  obtain ⟨Rstar, _, _, hF, hpos⟩ := thm_existence W
  refine ⟨Rstar, hpos, ?_, hF⟩
  simpa [netForce, sub_eq_zero] using hF

/-- Package a restoring slope point into `RestoringRemnant`. -/
def restoringOfSlope {H' GM Rstar gamma : ℝ}
    (hR : 0 < Rstar) (hDamp : 0 < gamma)
    (hstr : H' < - (2 * GM / Rstar ^ 3)) : RestoringRemnant where
  Rstar := Rstar
  Fprime := forceSlope H' GM Rstar
  gamma := gamma
  hR := hR
  hRest := lem_slope hstr
  hDamp := hDamp

/-- TeX: thm:remnant (2)–(3) — restoring slope plus full damped asymptotic stability. -/
theorem thm_remnant_stability {H' GM Rstar gamma : ℝ}
    (hR : 0 < Rstar) (hDamp : 0 < gamma)
    (hstr : H' < - (2 * GM / Rstar ^ 3)) :
    forceSlope H' GM Rstar < 0 ∧
      (∀ z : ℂ,
        charPolyℂ gamma (-forceSlope H' GM Rstar) z = 0 → z.re < 0) ∧
      (∀ A B omega : ℝ, Tendsto (underdampedSol gamma A B omega) atTop (nhds 0)) ∧
      (∀ A B : ℝ, Tendsto (criticalSol gamma A B) atTop (nhds 0)) ∧
      (∀ r1 r2 A B : ℝ, r1 < 0 → r2 < 0 →
        Tendsto (fun t : ℝ => A * Real.exp (r1 * t) + B * Real.exp (r2 * t))
          atTop (nhds 0)) := by
  let S := restoringOfSlope hR hDamp hstr
  have hd := thm_damped S
  refine ⟨S.hRest, ?_, hd.2.1, hd.2.2.1, hd.2.2.2⟩
  intro z hz
  apply hd.1
  simpa [S, restoringOfSlope, RestoringRemnant.kappa] using hz

/-- TeX: thm:remnant — Stable Hysterical Remnant. -/
theorem thm_remnant (W : WakeHypotheses) {H' gamma : ℝ}
    (hDamp : 0 < gamma) :
    (∃ Rstar, 0 < Rstar ∧ W.G.H Rstar = W.G.GM / Rstar ^ 2) ∧
      (∀ Rstar, 0 < Rstar →
        H' < - (2 * W.G.GM / Rstar ^ 3) →
          forceSlope H' W.G.GM Rstar < 0 ∧
            (∀ z : ℂ,
              charPolyℂ gamma (-forceSlope H' W.G.GM Rstar) z = 0 → z.re < 0) ∧
            (∀ A B omega : ℝ,
              Tendsto (underdampedSol gamma A B omega) atTop (nhds 0)) ∧
            (∀ A B : ℝ, Tendsto (criticalSol gamma A B) atTop (nhds 0)) ∧
            (∀ r1 r2 A B : ℝ, r1 < 0 → r2 < 0 →
              Tendsto (fun t : ℝ => A * Real.exp (r1 * t) + B * Real.exp (r2 * t))
                atTop (nhds 0))) := by
  refine ⟨thm_existence_balance W, ?_⟩
  intro Rstar hR hstr
  exact thm_remnant_stability (GM := W.G.GM) hR hDamp hstr

/-- TeX: cor:nofocus — all standard linear modes converge to the remnant radius. -/
theorem cor_nofocus_underdamped (S : RestoringRemnant) (A B omega : ℝ) :
    Tendsto (fun t : ℝ => S.Rstar + underdampedSol S.gamma A B omega t)
      atTop (nhds S.Rstar) := by
  have h := (thm_damped S).2.1 A B omega
  simpa [add_comm] using tendsto_const_nhds.add h

theorem cor_nofocus_critical (S : RestoringRemnant) (A B : ℝ) :
    Tendsto (fun t : ℝ => S.Rstar + criticalSol S.gamma A B t)
      atTop (nhds S.Rstar) := by
  have h := (thm_damped S).2.2.1 A B
  simpa [add_comm] using tendsto_const_nhds.add h

theorem cor_nofocus_overdamped (S : RestoringRemnant) {r1 r2 A B : ℝ}
    (h1 : r1 < 0) (h2 : r2 < 0) :
    Tendsto (fun t : ℝ => S.Rstar + (A * Real.exp (r1 * t) + B * Real.exp (r2 * t)))
      atTop (nhds S.Rstar) := by
  have h := (thm_damped S).2.2.2 r1 r2 A B h1 h2
  simpa [add_comm] using tendsto_const_nhds.add h

/-- Combined no-focus packaging matching TeX Cor. nofocus. -/
theorem cor_nofocus (S : RestoringRemnant) :
    (∀ A B omega : ℝ,
      Tendsto (fun t : ℝ => S.Rstar + underdampedSol S.gamma A B omega t)
        atTop (nhds S.Rstar)) ∧
    (∀ A B : ℝ,
      Tendsto (fun t : ℝ => S.Rstar + criticalSol S.gamma A B t)
        atTop (nhds S.Rstar)) ∧
    (∀ r1 r2 A B : ℝ, r1 < 0 → r2 < 0 →
      Tendsto (fun t : ℝ => S.Rstar + (A * Real.exp (r1 * t) + B * Real.exp (r2 * t)))
        atTop (nhds S.Rstar)) :=
  ⟨cor_nofocus_underdamped S, cor_nofocus_critical S,
    fun r1 r2 A B h1 h2 =>
      cor_nofocus_overdamped (S := S) (r1 := r1) (r2 := r2) (A := A) (B := B) h1 h2⟩

/-- TeX: thm:nonsingular — Nonsingular Gravitational Collapse. -/
theorem thm_nonsingular (W : WakeHypotheses) {H' gamma : ℝ}
    (hDamp : 0 < gamma)
    (hSlope : ∀ Rstar, 0 < Rstar →
      W.G.H Rstar = W.G.GM / Rstar ^ 2 →
        H' < - (2 * W.G.GM / Rstar ^ 3)) :
    -- Wake theorem (HRT + horizon)
    ((∃ R : ℝ, 0 < R ∧ W.G.H R ≠ 0) ∧ (∀ R : ℝ, 0 < R → 0 < W.G.H R)) ∧
    -- Remnant existence
    (∃ Rstar, 0 < Rstar ∧ W.G.H Rstar = W.G.GM / Rstar ^ 2) ∧
    -- Linearised attraction to remnant for all standard modes
    (∀ Rstar, 0 < Rstar →
      W.G.H Rstar = W.G.GM / Rstar ^ 2 →
        forceSlope H' W.G.GM Rstar < 0 ∧
          (∀ z : ℂ,
            charPolyℂ gamma (-forceSlope H' W.G.GM Rstar) z = 0 → z.re < 0) ∧
          (∀ A B omega : ℝ,
            Tendsto (fun t => Rstar + underdampedSol gamma A B omega t)
              atTop (nhds Rstar)) ∧
          (∀ A B : ℝ,
            Tendsto (fun t => Rstar + criticalSol gamma A B t)
              atTop (nhds Rstar)) ∧
          (∀ r1 r2 A B : ℝ, r1 < 0 → r2 < 0 →
            Tendsto (fun t => Rstar + (A * Real.exp (r1 * t) + B * Real.exp (r2 * t)))
              atTop (nhds Rstar))) := by
  refine ⟨thm_wake_of W, thm_existence_balance W, ?_⟩
  intro Rstar hR hBal
  have hstr := hSlope Rstar hR hBal
  let S := restoringOfSlope (GM := W.G.GM) hR hDamp hstr
  have hpack := thm_remnant_stability (GM := W.G.GM) hR hDamp hstr
  have hn := cor_nofocus S
  refine ⟨hpack.1, hpack.2.1, ?_, ?_, ?_⟩
  · intro A B omega
    simpa [S, restoringOfSlope] using hn.1 A B omega
  · intro A B
    simpa [S, restoringOfSlope] using hn.2.1 A B
  · intro r1 r2 A B h1 h2
    simpa [S, restoringOfSlope] using hn.2.2 r1 r2 A B h1 h2

/-- Existence companion. -/
theorem cor_nofocus_exists (W : WakeHypotheses) :
    ∃ Rstar, 0 < Rstar ∧ netForce W.G Rstar = 0 := by
  obtain ⟨Rstar, hpos, _, hF⟩ := thm_remnant_existence W
  exact ⟨Rstar, hpos, hF⟩

end

end Paper12
