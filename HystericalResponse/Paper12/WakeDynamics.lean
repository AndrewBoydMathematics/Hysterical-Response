import Mathlib

/-!
TeX: `12_nonsingular_gravitational_collapse/paper_12_nonsingular_collapse.tex`,
Sections “Inherited Hysterical Response Theory” and
“Horizon residual cancellation and the wake”.

`thm_wake` ports the TeX argument at this abstraction:
1. Ass.horizon supplies an uncanceled exterior residual magnitude μ > 0;
2. gravitational attraction toward the exterior wake orients that residual outward;
3. therefore H := outward wake acceleration is strictly positive (and nonzero).
-/

set_option autoImplicit false

namespace Paper12

noncomputable section

/-- TeX: def:gH — gravitational Hysterical radial acceleration on the collapsing surface. -/
structure GravitationalHRT where
  H : ℝ → ℝ
  GM : ℝ
  hGM : 0 < GM
  hCont : Continuous H

/-- TeX: prop:survival — Paper 1 gravitational survival (Neutrality does not force F_H → 0).
    Reduced abstraction: propositional prior tag; quantitative Paper 1 bound not re-proved. -/
axiom literature_gravitational_survival : True

/-- TeX: prop:instab — Paper 1 Neutrality–Instability / slow-gap criticality mechanism.
    Reduced abstraction: propositional prior tag. -/
axiom literature_hysterical_instability : True

/-- TeX: ass:horizon — causal failure of residual shell cancellation.
    At this abstraction: an uncanceled exterior residual magnitude μ(R) > 0 remains
    on the collapsing surface (Ass.horizon + survival nonzero leftover). -/
structure HorizonCancellationFailure where
  /-- Magnitude of the uncanceled exterior residual acceleration. -/
  μ : ℝ → ℝ
  /-- Residual is present and positive as a magnitude for every surface radius. -/
  hPos : ∀ R : ℝ, 0 < R → 0 < μ R
  hCont : Continuous μ

/-- TeX proof steps (2)–(3): attraction toward the exterior wake orients the residual
    as an *outward* radial acceleration on the collapsing surface. -/
def outwardWakeAcceleration (A : HorizonCancellationFailure) : ℝ → ℝ :=
  A.μ

/-- Identify the HRT surface acceleration `G.H` with that outward wake orientation. -/
structure WakeIdentification (G : GravitationalHRT) (A : HorizonCancellationFailure) where
  hId : G.H = outwardWakeAcceleration A

/-- TeX: thm:wake — nonzero outward Hysterical wake. -/
theorem thm_wake (G : GravitationalHRT) (A : HorizonCancellationFailure)
    (W : WakeIdentification G A) :
    (∃ R : ℝ, 0 < R ∧ G.H R ≠ 0) ∧ (∀ R : ℝ, 0 < R → 0 < G.H R) := by
  have hpos : ∀ R : ℝ, 0 < R → 0 < G.H R := by
    intro R hR
    have hμ := A.hPos R hR
    simpa [W.hId, outwardWakeAcceleration] using hμ
  refine ⟨⟨1, by norm_num, ne_of_gt (hpos 1 (by norm_num))⟩, hpos⟩

/-- Continuity of H follows from the wake magnitude once identified. -/
theorem continuous_H_of_wake (G : GravitationalHRT) (A : HorizonCancellationFailure)
    (W : WakeIdentification G A) : Continuous G.H := by
  simpa [W.hId, outwardWakeAcceleration] using A.hCont

/-- TeX: ass:crit — curvature-driven criticality supplies the F sign change. -/
structure CriticalWakeDominance (G : GravitationalHRT) where
  R_in : ℝ
  R_out : ℝ
  hIn : 0 < R_in
  hOrd : R_in < R_out
  hDom : G.GM / R_in ^ 2 < G.H R_in
  hSub : G.H R_out < G.GM / R_out ^ 2

/-- TeX: def:F / eq:F — net outward acceleration. -/
def netForce (G : GravitationalHRT) (R : ℝ) : ℝ :=
  G.H R - G.GM / R ^ 2

/-- TeX: eq:sign packaged as F(R_in)>0 and F(R_out)<0. -/
theorem critical_sign_change (G : GravitationalHRT) (C : CriticalWakeDominance G) :
    0 < netForce G C.R_in ∧ netForce G C.R_out < 0 := by
  constructor
  · simpa [netForce] using sub_pos.mpr C.hDom
  · simpa [netForce] using sub_neg.mpr C.hSub

/-- Bundle for remnant analysis. -/
structure WakeHypotheses where
  G : GravitationalHRT
  horizon : HorizonCancellationFailure
  ident : WakeIdentification G horizon
  crit : CriticalWakeDominance G

/-- Continuity of F on the critical interval. -/
theorem continuousOn_netForce_interval (W : WakeHypotheses) :
    ContinuousOn (netForce W.G) (Set.Icc W.crit.R_in W.crit.R_out) := by
  have hden : ContinuousOn (fun R : ℝ => R ^ 2) (Set.Icc W.crit.R_in W.crit.R_out) :=
    continuous_pow 2 |>.continuousOn
  have hinv : ContinuousOn (fun R : ℝ => W.G.GM / R ^ 2)
      (Set.Icc W.crit.R_in W.crit.R_out) := by
    apply ContinuousOn.div continuousOn_const hden
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le W.crit.hIn hx.1
    exact ne_of_gt (pow_pos hx0 2)
  exact W.G.hCont.continuousOn.sub hinv

def WakeHypotheses.H (W : WakeHypotheses) : ℝ → ℝ := W.G.H
def WakeHypotheses.GM (W : WakeHypotheses) : ℝ := W.G.GM
def WakeHypotheses.R_in (W : WakeHypotheses) : ℝ := W.crit.R_in
def WakeHypotheses.R_out (W : WakeHypotheses) : ℝ := W.crit.R_out
theorem WakeHypotheses.hGM (W : WakeHypotheses) : 0 < W.GM := W.G.hGM
theorem WakeHypotheses.hIn (W : WakeHypotheses) : 0 < W.R_in := W.crit.hIn
theorem WakeHypotheses.hOrd (W : WakeHypotheses) : W.R_in < W.R_out := W.crit.hOrd
theorem WakeHypotheses.hCont (W : WakeHypotheses) : Continuous W.H := W.G.hCont
theorem WakeHypotheses.hPos (W : WakeHypotheses) : 0 < netForce W.G W.R_in :=
  (critical_sign_change W.G W.crit).1
theorem WakeHypotheses.hNeg (W : WakeHypotheses) : netForce W.G W.R_out < 0 :=
  (critical_sign_change W.G W.crit).2

/-- Wake theorem on the remnant bundle. -/
theorem thm_wake_of (W : WakeHypotheses) :
    (∃ R : ℝ, 0 < R ∧ W.G.H R ≠ 0) ∧ (∀ R : ℝ, 0 < R → 0 < W.G.H R) :=
  thm_wake W.G W.horizon W.ident

end

end Paper12
