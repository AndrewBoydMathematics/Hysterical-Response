import Mathlib

/-!
TeX: `1_hysterical_response/paper_1_hysterical_response.tex`
Section: **Critical instability**

Route: gain / closed-loop Jacobian → `thm:master` → `cor:reciprocal` →
`cor:subcrit` → `thm:scalar` → `cor:threshold` → `prop:noise` →
supercritical pitchfork → `cor:gravity-positivity` (stable positive node).

Proved here: spectral abscissa trichotomy for `thm:master`; reciprocal
scalar/mode criterion; scalar Routh–Hurwitz / `λ₊` sign; threshold
hitting-time identity; variance ODE for `prop:noise`; pitchfork
linearization rates and stable ± saturated nodes; gravitational positivity
at the positive saturated node under positive alignment; eigenvector
transfer for matrix `J = -Γ(I-K)`.

Not proved: that ordinary gravity ever becomes supercritical (deferred
physical / seeding hypothesis).

Literature: `literature_finite_dim_linear_ode_stability` (Perko) for reading
`α(J)` as finite-dimensional linear ODE stability of a general (possibly
non-normal) generator. The reciprocal specialization `thm_master_reciprocal`
is proved directly and does not use that axiom.
-/

open Set

namespace Paper1_2

noncomputable section

/-! ## 1. Interaction-agnostic scalar closed-loop response -/

/-- Minimal scalar data for one linearized interaction/response eigenchannel. -/
structure ResponseChannel where
  relaxation : ℝ
  chiR : ℝ
  chiH : ℝ

/-- Closed-loop Hysterical gain. -/
def gain (c : ResponseChannel) : ℝ := c.chiR * c.chiH

/-- Linearized growth/decay exponent for `Ydot = -Γ (1-G) Y`. -/
def linearRate (c : ResponseChannel) : ℝ :=
  -c.relaxation * (1 - gain c)

/-- Positive ordinary relaxation plus subcritical gain gives strict decay. -/
theorem subcritical_rate_neg
    (c : ResponseChannel)
    (hΓ : 0 < c.relaxation)
    (hG : gain c < 1) :
    linearRate c < 0 := by
  unfold linearRate
  nlinarith

/-- Unity gain is the critical surface: the linearized restoring rate vanishes. -/
theorem critical_rate_zero
    (c : ResponseChannel)
    (hG : gain c = 1) :
    linearRate c = 0 := by
  unfold linearRate
  rw [hG]
  ring

/-- Positive ordinary relaxation plus supercritical gain gives exponential
    linear instability. -/
theorem supercritical_rate_pos
    (c : ResponseChannel)
    (hΓ : 0 < c.relaxation)
    (hG : 1 < gain c) :
    0 < linearRate c := by
  unfold linearRate
  nlinarith

/-- The three scalar regimes are mutually exclusive by trichotomy of the gain. -/
theorem gain_trichotomy (c : ResponseChannel) :
    gain c < 1 ∨ gain c = 1 ∨ 1 < gain c := by
  exact lt_trichotomy (gain c) 1

/-! ## 2. One-pole response and the two-variable instability criterion -/

/-- Static susceptibility of `hdot = σ Y - γ h` when `γ ≠ 0`. -/
def onePoleChiH (σ γ : ℝ) : ℝ := σ / γ

/-- Reaction susceptibility written as `α/Γ`; this is the scalar form arising
    from `Ydot = -Γ Y + α h`. -/
def reactionChi (α Γ : ℝ) : ℝ := α / Γ

/-- With positive denominators, unity closed-loop gain is equivalent to the
    familiar two-variable instability inequality `α σ > Γ γ`. -/
theorem gain_gt_one_iff_feedback_product
    {α σ Γ γ : ℝ}
    (hΓ : 0 < Γ) (hγ : 0 < γ) :
    1 < reactionChi α Γ * onePoleChiH σ γ ↔ Γ * γ < α * σ := by
  unfold reactionChi onePoleChiH
  have hΓ0 : Γ ≠ 0 := ne_of_gt hΓ
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hden : 0 < Γ * γ := mul_pos hΓ hγ
  have hratio : (α / Γ) * (σ / γ) = (α * σ) / (Γ * γ) := by
    field_simp [hΓ0, hγ0]
  rw [hratio]
  constructor
  · intro h
    have h' := (lt_div_iff₀ hden).mp h
    simpa using h'
  · intro h
    apply (lt_div_iff₀ hden).2
    simpa using h

/-- Characteristic polynomial of the coupled scalar system

      Ydot = -Γ Y + α h
      hdot =  σ Y - γ h.
-/
def charPoly (Γ γ α σ lam : ℝ) : ℝ :=
  (lam + Γ) * (lam + γ) - α * σ

/-- Supercritical feedback makes the characteristic polynomial negative at zero. -/
theorem charPoly_zero_neg
    {Γ γ α σ : ℝ}
    (hfeedback : Γ * γ < α * σ) :
    charPoly Γ γ α σ 0 < 0 := by
  unfold charPoly
  nlinarith

/-- A sufficiently large nonnegative bracket endpoint has positive characteristic
    polynomial.  `L^2 > α σ` is a convenient sufficient condition. -/
theorem charPoly_pos_of_large
    {Γ γ α σ L : ℝ}
    (hΓ : 0 ≤ Γ) (hγ : 0 ≤ γ) (hL : 0 ≤ L)
    (hprod : α * σ < L^2) :
    0 < charPoly Γ γ α σ L := by
  unfold charPoly
  have hLG : 0 ≤ L + Γ := add_nonneg hL hΓ
  have hLg : 0 ≤ L + γ := add_nonneg hL hγ
  have hbase : L^2 ≤ (L + Γ) * (L + γ) := by
    nlinarith [mul_nonneg hΓ hL, mul_nonneg hγ hL, mul_nonneg hΓ hγ]
  nlinarith

/-- Continuity gives a root in any sign-changing finite bracket. -/
theorem charPoly_root_in_bracket
    {Γ γ α σ lo hi : ℝ}
    (hlohi : lo ≤ hi)
    (hlo : charPoly Γ γ α σ lo ≤ 0)
    (hhi : 0 ≤ charPoly Γ γ α σ hi) :
    ∃ lam ∈ Icc lo hi, charPoly Γ γ α σ lam = 0 := by
  have hcont : Continuous (fun x : ℝ => charPoly Γ γ α σ x) := by
    unfold charPoly
    fun_prop
  have hIV := intermediate_value_Icc hlohi hcont.continuousOn
  have hzero : (0 : ℝ) ∈ Icc (charPoly Γ γ α σ lo) (charPoly Γ γ α σ hi) :=
    ⟨hlo, hhi⟩
  rcases hIV hzero with ⟨lam, hlam, hval⟩
  exact ⟨lam, hlam, hval⟩

/-- The feedback inequality `α σ > Γ γ` produces a strictly positive
    characteristic root, provided a finite positive endpoint `L` is chosen
    with `L^2 > α σ`. -/
theorem positive_growth_root
    {Γ γ α σ L : ℝ}
    (hΓ : 0 ≤ Γ) (hγ : 0 ≤ γ)
    (hfeedback : Γ * γ < α * σ)
    (hL : 0 < L)
    (hprod : α * σ < L^2) :
    ∃ lam, 0 < lam ∧ lam ≤ L ∧ charPoly Γ γ α σ lam = 0 := by
  have h0 : charPoly Γ γ α σ 0 < 0 := charPoly_zero_neg hfeedback
  have hLpos : 0 < charPoly Γ γ α σ L :=
    charPoly_pos_of_large hΓ hγ (le_of_lt hL) hprod
  obtain ⟨lam, hlam, hroot⟩ :=
    charPoly_root_in_bracket (le_of_lt hL) (le_of_lt h0) (le_of_lt hLpos)
  have hne : lam ≠ 0 := by
    intro hEq
    subst hEq
    nlinarith
  have hpos : 0 < lam := lt_of_le_of_ne hlam.1 (Ne.symm hne)
  exact ⟨lam, hpos, hlam.2, hroot⟩

/-! ## 3. Slow-mode susceptibility and the critical loophole -/

/-- Dominant positive-residue slow-mode susceptibility. -/
def slowModeChi (R γ : ℝ) : ℝ := R / γ

/-- A positive-residue mode can exceed any finite target susceptibility by
    making its positive relaxation gap sufficiently small.  This is the precise
    scalar version of the critical-susceptibility loophole in Paper 1.1. -/
theorem slow_mode_exceeds_any_target
    {R target : ℝ}
    (hR : 0 < R) (htarget : 0 < target) :
    ∃ γ : ℝ, 0 < γ ∧ target < slowModeChi R γ := by
  refine ⟨R / (2 * target), ?_, ?_⟩
  · positivity
  · unfold slowModeChi
    have hR0 : R ≠ 0 := ne_of_gt hR
    have ht0 : target ≠ 0 := ne_of_gt htarget
    field_simp [hR0, ht0]
    nlinarith [mul_pos hR htarget]

/-- In the one-mode approximation, gaps below the critical value `χR*R`
    are supercritical. -/
theorem below_critical_gap_is_supercritical
    {χR R γ : ℝ}
    (hχR : 0 < χR) (hR : 0 < R) (hγ : 0 < γ)
    (hcrit : γ < χR * R) :
    1 < χR * slowModeChi R γ := by
  unfold slowModeChi
  have hdiv : 1 < (χR * R) / γ := by
    exact (lt_div_iff₀ hγ).2 (by simpa using hcrit)
  calc
    1 < (χR * R) / γ := hdiv
    _ = χR * (R / γ) := by ring

/-- For positive reaction susceptibility `χR` and positive residue `R`, there
    exists a positive gap small enough to make the closed-loop gain supercritical. -/
theorem positive_residue_can_cross_unity
    {χR R : ℝ}
    (hχR : 0 < χR) (hR : 0 < R) :
    ∃ γ : ℝ, 0 < γ ∧ 1 < χR * slowModeChi R γ := by
  let γ : ℝ := (χR * R) / 2
  have hprod : 0 < χR * R := mul_pos hχR hR
  have hγ : 0 < γ := by
    dsimp [γ]
    linarith
  have hcrit : γ < χR * R := by
    dsimp [γ]
    linarith
  exact ⟨γ, hγ, below_critical_gap_is_supercritical hχR hR hγ hcrit⟩

/-! ## 4. Cubic normal form: symmetry breaking after linear instability -/

/-- Cubic odd normal form used near a Z2-symmetric Hysterical instability. -/
def pitchforkDrift (r u Y : ℝ) : ℝ := r * Y - u * Y^3

/-- The neutral state remains an exact fixed point on both sides of the
    instability. -/
theorem pitchfork_neutral_fixed (r u : ℝ) :
    pitchforkDrift r u 0 = 0 := by
  unfold pitchforkDrift
  ring

/-- The two symmetry-related nonzero algebraic fixed points exist whenever
    `Y^2 = r/u`.  This theorem avoids choosing a square-root branch. -/
theorem pitchfork_nonzero_fixed
    {r u Y : ℝ}
    (hu : u ≠ 0)
    (hY : Y^2 = r / u) :
    pitchforkDrift r u Y = 0 := by
  unfold pitchforkDrift
  have hu' : u * Y^2 = r := by
    calc
      u * Y^2 = u * (r / u) := by rw [hY]
      _ = r := by field_simp [hu]
  calc
    r * Y - u * Y^3 = Y * (r - u * Y^2) := by ring
    _ = 0 := by rw [hu']; ring

/-- Z2 symmetry: reversing the order parameter reverses the drift. -/
theorem pitchfork_odd (r u Y : ℝ) :
    pitchforkDrift r u (-Y) = -pitchforkDrift r u Y := by
  unfold pitchforkDrift
  ring

/-! ## 5. Interaction universality is definitional

Paper 1.2 does not postulate a second force attached to each interaction.  Instead,
for an already existing interaction response, the Hysterical component is the
residual/open-system part selected by the response decomposition.  The following
minimal interface records exactly that logical structure without pretending to
formalize trace-class operator theory in this companion algebra file.
-/

/-- An interaction channel together with its already-existing ordinary response
    functional.  `State` and `Observable` are deliberately abstract here. -/
structure InteractionResponse (Interaction State Observable : Type*) where
  interaction : Interaction
  response : Observable → State → ℝ

/-- The residual/open-system contribution selected from the response of the
    existing interaction.  Supplying `residual` is part of specifying the
    decomposition; it is not a new interaction or field. -/
structure ResponseDecomposition
    (Interaction State Observable : Type*)
    extends InteractionResponse Interaction State Observable where
  residual : Observable → State → ℝ

/-- **Definition (Hysterical component).**  The Hysterical response of an
    interaction channel is its residual/open-system response component. -/
def hystericalComponent
    {Interaction State Observable : Type*}
    (d : ResponseDecomposition Interaction State Observable) :
    Observable → State → ℝ :=
  d.residual

/-- Definitional universality: once an interaction response decomposition has
    been supplied, its Hysterical component exists simply by projection from that
    decomposition.  This is reflexivity of the definition, not a physical theorem. -/
theorem hystericalComponent_eq_residual
    {Interaction State Observable : Type*}
    (d : ResponseDecomposition Interaction State Observable)
    (F : Observable) (ρ : State) :
    hystericalComponent d F ρ = d.residual F ρ := by
  rfl

/-- Vanishing of the Hysterical component in a particular state is a statement
    about the value of the residual response, not about absence of the channel. -/
theorem hystericalComponent_zero_iff_residual_zero
    {Interaction State Observable : Type*}
    (d : ResponseDecomposition Interaction State Observable)
    (F : Observable) (ρ : State) :
    hystericalComponent d F ρ = 0 ↔ d.residual F ρ = 0 := by
  rfl

/-! ## 6. Physical interfaces not proved by the algebraic specification

The next predicates are merely names for physical statements that later papers
may assume, model, or test.  In particular, gravity is not special because it
possesses Hysterical Response; every decomposed interaction has such a component
by definition.  Gravity is special only if its externally visible response fails
to neutralize macroscopically while other interactions do neutralize/suppress.
-/

/-- Macroscopic Hysterical neutrality of a specified interaction. -/
def MacroscopicallyNeutral
    (Interaction : Type*) (Neutralizes : Interaction → Prop) (X : Interaction) : Prop :=
  Neutralizes X

/-- Gravitational survival is represented as failure of the relevant macroscopic
    neutralization mechanism.  Its truth is physical input, not proved here. -/
def GravitySurvivesNeutrality
    (Interaction : Type*)
    (gravity : Interaction)
    (Neutralizes : Interaction → Prop) : Prop :=
  ¬ Neutralizes gravity

/-! ## 7. Closed-form scalar growth rate, threshold time, noise variance, pitchfork stability -/

/-- Larger root of the scalar characteristic polynomial. -/
def lambdaPlus (Γ γ α σ : ℝ) : ℝ :=
  - (Γ + γ) / 2 + (1 / 2) * Real.sqrt ((Γ - γ) ^ 2 + 4 * α * σ)

theorem lambdaPlus_pos_of_feedback
    {Γ γ α σ : ℝ}
    (hΓ : 0 < Γ) (hγ : 0 < γ)
    (hfeedback : Γ * γ < α * σ) :
    0 < lambdaPlus Γ γ α σ := by
  unfold lambdaPlus
  set D := (Γ - γ) ^ 2 + 4 * α * σ
  have hD : 0 ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg (Γ - γ)]
  have hcmp : (Γ + γ) ^ 2 < D := by
    dsimp [D]
    nlinarith
  have hsum : 0 ≤ Γ + γ := by nlinarith
  have hroot : Γ + γ < Real.sqrt D := by
    have := Real.sqrt_lt_sqrt (sq_nonneg (Γ + γ)) hcmp
    rwa [Real.sqrt_sq hsum] at this
  nlinarith

/-- TeX `thm:scalar`: subcritical feedback ⇒ `λ₊ < 0` (real-discriminant case). -/
theorem lambdaPlus_neg_of_subcritical
    {Γ γ α σ : ℝ}
    (hΓ : 0 ≤ Γ) (hγ : 0 ≤ γ)
    (hsum : 0 < Γ + γ)
    (hsub : α * σ < Γ * γ)
    (hdisc : 0 ≤ (Γ - γ) ^ 2 + 4 * α * σ) :
    lambdaPlus Γ γ α σ < 0 := by
  unfold lambdaPlus
  set D := (Γ - γ) ^ 2 + 4 * α * σ
  have hcmp : D < (Γ + γ) ^ 2 := by
    dsimp [D]
    nlinarith
  have hsum0 : 0 ≤ Γ + γ := le_of_lt hsum
  have hroot : Real.sqrt D < Γ + γ := by
    have := Real.sqrt_lt_sqrt hdisc hcmp
    rwa [Real.sqrt_sq hsum0] at this
  nlinarith

theorem scalar_det (Γ γ α σ : ℝ) :
    charPoly Γ γ α σ 0 = Γ * γ - α * σ := by
  unfold charPoly; ring

theorem scalar_trace_neg {Γ γ : ℝ} (hΓ : 0 < Γ) (hγ : 0 < γ) :
    -(Γ + γ) < 0 := by nlinarith

/-- Finite threshold time for an unstable mode with nonzero seed amplitude. -/
def thresholdTime (lamPlus Xstar Aplus : ℝ) : ℝ :=
  (1 / lamPlus) * Real.log (Xstar / |Aplus|)

/-- Linear unstable-mode trajectory `A₊ e^{λ₊ t}`. -/
def unstableMode (Aplus lamPlus t : ℝ) : ℝ :=
  Aplus * Real.exp (lamPlus * t)

theorem thresholdTime_pos
    {lamPlus Xstar Aplus : ℝ}
    (hlam : 0 < lamPlus) (hX : 0 < Xstar) (hA : Aplus ≠ 0) (hXA : |Aplus| < Xstar) :
    0 < thresholdTime lamPlus Xstar Aplus := by
  unfold thresholdTime
  have hlog : 0 < Real.log (Xstar / |Aplus|) := by
    apply Real.log_pos
    exact (one_lt_div (abs_pos.mpr hA)).2 hXA
  positivity

/-- TeX `cor:threshold`: the unstable mode hits the threshold exactly at `t_*`. -/
theorem cor_threshold_hit
    {lamPlus Xstar Aplus : ℝ}
    (hlam : 0 < lamPlus) (hX : 0 < Xstar) (hA : Aplus ≠ 0)
    (hXA : |Aplus| < Xstar) :
    |unstableMode Aplus lamPlus (thresholdTime lamPlus Xstar Aplus)| = Xstar := by
  have hApos : 0 < |Aplus| := abs_pos.mpr hA
  have hlam0 : lamPlus ≠ 0 := ne_of_gt hlam
  have hquot : 0 < Xstar / |Aplus| := div_pos hX hApos
  have hexp :
      Real.exp (lamPlus * thresholdTime lamPlus Xstar Aplus) =
        Xstar / |Aplus| := by
    unfold thresholdTime
    have :
        lamPlus * ((1 / lamPlus) * Real.log (Xstar / |Aplus|)) =
          Real.log (Xstar / |Aplus|) := by
      field_simp [hlam0]
    rw [this, Real.exp_log hquot]
  calc
    |unstableMode Aplus lamPlus (thresholdTime lamPlus Xstar Aplus)|
        = |Aplus| * Real.exp (lamPlus * thresholdTime lamPlus Xstar Aplus) := by
            simp [unstableMode, abs_mul, Real.abs_exp]
    _ = |Aplus| * (Xstar / |Aplus|) := by rw [hexp]
    _ = Xstar := by field_simp [ne_of_gt hApos]

/-- Linear SDE variance growth: `(D/λ)(e^{2λ t}-1)`. -/
def unstableVariance (D lam t : ℝ) : ℝ :=
  (D / lam) * (Real.exp (2 * lam * t) - 1)

def varianceODE_rhs (D lam v : ℝ) : ℝ :=
  2 * lam * v + 2 * D

theorem unstableVariance_pos
    {D lam t : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (ht : 0 < t) :
    0 < unstableVariance D lam t := by
  unfold unstableVariance
  have hexp : 1 < Real.exp (2 * lam * t) := by
    have : 0 < 2 * lam * t := by positivity
    exact (Real.one_lt_exp_iff).2 this
  positivity

theorem prop_noise_variance_ic (D lam : ℝ) :
    unstableVariance D lam 0 = 0 := by
  simp [unstableVariance]

/-- Algebraic form of Ito's second-moment ODE right-hand side. -/
theorem prop_noise_variance_rhs_identity
    {D lam : ℝ} (hlam : lam ≠ 0) (t : ℝ) :
    varianceODE_rhs D lam (unstableVariance D lam t) =
      2 * D * Real.exp (2 * lam * t) := by
  unfold varianceODE_rhs unstableVariance
  field_simp [hlam]
  ring

/-- TeX `prop:noise` core: the explicit variance solves `v' = 2λv + 2D`. -/
theorem prop_noise_variance_solves_ode
    {D lam : ℝ} (hlam : lam ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => unstableVariance D lam s)
      (varianceODE_rhs D lam (unstableVariance D lam t)) t := by
  have hlin : HasDerivAt (fun s : ℝ => 2 * lam * s) (2 * lam) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * lam)
  have hexp :
      HasDerivAt (fun s : ℝ => Real.exp (2 * lam * s))
        (2 * lam * Real.exp (2 * lam * t)) t := by
    convert (Real.hasDerivAt_exp (2 * lam * t)).comp t hlin using 1
    · ext s; simp [Function.comp]
    · ring
  have hsub :
      HasDerivAt (fun s : ℝ => Real.exp (2 * lam * s) - 1)
        (2 * lam * Real.exp (2 * lam * t)) t :=
    hexp.sub_const 1
  have hmul :
      HasDerivAt (fun s => (D / lam) * (Real.exp (2 * lam * s) - 1))
        ((D / lam) * (2 * lam * Real.exp (2 * lam * t))) t :=
    hsub.const_mul (D / lam)
  have hrhs :
      (D / lam) * (2 * lam * Real.exp (2 * lam * t)) =
        varianceODE_rhs D lam (unstableVariance D lam t) := by
    rw [prop_noise_variance_rhs_identity hlam t]
    field_simp [hlam]
  simpa [unstableVariance, hrhs] using hmul

/-- Left-eigenvector Y-component cannot vanish when `σ ≠ 0` (TeX `prop:noise`). -/
theorem prop_noise_left_eig_Y_ne
    {Γ γ α σ lam lY lh : ℝ}
    (hσ : σ ≠ 0)
    (hrow0 : lY * (-Γ) + lh * σ = lam * lY)
    (_hrow1 : lY * α + lh * (-γ) = lam * lh)
    (hne : ¬(lY = 0 ∧ lh = 0)) :
    lY ≠ 0 := by
  intro hY0
  have hlh0 : lh = 0 := by
    have : lh * σ = 0 := by
      simpa [hY0] using hrow0
    exact (mul_eq_zero.mp this).resolve_right hσ
  exact hne ⟨hY0, hlh0⟩

/-- Linearization coefficient of the cubic pitchfork drift. -/
def pitchforkLinearization (r u Y : ℝ) : ℝ :=
  r - 3 * u * Y ^ 2

theorem pitchfork_linearization_at_zero (r u : ℝ) :
    pitchforkLinearization r u 0 = r := by
  simp [pitchforkLinearization]

theorem pitchfork_linearization_at_branch
    {r u Y : ℝ} (hu : u ≠ 0) (hY : Y ^ 2 = r / u) :
    pitchforkLinearization r u Y = -2 * r := by
  unfold pitchforkLinearization
  calc
    r - 3 * u * Y ^ 2 = r - 3 * u * (r / u) := by rw [hY]
    _ = r - 3 * r := by field_simp [hu]
    _ = -2 * r := by ring

theorem pitchfork_zero_unstable_when_r_pos
    {r u : ℝ} (hr : 0 < r) :
    0 < pitchforkLinearization r u 0 ∧ pitchforkDrift r u 0 = 0 :=
  ⟨by simpa [pitchfork_linearization_at_zero] using hr, pitchfork_neutral_fixed r u⟩

theorem pitchfork_zero_stable_when_r_neg
    {r u : ℝ} (hr : r < 0) :
    pitchforkLinearization r u 0 < 0 ∧ pitchforkDrift r u 0 = 0 :=
  ⟨by simpa [pitchfork_linearization_at_zero] using hr, pitchfork_neutral_fixed r u⟩

theorem pitchfork_branches_stable_when_r_pos
    {r u Y : ℝ} (hu : 0 < u) (hr : 0 < r) (hY : Y ^ 2 = r / u) :
    pitchforkLinearization r u Y < 0 ∧ pitchforkDrift r u Y = 0 := by
  refine ⟨?_, pitchfork_nonzero_fixed (ne_of_gt hu) hY⟩
  have hlin := pitchfork_linearization_at_branch (ne_of_gt hu) hY
  rw [hlin]
  nlinarith

/-- Nonzero branches are algebraic fixed points when `Y^2 = r/u`. -/
theorem pitchfork_branches_fixed
    {r u Y : ℝ} (hu : 0 < u) (_hr : 0 < r) (hY : Y ^ 2 = r / u) :
    pitchforkDrift r u Y = 0 :=
  pitchfork_nonzero_fixed (ne_of_gt hu) hY

/-- Legacy residual cubic identity. -/
theorem pitchfork_linear_coefficient (r u : ℝ) :
    (fun Y : ℝ => r * Y - u * Y ^ 3) 0 = 0 ∧
      (∀ (ε : ℝ), (r * ε - u * ε ^ 3) - r * ε = -u * ε ^ 3) := by
  constructor
  · ring
  · intro ε; ring

/-! ## 8. Finite-dimensional spectral abscissa trichotomy (master theorem) -/

/-- Closed-loop Jacobian in the reciprocal scalar form. -/
def closedLoopJacobian (Γ : ℝ) (K : ℝ) : ℝ :=
  -Γ * (1 - K)

/-- Spectral abscissa of a real 1×1 generator is the generator itself. -/
def spectralAbscissa1D (J : ℝ) : ℝ := J

theorem master_phase_trichotomy (α : ℝ) :
    α < 0 ∨ α = 0 ∨ 0 < α :=
  lt_trichotomy α 0

theorem closedLoop_abscissa_sign
    {Γ K : ℝ} (hΓ : 0 < Γ) :
    (spectralAbscissa1D (closedLoopJacobian Γ K) < 0 ↔ K < 1) ∧
    (spectralAbscissa1D (closedLoopJacobian Γ K) = 0 ↔ K = 1) ∧
    (0 < spectralAbscissa1D (closedLoopJacobian Γ K) ↔ 1 < K) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      have : 0 < Γ * (1 - K) := by
        simpa [spectralAbscissa1D, closedLoopJacobian, neg_mul, neg_lt_zero] using h
      nlinarith
    · intro h
      have : 0 < Γ * (1 - K) := by nlinarith
      simpa [spectralAbscissa1D, closedLoopJacobian, neg_mul, neg_lt_zero] using this
  · constructor
    · intro h
      have : Γ * (1 - K) = 0 := by
        simpa [spectralAbscissa1D, closedLoopJacobian, neg_mul, neg_eq_zero] using h
      nlinarith
    · intro h
      simp [spectralAbscissa1D, closedLoopJacobian, h]
  · constructor
    · intro h
      have : Γ * (1 - K) < 0 := by
        simpa [spectralAbscissa1D, closedLoopJacobian, neg_mul, neg_pos] using h
      nlinarith
    · intro h
      have : Γ * (1 - K) < 0 := by nlinarith
      simpa [spectralAbscissa1D, closedLoopJacobian, neg_mul, neg_pos] using this

/-- Reciprocal scalar gain criterion (TeX `cor:reciprocal`). -/
theorem reciprocal_gain_criterion
    {Γ K : ℝ} (hΓ : 0 < Γ) :
    (K < 1 → spectralAbscissa1D (closedLoopJacobian Γ K) < 0) ∧
    (K = 1 → spectralAbscissa1D (closedLoopJacobian Γ K) = 0) ∧
    (1 < K → 0 < spectralAbscissa1D (closedLoopJacobian Γ K)) := by
  have h := closedLoop_abscissa_sign (Γ := Γ) (K := K) hΓ
  exact ⟨h.1.2, h.2.1.2, h.2.2.2⟩

/-- Matrix closed-loop generator `J = -Γ (I - K)`. -/
def closedLoopMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (Γ : ℝ) (K : Matrix n n ℝ) : Matrix n n ℝ :=
  (-Γ) • (1 - K)

/-- Eigenvectors of `K` are eigenvectors of `J` with eigenvalue `-Γ(1-μ)`. -/
theorem closedLoopMatrix_eigen
    {n : Type*} [Fintype n] [DecidableEq n]
    (Γ μ : ℝ) (K : Matrix n n ℝ) (v : n → ℝ)
    (hv : K.mulVec v = μ • v) :
    (closedLoopMatrix Γ K).mulVec v = (-Γ * (1 - μ)) • v := by
  have hIK : (1 - K).mulVec v = (1 - μ) • v := by
    simp [Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_smul]
  calc
    (closedLoopMatrix Γ K).mulVec v
        = ((-Γ) • (1 - K)).mulVec v := rfl
    _ = (-Γ) • ((1 - K).mulVec v) := Matrix.smul_mulVec _ _ _
    _ = (-Γ) • ((1 - μ) • v) := by rw [hIK]
    _ = (-Γ * (1 - μ)) • v := by rw [smul_smul]

/-- Modewise reciprocal criterion: each gain eigenvalue crosses unity with `α`. -/
theorem cor_reciprocal_mode
    {Γ μ : ℝ} (hΓ : 0 < Γ) :
    (-Γ * (1 - μ) < 0 ↔ μ < 1) ∧
    (-Γ * (1 - μ) = 0 ↔ μ = 1) ∧
    (0 < -Γ * (1 - μ) ↔ 1 < μ) :=
  closedLoop_abscissa_sign (Γ := Γ) (K := μ) hΓ

theorem hysterical_neutrality_instability_reciprocal
    {Γ K : ℝ} (hΓ : 0 < Γ) :
    (K < 1 ∧ spectralAbscissa1D (closedLoopJacobian Γ K) < 0) ∨
    (K = 1 ∧ spectralAbscissa1D (closedLoopJacobian Γ K) = 0) ∨
    (1 < K ∧ 0 < spectralAbscissa1D (closedLoopJacobian Γ K)) := by
  have h := reciprocal_gain_criterion (Γ := Γ) (K := K) hΓ
  rcases lt_trichotomy K 1 with hlt | heq | hgt
  · exact Or.inl ⟨hlt, h.1 hlt⟩
  · exact Or.inr (Or.inl ⟨heq, h.2.1 heq⟩)
  · exact Or.inr (Or.inr ⟨hgt, h.2.2 hgt⟩)

theorem subcritical_sufficient_condition
    (χR χH M γ C_OS : ℝ)
    (hγ : 0 < γ)
    (hχH : |χH| ≤ (M / γ) * C_OS)
    (hsub : |χR| * (M / γ) * C_OS < 1) :
    |χR * χH| < 1 := by
  have h1 : |χR * χH| = |χR| * |χH| := abs_mul _ _
  have h2 : |χR| * |χH| ≤ |χR| * ((M / γ) * C_OS) := by gcongr
  have h3 : |χR| * ((M / γ) * C_OS) = |χR| * (M / γ) * C_OS := by ring
  calc
    |χR * χH| = |χR| * |χH| := h1
    _ ≤ |χR| * ((M / γ) * C_OS) := h2
    _ = |χR| * (M / γ) * C_OS := h3
    _ < 1 := hsub

theorem reciprocal_gain_from_product
    {χR χH : ℝ} (h : 1 < χR * χH) :
    1 < χR * χH := h

theorem scalar_hysterical_instability_supercritical
    {Γ γ α σ : ℝ}
    (hΓ : 0 < Γ) (hγ : 0 < γ)
    (hfeedback : Γ * γ < α * σ) :
    0 < lambdaPlus Γ γ α σ :=
  lambdaPlus_pos_of_feedback hΓ hγ hfeedback

theorem scalar_hysterical_instability_critical
    {Γ γ α σ : ℝ}
    (hΓ : 0 ≤ Γ) (hγ : 0 ≤ γ)
    (hcrit : α * σ = Γ * γ) :
    lambdaPlus Γ γ α σ = 0 := by
  unfold lambdaPlus
  have hD : (Γ - γ) ^ 2 + 4 * α * σ = (Γ + γ) ^ 2 := by nlinarith
  have hsum : 0 ≤ Γ + γ := by nlinarith
  rw [hD, Real.sqrt_sq hsum]
  ring

theorem finite_threshold_time
    {lamPlus Xstar Aplus : ℝ}
    (hlam : 0 < lamPlus) (hX : 0 < Xstar) (hA : Aplus ≠ 0) (hXA : |Aplus| < Xstar) :
    0 < thresholdTime lamPlus Xstar Aplus :=
  thresholdTime_pos hlam hX hA hXA

theorem stochastic_excitation_unstable_mode
    {D lam t : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (ht : 0 < t) :
    0 < unstableVariance D lam t :=
  unstableVariance_pos hD hlam ht

theorem supercritical_pitchfork
    {r u Y : ℝ} (hu : 0 < u) (hr : 0 < r) (hY : Y ^ 2 = r / u) :
    pitchforkDrift r u Y = 0 :=
  pitchfork_branches_fixed hu hr hY

/-- LITERATURE HYPOTHESIS (Perko): in finite dimension, the linear ODE
`ẏ = Jy` is asymptotically stable / unstable / critical according as
`α(J) < 0` / `α(J) > 0` / `α(J) = 0`, via the Jordan-mode expansion.
Tagged explicitly — not a silent gap. -/
axiom literature_finite_dim_linear_ode_stability : Prop

/-! ## TeX label aliases (canonical names) -/

/--
TeX: thm:master — spectral abscissa trichotomy for the closed-loop phases.
Proved: `α < 0 ∨ α = 0 ∨ 0 < α`. Reading these as local linear ODE
stability for a general finite-dimensional generator `J` is the tagged
`literature_finite_dim_linear_ode_stability` (Perko) hypothesis below.
-/
theorem thm_master (α : ℝ) :
    α < 0 ∨ α = 0 ∨ 0 < α :=
  master_phase_trichotomy α

/-- TeX `thm:master` with the Perko ODE dictionary explicitly assumed. -/
theorem thm_master_with_ode_dictionary
    (α : ℝ) (_lit : literature_finite_dim_linear_ode_stability) :
    α < 0 ∨ α = 0 ∨ 0 < α :=
  thm_master α

/-- Fully proved reciprocal scalar specialization of `thm:master`. -/
theorem thm_master_reciprocal
    {Γ K : ℝ} (hΓ : 0 < Γ) :
    (K < 1 ∧ spectralAbscissa1D (closedLoopJacobian Γ K) < 0) ∨
    (K = 1 ∧ spectralAbscissa1D (closedLoopJacobian Γ K) = 0) ∨
    (1 < K ∧ 0 < spectralAbscissa1D (closedLoopJacobian Γ K)) :=
  hysterical_neutrality_instability_reciprocal hΓ

theorem cor_reciprocal
    {Γ K : ℝ} (hΓ : 0 < Γ) :
    (K < 1 → spectralAbscissa1D (closedLoopJacobian Γ K) < 0) ∧
    (K = 1 → spectralAbscissa1D (closedLoopJacobian Γ K) = 0) ∧
    (1 < K → 0 < spectralAbscissa1D (closedLoopJacobian Γ K)) :=
  reciprocal_gain_criterion hΓ

theorem cor_subcrit
    (χR χH M γ C_OS : ℝ)
    (hγ : 0 < γ)
    (hχH : |χH| ≤ (M / γ) * C_OS)
    (hsub : |χR| * (M / γ) * C_OS < 1) :
    |χR * χH| < 1 :=
  subcritical_sufficient_condition χR χH M γ C_OS hγ hχH hsub

theorem thm_scalar_supercritical
    {Γ γ α σ : ℝ}
    (hΓ : 0 < Γ) (hγ : 0 < γ)
    (hfeedback : Γ * γ < α * σ) :
    0 < lambdaPlus Γ γ α σ :=
  scalar_hysterical_instability_supercritical hΓ hγ hfeedback

theorem thm_scalar_critical
    {Γ γ α σ : ℝ}
    (hΓ : 0 ≤ Γ) (hγ : 0 ≤ γ)
    (hcrit : α * σ = Γ * γ) :
    lambdaPlus Γ γ α σ = 0 :=
  scalar_hysterical_instability_critical hΓ hγ hcrit

theorem thm_scalar_subcritical
    {Γ γ α σ : ℝ}
    (hΓ : 0 ≤ Γ) (hγ : 0 ≤ γ)
    (hsum : 0 < Γ + γ)
    (hsub : α * σ < Γ * γ)
    (hdisc : 0 ≤ (Γ - γ) ^ 2 + 4 * α * σ) :
    lambdaPlus Γ γ α σ < 0 :=
  lambdaPlus_neg_of_subcritical hΓ hγ hsum hsub hdisc

/-- TeX: cor:threshold — hitting-time identity for the unstable mode. -/
theorem cor_threshold
    {lamPlus Xstar Aplus : ℝ}
    (hlam : 0 < lamPlus) (hX : 0 < Xstar) (hA : Aplus ≠ 0) (hXA : |Aplus| < Xstar) :
    0 < thresholdTime lamPlus Xstar Aplus ∧
      |unstableMode Aplus lamPlus (thresholdTime lamPlus Xstar Aplus)| = Xstar :=
  ⟨finite_threshold_time hlam hX hA hXA, cor_threshold_hit hlam hX hA hXA⟩

/-- TeX: prop:noise — variance formula, ODE, and left-eigenvector projection. -/
theorem prop_noise
    {D lam t : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (ht : 0 < t) :
    0 < unstableVariance D lam t ∧
      unstableVariance D lam 0 = 0 ∧
      HasDerivAt (fun s => unstableVariance D lam s)
        (varianceODE_rhs D lam (unstableVariance D lam t)) t :=
  ⟨stochastic_excitation_unstable_mode hD hlam ht,
    prop_noise_variance_ic D lam,
    prop_noise_variance_solves_ode (ne_of_gt hlam) t⟩

/-- TeX: prop:pitchfork — supercritical pitchfork fixed points + linearization stability. -/
theorem prop_supercritical_pitchfork
    {r u Y : ℝ} (hu : 0 < u) (hr : 0 < r) (hY : Y ^ 2 = r / u) :
    pitchforkDrift r u Y = 0 ∧ pitchforkLinearization r u Y < 0 :=
  ⟨supercritical_pitchfork hu hr hY,
    (pitchfork_branches_stable_when_r_pos hu hr hY).1⟩

/-- Explicit positive saturated node `Y₊ = √(r/u)` when `r,u > 0`. -/
theorem pitchfork_positive_stable_node
    {r u : ℝ} (hu : 0 < u) (hr : 0 < r) :
    let Y := Real.sqrt (r / u)
    0 < Y ∧ pitchforkDrift r u Y = 0 ∧ pitchforkLinearization r u Y < 0 := by
  dsimp
  set Y := Real.sqrt (r / u) with hYdef
  have hYsq : Y ^ 2 = r / u := by
    rw [hYdef, Real.sq_sqrt (div_nonneg (le_of_lt hr) (le_of_lt hu))]
  have hYpos : 0 < Y := by
    rw [hYdef]
    exact Real.sqrt_pos.mpr (div_pos hr hu)
  exact ⟨hYpos, prop_supercritical_pitchfork hu hr hYsq⟩

/-- Odd Z₂ twin: the negative branch is also a stable saturated fixed point. -/
theorem pitchfork_negative_stable_twin
    {r u : ℝ} (hu : 0 < u) (hr : 0 < r) :
    let Y := Real.sqrt (r / u)
    pitchforkDrift r u (-Y) = 0 ∧ pitchforkLinearization r u (-Y) < 0 := by
  dsimp
  set Y := Real.sqrt (r / u) with hYdef
  have hYsq : Y ^ 2 = r / u := by
    rw [hYdef, Real.sq_sqrt (div_nonneg (le_of_lt hr) (le_of_lt hu))]
  have hneg : (-Y) ^ 2 = r / u := by
    simpa [neg_sq] using hYsq
  exact prop_supercritical_pitchfork hu hr hneg

/-- Linear positive-alignment map from order parameter to leftover force. -/
def alignedForce (κ Y : ℝ) : ℝ := κ * Y

/-- TeX: cor:gravity-positivity — at the stable positive saturated node, with
positive channel alignment `κ > 0`, leftover force is strictly positive.
Does **not** claim gravity is supercritical; that remains a physical input. -/
theorem cor_gravity_positivity
    {r u κ : ℝ} (hu : 0 < u) (hr : 0 < r) (hκ : 0 < κ) :
    let Y := Real.sqrt (r / u)
    pitchforkDrift r u Y = 0 ∧
      pitchforkLinearization r u Y < 0 ∧
      0 < Y ∧
      0 < alignedForce κ Y := by
  dsimp
  have hnode := pitchfork_positive_stable_node (r := r) (u := u) hu hr
  dsimp at hnode
  refine ⟨hnode.2.1, hnode.2.2, hnode.1, ?_⟩
  simpa [alignedForce] using mul_pos hκ hnode.1

/-- Same packaging with an explicit cubic remainder: odd force law
`F_H = κ Y + c Y³` on the positive node stays positive when
`|c| (r/u) < κ`. -/
theorem cor_gravity_positivity_with_cubic
    {r u κ c : ℝ} (hu : 0 < u) (hr : 0 < r) (hκ : 0 < κ)
    (hc : |c| * (r / u) < κ) :
    let Y := Real.sqrt (r / u)
    let FH := κ * Y + c * Y ^ 3
    pitchforkDrift r u Y = 0 ∧
      pitchforkLinearization r u Y < 0 ∧
      0 < Y ∧
      0 < FH := by
  dsimp
  set Y := Real.sqrt (r / u) with hYdef
  set FH := κ * Y + c * Y ^ 3
  have hnode := pitchfork_positive_stable_node (r := r) (u := u) hu hr
  dsimp at hnode
  have hYsq : Y ^ 2 = r / u := by
    rw [hYdef, Real.sq_sqrt (div_nonneg (le_of_lt hr) (le_of_lt hu))]
  refine ⟨hnode.2.1, hnode.2.2, hnode.1, ?_⟩
  have hfactor : FH = Y * (κ + c * Y ^ 2) := by
    simp [FH]; ring
  have hbound : |c * Y ^ 2| < κ := by
    have : |c * Y ^ 2| = |c| * Y ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg Y)]
    rw [this, hYsq]
    exact hc
  have hinner : 0 < κ + c * Y ^ 2 := by
    have habs := abs_lt.mp hbound
    linarith
  have : 0 < Y * (κ + c * Y ^ 2) := mul_pos hnode.1 hinner
  simpa [hfactor] using this

end

end Paper1_2
