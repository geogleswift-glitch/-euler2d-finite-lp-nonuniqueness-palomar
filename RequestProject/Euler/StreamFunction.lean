module

public import RequestProject.Euler.Stationary
public import RequestProject.Euler.LagrangianTransport

/-!
# An explicit stream function for a smooth periodic divergence-free field

The primitive is the radial line integral of the closed one-form
`ψ₁ dx₀ - ψ₀ dx₁`.  Its two period increments determine an explicit constant
vector; subtracting the corresponding linear function gives a periodic
stream function.  No potential-existence hypothesis is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Euler2D

namespace StreamPotential

/-- Differentiation of a smooth scalar kernel under a fixed interval
integral.  Compactness supplies the local dominating derivative bound. -/
theorem hasFDerivAt_intervalIntegral {F : R2 → ℝ → ℝ}
    (hF : ContDiff ℝ 1 (Function.uncurry F)) (a b : ℝ) (x : R2) :
    HasFDerivAt (fun y => ∫ r in a..b, F y r)
      (∫ r in a..b, (fderiv ℝ (Function.uncurry F) (x, r)).comp
        (ContinuousLinearMap.inl ℝ R2 ℝ)) x := by
  let D : R2 → ℝ → R2 →L[ℝ] ℝ := fun y r =>
    (fderiv ℝ (Function.uncurry F) (y, r)).comp (ContinuousLinearMap.inl ℝ R2 ℝ)
  have hD : Continuous (Function.uncurry D) :=
    (hF.continuous_fderiv one_ne_zero).clm_comp continuous_const
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod
    (isCompact_uIcc : IsCompact (uIcc a b))).exists_bound_of_continuousOn hD.continuousOn
  have hdiff : ∀ r y, HasFDerivAt (fun z => F z r) (D y r) y := by
    intro r y
    exact (hF.differentiable one_ne_zero (y, r)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) y r)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s := Metric.ball x 1) (bound := fun _ => C) (Metric.ball_mem_nhds x zero_lt_one)
  · exact Filter.Eventually.of_forall fun y =>
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    intro y hy
    exact hC (y, r) ⟨Metric.ball_subset_closedBall hy, uIoc_subset_uIcc hr⟩
  · exact continuous_const.intervalIntegrable a b
  · exact Filter.Eventually.of_forall fun r y _ => hdiff r y

/-- The one-form whose potential has perpendicular gradient `ψ`. -/
def form (ψ : R2 → R2) (x : R2) : R2 →L[ℝ] ℝ :=
  (ψ x 1) • PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 -
    (ψ x 0) • PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1

theorem form_apply (ψ : R2 → R2) (x y : R2) :
    form ψ x y = ψ x 1 * y 0 - ψ x 0 * y 1 := rfl

theorem contDiff_form {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (form ψ) := by
  unfold form
  exact (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff.comp hψ).smul
    contDiff_const).sub
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff.comp hψ).smul
      contDiff_const)

theorem fderiv_form_apply {ψ : R2 → R2} (hψ : Differentiable ℝ ψ) (x a b : R2) :
    fderiv ℝ (form ψ) x a b =
      (fderiv ℝ ψ x a) 1 * b 0 - (fderiv ℝ ψ x a) 0 * b 1 := by
  have h₁ := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).hasFDerivAt.comp x
    (hψ x).hasFDerivAt
  have h₀ := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).hasFDerivAt.comp x
    (hψ x).hasFDerivAt
  have hform := (h₁.smul_const (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0)).sub
    (h₀.smul_const (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1))
  change HasFDerivAt (form ψ) _ x at hform
  rw [hform.fderiv]
  rfl

theorem fderiv_vector_apply_eq_pd (ψ : R2 → R2) (x a : R2) (j : Fin 2) :
    (fderiv ℝ ψ x a) j = a 0 * pd 0 ψ x j + a 1 * pd 1 ψ x j := by
  have ha : a = a 0 • EuclideanSpace.single 0 (1 : ℝ) +
      a 1 • EuclideanSpace.single 1 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [EuclideanSpace.single_apply]
  conv_lhs => rw [ha]
  simp [pd]

/-- Divergence-freeness is exactly the symmetry of the derivative of the
rotated one-form. -/
theorem fderiv_form_symmetric {ψ : R2 → R2} (hψ : Differentiable ℝ ψ)
    (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) (x a b : R2) :
    fderiv ℝ (form ψ) x a b = fderiv ℝ (form ψ) x b a := by
  rw [fderiv_form_apply hψ, fderiv_form_apply hψ]
  simp only [fderiv_vector_apply_eq_pd]
  have hd : pd 1 ψ x 1 = -pd 0 ψ x 0 := by linarith [hdiv x]
  rw [hd]
  ring

/-- The integrand of the explicit radial potential. -/
def radialIntegrand (ψ : R2 → R2) (x : R2) (r : ℝ) : ℝ := form ψ (r • x) x

/-- An explicit primitive on the plane, before removing its periods. -/
def raw (ψ : R2 → R2) (x : R2) : ℝ := ∫ r in (0 : ℝ)..1, radialIntegrand ψ x r

theorem contDiff_radialIntegrand {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (Function.uncurry (radialIntegrand ψ)) := by
  exact ((contDiff_form hψ).comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_fst

/-- The radial derivative, as a continuous linear functional in the
spatial increment. -/
def radialDerivative (ψ : R2 → R2) (x : R2) (r : ℝ) : R2 →L[ℝ] ℝ :=
  form ψ (r • x) + r • fderiv ℝ (form ψ) (r • x) x

theorem hasFDerivAt_radialIntegrand {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) (x : R2) (r : ℝ) :
    HasFDerivAt (fun y => radialIntegrand ψ y r) (radialDerivative ψ x r) x := by
  have hS := (contDiff_form hψ).differentiable (by simp)
  have hscl : HasFDerivAt (fun y : R2 => r • y) (r • ContinuousLinearMap.id ℝ R2) x :=
    (hasFDerivAt_id x).const_smul r
  have hcomp := (hS (r • x)).hasFDerivAt.comp x hscl
  convert hcomp.clm_apply (hasFDerivAt_id x) using 1 <;>
    (try simp only [radialIntegrand, Function.comp_apply, id_eq])
  ext y
  symm
  change form ψ (r • x) y + fderiv ℝ (form ψ) (r • x) (r • y) x =
    form ψ (r • x) y + r * fderiv ℝ (form ψ) (r • x) x y
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_form_symmetric (hψ.differentiable (by simp)) hdiv]

theorem hasDerivAt_radial_form {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    (x : R2) (r : ℝ) :
    HasDerivAt (fun s : ℝ => s • form ψ (s • x)) (radialDerivative ψ x r) r := by
  have hline : HasDerivAt (fun s : ℝ => s • x) x r :=
    by simpa using (hasDerivAt_id r).smul_const x
  have hS := ((contDiff_form hψ).differentiable (by simp) (r • x)).hasFDerivAt.comp_hasDerivAt r hline
  simpa only [radialDerivative, Pi.smul_def', Function.comp_def, id_eq, one_smul, add_comm]
    using (hasDerivAt_id r).smul hS

theorem integral_radialDerivative {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ) (x : R2) :
    (∫ r in (0 : ℝ)..1, radialDerivative ψ x r) = form ψ x := by
  have hscl : Continuous (fun r : ℝ => r • x) := continuous_id.smul continuous_const
  have hD : Continuous (fun r : ℝ => fderiv ℝ (form ψ) (r • x) x) :=
    (((contDiff_form hψ).continuous_fderiv (by simp)).comp hscl).clm_apply continuous_const
  have hc : Continuous (radialDerivative ψ x) :=
    ((contDiff_form hψ).continuous.comp hscl).add (continuous_id.smul hD)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_radial_form hψ x r) (hc.intervalIntegrable 0 1)
  simpa only [one_smul, zero_smul, sub_zero] using hftc

theorem hasFDerivAt_raw {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) (x : R2) :
    HasFDerivAt (raw ψ) (form ψ x) x := by
  have hF : ContDiff ℝ 1 (Function.uncurry (radialIntegrand ψ)) :=
    (contDiff_radialIntegrand hψ).of_le (by simp)
  have hcoef : ∀ r : ℝ,
      (fderiv ℝ (Function.uncurry (radialIntegrand ψ)) (x, r)).comp
        (ContinuousLinearMap.inl ℝ R2 ℝ) = radialDerivative ψ x r := by
    intro r
    have hpartial := (hF.differentiable one_ne_zero (x, r)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) x r)
    exact hpartial.unique (hasFDerivAt_radialIntegrand hψ hdiv x r)
  have hdiff := hasFDerivAt_intervalIntegral hF 0 1 x
  have heq : (∫ r in (0 : ℝ)..1,
      (fderiv ℝ (Function.uncurry (radialIntegrand ψ)) (x, r)).comp
        (ContinuousLinearMap.inl ℝ R2 ℝ)) = form ψ x := by
    simp_rw [hcoef]
    exact integral_radialDerivative hψ x
  rw [heq] at hdiff
  exact hdiff

theorem contDiff_raw {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) : ContDiff ℝ ∞ (raw ψ) := by
  apply contDiff_infty_iff_fderiv.mpr
  refine ⟨fun x => (hasFDerivAt_raw hψ hdiv x).differentiableAt, ?_⟩
  have heq : fderiv ℝ (raw ψ) = form ψ :=
    funext fun x => (hasFDerivAt_raw hψ hdiv x).fderiv
  rw [heq]
  exact contDiff_form hψ

theorem raw_zero (ψ : R2 → R2) : raw ψ 0 = 0 := by
  simp [raw, radialIntegrand, form_apply]

theorem smul_single (r a : ℝ) (i : Fin 2) :
    r • EuclideanSpace.single i a = EuclideanSpace.single i (r * a) := by
  ext j
  simp [EuclideanSpace.single_apply]

/-- On a coordinate axis the radial primitive is the usual line integral. -/
theorem raw_single_zero (ψ : R2 → R2) (a : ℝ) :
    raw ψ (EuclideanSpace.single 0 a) =
      ∫ s in (0 : ℝ)..a, ψ (EuclideanSpace.single 0 s) 1 := by
  have hfun : radialIntegrand ψ (EuclideanSpace.single 0 a) =
      fun r => a * ψ (EuclideanSpace.single 0 (r * a)) 1 := by
    funext r
    rw [radialIntegrand, form_apply, smul_single]
    simp [EuclideanSpace.single_apply]
    ring
  rw [raw, hfun, intervalIntegral.integral_const_mul]
  simpa only [smul_eq_mul, zero_mul, one_mul] using
    (intervalIntegral.smul_integral_comp_mul_right
      (a := (0 : ℝ)) (b := (1 : ℝ)) (fun s => ψ (EuclideanSpace.single 0 s) 1) a)

theorem raw_single_one (ψ : R2 → R2) (a : ℝ) :
    raw ψ (EuclideanSpace.single 1 a) =
      -(∫ s in (0 : ℝ)..a, ψ (EuclideanSpace.single 1 s) 0) := by
  have hfun : radialIntegrand ψ (EuclideanSpace.single 1 a) =
      fun r => -(a * ψ (EuclideanSpace.single 1 (r * a)) 0) := by
    funext r
    rw [radialIntegrand, form_apply, smul_single]
    simp [EuclideanSpace.single_apply]
    ring
  rw [raw, hfun, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  congr 1
  simpa only [smul_eq_mul, zero_mul, one_mul] using
    (intervalIntegral.smul_integral_comp_mul_right
      (a := (0 : ℝ)) (b := (1 : ℝ)) (fun s => ψ (EuclideanSpace.single 1 s) 0) a)

/-- The increment of the plane primitive over a period is independent of
the base point, since its derivative is the periodic one-form. -/
theorem raw_period_increment {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0)
    (hp : IsTorusPeriodic ψ) (i : Fin 2) (x : R2) :
    raw ψ (x + EuclideanSpace.single i (2 * Real.pi)) - raw ψ x =
      raw ψ (EuclideanSpace.single i (2 * Real.pi)) := by
  let a : R2 := EuclideanSpace.single i (2 * Real.pi)
  have hd : ∀ y : R2, HasFDerivAt (𝕜 := ℝ)
      (fun z : R2 => raw ψ (z + a) - raw ψ z) 0 y := by
    intro y
    have hshift := (hasFDerivAt_raw hψ hdiv (y + a)).comp y
      ((hasFDerivAt_id y).add_const a)
    have hsub := hshift.sub (hasFDerivAt_raw hψ hdiv y)
    have hper : form ψ (y + a) = form ψ y := by
      unfold form a
      rw [hp y i]
    simpa only [Function.comp_def, Pi.sub_def, id_eq,
      ContinuousLinearMap.comp_id, hper, sub_self] using hsub
  have hconst := is_const_of_fderiv_eq_zero (𝕜 := ℝ)
    (fun y => (hd y).differentiableAt) (fun y => (hd y).fderiv) x 0
  simpa only [zero_add, raw_zero, sub_zero] using hconst

/-- The linear functional with the two periods of the plane primitive. -/
def periodCorrection (ψ : R2 → R2) : R2 →L[ℝ] ℝ :=
  (raw ψ (EuclideanSpace.single 0 (2 * Real.pi)) / (2 * Real.pi)) •
      PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 +
    (raw ψ (EuclideanSpace.single 1 (2 * Real.pi)) / (2 * Real.pi)) •
      PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1

theorem periodCorrection_single (ψ : R2 → R2) (i : Fin 2) :
    periodCorrection ψ (EuclideanSpace.single i (2 * Real.pi)) =
      raw ψ (EuclideanSpace.single i (2 * Real.pi)) := by
  have hL : (2 * Real.pi) ≠ 0 := by positivity
  fin_cases i <;> simp [periodCorrection, EuclideanSpace.single_apply, div_mul_cancel₀ _ hL]

end StreamPotential

/-- The constant harmonic part of a smooth divergence-free torus field,
computed explicitly from the two periods of its radial primitive. -/
def streamConstant (ψ : R2 → R2) : R2 :=
  torusVec (-(StreamPotential.raw ψ (EuclideanSpace.single 1 (2 * Real.pi)) / (2 * Real.pi)))
    (StreamPotential.raw ψ (EuclideanSpace.single 0 (2 * Real.pi)) / (2 * Real.pi))

/-- The explicitly chosen constant is exactly the two transverse line
averages on the period-`2π` torus. -/
theorem streamConstant_eq_lineAverages (ψ : R2 → R2) :
    streamConstant ψ = torusVec
      ((∫ s in (0 : ℝ)..(2 * Real.pi), ψ (EuclideanSpace.single 1 s) 0) / (2 * Real.pi))
      ((∫ s in (0 : ℝ)..(2 * Real.pi), ψ (EuclideanSpace.single 0 s) 1) / (2 * Real.pi)) := by
  rw [streamConstant, StreamPotential.raw_single_zero, StreamPotential.raw_single_one]
  simp only [neg_div, neg_neg]

/-- The explicitly constructed periodic stream function. -/
def streamFunction (ψ : R2 → R2) (x : R2) : ℝ :=
  StreamPotential.raw ψ x - StreamPotential.periodCorrection ψ x

theorem contDiff_streamFunction {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) : ContDiff ℝ ∞ (streamFunction ψ) :=
  (StreamPotential.contDiff_raw hψ hdiv).sub (StreamPotential.periodCorrection ψ).contDiff

theorem isTorusPeriodic_streamFunction {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0)
    (hp : IsTorusPeriodic ψ) : IsTorusPeriodic (streamFunction ψ) := by
  intro x i
  have hinc := StreamPotential.raw_period_increment hψ hdiv hp i x
  change StreamPotential.raw ψ (x + EuclideanSpace.single i (2 * Real.pi)) -
      StreamPotential.periodCorrection ψ (x + EuclideanSpace.single i (2 * Real.pi)) =
    StreamPotential.raw ψ x - StreamPotential.periodCorrection ψ x
  rw [map_add, StreamPotential.periodCorrection_single]
  linarith

theorem hasFDerivAt_streamFunction {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) (x : R2) :
    HasFDerivAt (streamFunction ψ)
      (StreamPotential.form ψ x - StreamPotential.periodCorrection ψ) x :=
  (StreamPotential.hasFDerivAt_raw hψ hdiv x).sub
    (StreamPotential.periodCorrection ψ).hasFDerivAt

theorem pd_streamFunction_zero {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) (x : R2) :
    pd 0 (streamFunction ψ) x = ψ x 1 - streamConstant ψ 1 := by
  rw [pd, (hasFDerivAt_streamFunction hψ hdiv x).fderiv]
  simp [StreamPotential.form, StreamPotential.periodCorrection, streamConstant,
    EuclideanSpace.single_apply]

theorem pd_streamFunction_one {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) (x : R2) :
    pd 1 (streamFunction ψ) x = streamConstant ψ 0 - ψ x 0 := by
  rw [pd, (hasFDerivAt_streamFunction hψ hdiv x).fderiv]
  simp [StreamPotential.form, StreamPotential.periodCorrection, streamConstant,
    EuclideanSpace.single_apply]
  ring

/-- Every actual smooth periodic pointwise divergence-free field is its
explicit constant part plus the perpendicular gradient of its explicit
smooth periodic stream function. -/
theorem smooth_periodic_divFree_stream {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    (hp : IsTorusPeriodic ψ) (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) :
    IsScalarTest (streamFunction ψ) ∧ ∀ x, ψ x = streamConstant ψ +
      torusVec (-pd 1 (streamFunction ψ) x) (pd 0 (streamFunction ψ) x) := by
  refine ⟨⟨contDiff_streamFunction hψ hdiv, isTorusPeriodic_streamFunction hψ hdiv hp⟩, ?_⟩
  intro x
  have h₀ := pd_streamFunction_zero hψ hdiv x
  have h₁ := pd_streamFunction_one hψ hdiv x
  ext i
  fin_cases i
  · change ψ x 0 = streamConstant ψ 0 + -pd 1 (streamFunction ψ) x
    linarith
  · change ψ x 1 = streamConstant ψ 1 + pd 0 (streamFunction ψ) x
    linarith

theorem exists_smooth_periodic_stream {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    (hp : IsTorusPeriodic ψ) (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) :
    ∃ (c : R2) (χ : R2 → ℝ), IsScalarTest χ ∧
      ∀ x, ψ x = c + torusVec (-pd 1 χ x) (pd 0 χ x) :=
  ⟨streamConstant ψ, streamFunction ψ, smooth_periodic_divFree_stream hψ hp hdiv⟩

namespace StreamPotential

section ParametricSmoothness

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- The Banach-valued version of differentiation under the compact-interval
integral, needed when successively differentiating the time-parameterized
stream construction. -/
theorem hasFDerivAt_intervalIntegral_banach {F : E → ℝ → G}
    (hF : ContDiff ℝ 1 (Function.uncurry F)) (a b : ℝ) (x : E) :
    HasFDerivAt (fun y => ∫ r in a..b, F y r)
      (∫ r in a..b, (fderiv ℝ (Function.uncurry F) (x, r)).comp
        (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let D : E → ℝ → E →L[ℝ] G := fun y r =>
    (fderiv ℝ (Function.uncurry F) (y, r)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous (Function.uncurry D) :=
    (hF.continuous_fderiv one_ne_zero).clm_comp continuous_const
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod
    (isCompact_uIcc : IsCompact (uIcc a b))).exists_bound_of_continuousOn hD.continuousOn
  have hdiff : ∀ r y, HasFDerivAt (fun z => F z r) (D y r) y := by
    intro r y
    exact (hF.differentiable one_ne_zero (y, r)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) y r)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s := Metric.ball x 1) (bound := fun _ => C) (Metric.ball_mem_nhds x zero_lt_one)
  · exact Filter.Eventually.of_forall fun y =>
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    intro y hy
    exact hC (y, r) ⟨Metric.ball_subset_closedBall hy, uIoc_subset_uIcc hr⟩
  · exact continuous_const.intervalIntegrable a b
  · exact Filter.Eventually.of_forall fun r y _ => hdiff r y

omit [NormedSpace ℝ E] [CompleteSpace G] in
theorem continuous_intervalIntegral {F : E → ℝ → G}
    (hF : Continuous (Function.uncurry F)) (a b : ℝ) :
    Continuous (fun y => ∫ r in a..b, F y r) := by
  rcases le_total a b with hab | hba
  · simp only [intervalIntegral.integral_of_le hab]
    simp_rw [← integral_Icc_eq_integral_Ioc]
    exact continuous_parametric_integral_of_continuous hF isCompact_Icc
  · simp only [intervalIntegral.integral_of_ge hba]
    apply Continuous.neg
    simp_rw [← integral_Icc_eq_integral_Ioc]
    exact continuous_parametric_integral_of_continuous hF isCompact_Icc

end ParametricSmoothness

/-- Compact-interval integration preserves every finite order of joint
smoothness.  The induction ranges over Banach outputs, so it can be applied
to the operator-valued derivative at the successor step. -/
theorem contDiff_intervalIntegral_nat
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] (n : ℕ) :
    ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {F : E → ℝ → G}, ContDiff ℝ n (Function.uncurry F) →
      ∀ a b : ℝ, ContDiff ℝ n (fun y => ∫ r in a..b, F y r) := by
  induction n with
  | zero =>
    intro G _ _ _ F hF a b
    exact contDiff_zero.mpr (continuous_intervalIntegral hF.continuous a b)
  | succ n ih =>
    intro G _ _ _ F hF a b
    let D : E → ℝ → E →L[ℝ] G := fun y r =>
      (fderiv ℝ (Function.uncurry F) (y, r)).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hF1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by norm_cast; omega)
    have hD : ContDiff ℝ n (Function.uncurry D) :=
      (hF.fderiv_right (by simp)).clm_comp contDiff_const
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨fun y => ∫ r in a..b, D y r, ih hD a b,
      fun y => hasFDerivAt_intervalIntegral_banach hF1 a b y⟩

/-- Compact-interval integration preserves `C∞` joint smoothness. -/
theorem contDiff_intervalIntegral
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E → ℝ → G} (hF : ContDiff ℝ ∞ (Function.uncurry F)) (a b : ℝ) :
    ContDiff ℝ ∞ (fun y => ∫ r in a..b, F y r) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n hn
  exact contDiff_intervalIntegral_nat n (hF.of_le (by exact_mod_cast hn)) a b

/-- The explicit primitive is jointly smooth in a smooth time parameter
and the spatial point. -/
theorem contDiff_raw_family {φ : ℝ → R2 → R2}
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ)) :
    ContDiff ℝ ∞ (fun p : ℝ × R2 => raw (φ p.1) p.2) := by
  let F : (ℝ × R2) → ℝ → ℝ := fun p r => radialIntegrand (φ p.1) p.2 r
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    change ContDiff ℝ ∞ (fun p : (ℝ × R2) × ℝ =>
      φ p.1.1 (p.2 • p.1.2) 1 * p.1.2 0 -
        φ p.1.1 (p.2 • p.1.2) 0 * p.1.2 1)
    fun_prop
  exact contDiff_intervalIntegral hF 0 1

@[simp] theorem raw_zero_field (x : R2) : raw (0 : R2 → R2) x = 0 := by
  simp [raw, radialIntegrand, form_apply]

end StreamPotential

/-- The stream construction preserves joint time/space smoothness. -/
theorem contDiff_streamFunction_family {φ : ℝ → R2 → R2}
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ)) :
    ContDiff ℝ ∞ (Function.uncurry (fun t => streamFunction (φ t))) := by
  have hraw := StreamPotential.contDiff_raw_family hφ
  have hA₀ : ContDiff ℝ ∞ (fun p : ℝ × R2 =>
      StreamPotential.raw (φ p.1) (EuclideanSpace.single 0 (2 * Real.pi))) :=
    hraw.comp (contDiff_fst.prodMk contDiff_const)
  have hA₁ : ContDiff ℝ ∞ (fun p : ℝ × R2 =>
      StreamPotential.raw (φ p.1) (EuclideanSpace.single 1 (2 * Real.pi))) :=
    hraw.comp (contDiff_fst.prodMk contDiff_const)
  have hx₀ : ContDiff ℝ ∞ (fun p : ℝ × R2 => p.2 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff.comp contDiff_snd
  have hx₁ : ContDiff ℝ ∞ (fun p : ℝ × R2 => p.2 1) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff.comp contDiff_snd
  change ContDiff ℝ ∞ (fun p : ℝ × R2 => StreamPotential.raw (φ p.1) p.2 -
    (StreamPotential.raw (φ p.1) (EuclideanSpace.single 0 (2 * Real.pi)) /
      (2 * Real.pi) * p.2 0 +
    StreamPotential.raw (φ p.1) (EuclideanSpace.single 1 (2 * Real.pi)) /
      (2 * Real.pi) * p.2 1))
  exact hraw.sub (((hA₀.div_const _).mul hx₀).add ((hA₁.div_const _).mul hx₁))

/-- The harmonic constant is a smooth function of a smooth time parameter. -/
theorem contDiff_streamConstant_family {φ : ℝ → R2 → R2}
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ)) :
    ContDiff ℝ ∞ (fun t => streamConstant (φ t)) := by
  have hraw := StreamPotential.contDiff_raw_family hφ
  have hA₀ : ContDiff ℝ ∞ (fun t : ℝ =>
      StreamPotential.raw (φ t) (EuclideanSpace.single 0 (2 * Real.pi))) :=
    hraw.comp (contDiff_id.prodMk contDiff_const)
  have hA₁ : ContDiff ℝ ∞ (fun t : ℝ =>
      StreamPotential.raw (φ t) (EuclideanSpace.single 1 (2 * Real.pi))) :=
    hraw.comp (contDiff_id.prodMk contDiff_const)
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun t => -(StreamPotential.raw (φ t)
      (EuclideanSpace.single 1 (2 * Real.pi)) / (2 * Real.pi)))
    exact (hA₁.div_const _).neg
  · change ContDiff ℝ ∞ (fun t => StreamPotential.raw (φ t)
      (EuclideanSpace.single 0 (2 * Real.pi)) / (2 * Real.pi))
    exact hA₀.div_const _

@[simp] theorem streamFunction_zero (x : R2) : streamFunction (0 : R2 → R2) x = 0 := by
  simp [streamFunction, StreamPotential.periodCorrection]

@[simp] theorem streamConstant_zero : streamConstant (0 : R2 → R2) = 0 := by
  ext i
  fin_cases i <;> simp [streamConstant]

/-- An actual Euler test vector field produces an actual scalar vorticity
test, with the same terminal time support. -/
theorem eulerTest_streamFunction {T : ℝ} {φ : ℝ → R2 → R2} (hφ : IsEulerTest T φ) :
    IsVorticityTest T (fun t => streamFunction (φ t)) := by
  have hslice : ∀ t, ContDiff ℝ ∞ (φ t) := fun t =>
    hφ.smooth.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨contDiff_streamFunction_family hφ.smooth, ?_, ?_⟩
  · intro t
    exact isTorusPeriodic_streamFunction (hslice t) (hφ.divFree t) (hφ.periodic t)
  · obtain ⟨T', hT', hsupp⟩ := hφ.support
    refine ⟨T', hT', ?_⟩
    intro t ht x
    have heq : φ t = (0 : R2 → R2) := funext fun y => hsupp t ht y
    rw [heq, streamFunction_zero]

theorem eulerTest_streamConstant_support {T : ℝ} {φ : ℝ → R2 → R2}
    (hφ : IsEulerTest T φ) :
    ∃ T' < T, ∀ t ≥ T', streamConstant (φ t) = 0 := by
  obtain ⟨T', hT', hsupp⟩ := hφ.support
  refine ⟨T', hT', ?_⟩
  intro t ht
  have heq : φ t = (0 : R2 → R2) := funext fun y => hsupp t ht y
  rw [heq, streamConstant_zero]

/-- The complete time-dependent decomposition of an actual Euler test:
a jointly smooth scalar vorticity test and a smooth time-dependent
constant vector, both vanishing near the terminal time. -/
theorem eulerTest_stream_decomposition {T : ℝ} {φ : ℝ → R2 → R2}
    (hφ : IsEulerTest T φ) :
    IsVorticityTest T (fun t => streamFunction (φ t)) ∧
    ContDiff ℝ ∞ (fun t => streamConstant (φ t)) ∧
    (∃ T' < T, ∀ t ≥ T', streamConstant (φ t) = 0) ∧
    ∀ t x, φ t x = streamConstant (φ t) +
      torusVec (-pd 1 (streamFunction (φ t)) x) (pd 0 (streamFunction (φ t)) x) := by
  refine ⟨eulerTest_streamFunction hφ, contDiff_streamConstant_family hφ.smooth,
    eulerTest_streamConstant_support hφ, ?_⟩
  intro t
  have hslice : ContDiff ℝ ∞ (φ t) := hφ.smooth.comp (contDiff_const.prodMk contDiff_id)
  exact (smooth_periodic_divFree_stream hslice (hφ.periodic t) (hφ.divFree t)).2

end Euler2D

end
