module

public import RequestProject.Euler.ContourCompactLinearFamilyIntegral
public import RequestProject.Euler.ContourHolderEvaluationNorm
public import RequestProject.Euler.ContourJointNormalizedChord
public import RequestProject.Euler.ContourSmoothSelfLog
public import RequestProject.Euler.ContourLogOperatorContinuity

/-! Genuine smooth dependence of the actual self-log integral at a
fixed base parameter on the Banach contour input. The integration
parameter is only Hölder continuous; no derivatives in it are used. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance] HolderFunctionSpace.complexScalarNormedSpace
  HolderFunctionSpace.complexScalarTower ContourC1Space.complexScalarNormedSpace
  ContourC1Space.complexScalarTower

variable {γ : ℝ≥0}

def contourSelfLogLinearFamily (hγ : 0 < (γ : ℝ)) (θ τ : ℝ) :
    ContourC1Space γ →L[ℝ] ℂ × ℂ :=
  let e := HolderFunctionSpace.eval γ (E := ℂ) ((θ : ContourCircle), contourClippedIncrement τ)
  (e.comp ((contourJointNormalizedChordCLM hγ).restrictScalars ℝ)).prod
    (e.comp ((contourJointDerivativeShiftCLM hγ).restrictScalars ℝ))

theorem continuous_contourSelfLogLinearFamily (hγ : 0 < (γ : ℝ)) (θ : ℝ) :
    Continuous (contourSelfLogLinearFamily hγ θ) := by
  have he : Continuous (fun τ : ℝ => HolderFunctionSpace.eval γ (E := ℂ)
      ((θ : ContourCircle), contourClippedIncrement τ)) :=
    (HolderFunctionSpace.continuous_eval_operator hγ).comp
      (continuous_const.prodMk continuous_contourClippedIncrement)
  have ha := he.clm_comp (continuous_const (y := (contourJointNormalizedChordCLM hγ).restrictScalars ℝ))
  have hn := he.clm_comp (continuous_const (y := (contourJointDerivativeShiftCLM hγ).restrictScalars ℝ))
  let C : ((ContourC1Space γ →L[ℝ] ℂ) × (ContourC1Space γ →L[ℝ] ℂ)) ≃ₗᵢ[ℝ]
      (ContourC1Space γ →L[ℝ] ℂ × ℂ) := ContinuousLinearMap.prodₗᵢ ℝ
  exact C.continuous.comp (ha.prodMk hn)

theorem contourSelfLogLinearFamily_coe (hγ : 0 < (γ : ℝ)) (θ τ : ℝ)
    (hτ : |τ| ≤ Real.pi) (Z : ContourC1Space γ) :
    contourSelfLogLinearFamily hγ θ τ Z =
      (-smoothContourNormalizedChord (ContourC1Space.lift γ Z) θ τ,
        deriv (ContourC1Space.lift γ Z) (θ + τ)) := by
  apply Prod.ext
  · change contourJointSample (contourJointNormalizedChordCLM hγ Z) (θ : ContourCircle) τ = _
    rw [contourJointSample_of_mem _ _ _ (abs_le.mp hτ), contourJointNormalizedChordCLM_coe]
  · change contourJointSample (contourJointDerivativeShiftCLM hγ Z) (θ : ContourCircle) τ = _
    rw [contourJointSample_of_mem _ _ _ (abs_le.mp hτ), contourJointDerivativeShiftCLM_apply]
    simp only [ContourC1Space.deriv_lift, AddCircle.coe_add]

def contourSelfLogFiniteKernel (q : ℂ × ℂ) : ℂ := Real.log ‖q.1‖ • q.2

theorem contDiffOn_contourSelfLogFiniteKernel :
    ContDiffOn ℝ ∞ contourSelfLogFiniteKernel {q : ℂ × ℂ | q.1 ≠ 0} := by
  intro q hq
  exact (((contDiffAt_fst.norm ℂ hq).log (norm_ne_zero_iff.mpr hq)).smul
    contDiffAt_snd).contDiffWithinAt

def contourSelfLogBasePresentation (hγ : 0 < (γ : ℝ)) (θ : ℝ) (Z : ContourC1Space γ) : ℂ :=
  (∫ τ in Icc (-Real.pi) Real.pi, Real.log τ • (contourSelfLogLinearFamily hγ θ τ Z).2) +
    ∫ τ in Icc (-Real.pi) Real.pi, contourSelfLogFiniteKernel (contourSelfLogLinearFamily hγ θ τ Z)

theorem contDiffOn_contourSelfLogBasePresentation (hγ : 0 < (γ : ℝ)) (θ : ℝ) :
    ContDiffOn ℝ ∞ (contourSelfLogBasePresentation hγ θ)
      {Z : ContourC1Space γ | ContourC1Space.HasPositiveChordArc Z} := by
  let S : Set ℝ := Icc (-Real.pi) Real.pi
  let U : Set (ContourC1Space γ) := {Z | ContourC1Space.HasPositiveChordArc Z}
  let W : Set (ℂ × ℂ) := {q | q.1 ≠ 0}
  have hU : IsOpen U := ContourC1Space.isOpen_hasPositiveChordArc γ
  have hW : IsOpen W := isOpen_compl_singleton.preimage continuous_fst
  have hL := (continuous_contourSelfLogLinearFamily hγ θ).continuousOn (s := S)
  have himage : ∀ Z ∈ U, ∀ τ ∈ S, contourSelfLogLinearFamily hγ θ τ Z ∈ W := by
    intro Z hZ τ hτ
    obtain ⟨c, hc, hZ⟩ := hZ
    rw [contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ)]
    change -smoothContourNormalizedChord (ContourC1Space.lift γ Z) θ τ ≠ 0
    exact neg_ne_zero.mpr (smoothContourNormalizedChord_ne_zero
      (ContourC1Space.contDiff_lift Z) hc hZ θ τ (abs_le.mpr hτ))
  have hab : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hw : IntegrableOn Real.log S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp intervalIntegral.intervalIntegrable_log'
  have hscale : ContDiffOn ℝ ∞ (fun Z : ContourC1Space γ =>
      ∫ τ in S, Real.log τ • (contourSelfLogLinearFamily hγ θ τ Z).2) U := by
    exact contDiffOn_weightedIntegral_compactLinearFamily isCompact_Icc hw hU isOpen_univ
      (contourSelfLogLinearFamily hγ θ) (fun _ => ContinuousLinearMap.id ℝ ℂ)
      (fun q : ℂ × ℂ => q.2) hL continuousOn_const contDiff_snd.contDiffOn
      (fun _ _ _ _ => mem_univ _)
  have hnormal : ContDiffOn ℝ ∞ (fun Z : ContourC1Space γ =>
      ∫ τ in S, contourSelfLogFiniteKernel (contourSelfLogLinearFamily hγ θ τ Z)) U := by
    simpa only [one_smul, ContinuousLinearMap.id_apply] using
      (contDiffOn_weightedIntegral_compactLinearFamily isCompact_Icc
        (w := fun _ : ℝ => 1) (integrableOn_const isCompact_Icc.measure_ne_top)
        hU hW (contourSelfLogLinearFamily hγ θ) (fun _ => ContinuousLinearMap.id ℝ ℂ)
        contourSelfLogFiniteKernel hL continuousOn_const contDiffOn_contourSelfLogFiniteKernel himage)
  exact hscale.add hnormal

theorem selfLogIntegral_eq_contourSelfLogBasePresentation (hγ : 0 < (γ : ℝ))
    (Z : ContourC1Space γ) {c : ℝ} (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (θ : ℝ) :
    ContourC1Space.selfLogIntegral Z θ = contourSelfLogBasePresentation hγ θ Z := by
  let S : Set ℝ := Icc (-Real.pi) Real.pi
  have hab : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hw : IntegrableOn Real.log S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp intervalIntegral.intervalIntegrable_log'
  have hd : Continuous (fun τ : ℝ => (contourSelfLogLinearFamily hγ θ τ Z).2) :=
    ((continuous_contourSelfLogLinearFamily hγ θ).clm_apply continuous_const).snd
  have hwi := integrableOn_smul_continuousOn_compact isCompact_Icc hw hd.continuousOn
  have hn : ContinuousOn (fun τ : ℝ =>
      contourSelfLogFiniteKernel (contourSelfLogLinearFamily hγ θ τ Z)) S := by
    apply contDiffOn_contourSelfLogFiniteKernel.continuousOn.comp
      ((continuous_contourSelfLogLinearFamily hγ θ).clm_apply continuous_const).continuousOn
    intro τ hτ
    change (contourSelfLogLinearFamily hγ θ τ Z).1 ≠ 0
    rw [contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ)]
    change -smoothContourNormalizedChord (ContourC1Space.lift γ Z) θ τ ≠ 0
    exact neg_ne_zero.mpr (smoothContourNormalizedChord_ne_zero
      (ContourC1Space.contDiff_lift Z) hc hZ θ τ (abs_le.mpr hτ))
  have hni : IntegrableOn (fun τ : ℝ =>
      contourSelfLogFiniteKernel (contourSelfLogLinearFamily hγ θ τ Z)) S :=
    ContinuousOn.integrableOn_compact isCompact_Icc hn
  rw [ContourC1Space.selfLogIntegral, contourSelfIntegral,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    contourSelfLogBasePresentation, ← integral_add hwi hni]
  apply integral_congr_ae
  have hn0 : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by
    rw [ae_iff]
    simp only [not_not, setOf_eq_eq_singleton, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn0] with τ hτ hne
  rw [contourSelfLogLinearFamily_coe hγ θ τ (abs_le.mpr hτ)]
  change contourLogIntegrand (ContourC1Space.lift γ Z) θ τ •
      deriv (ContourC1Space.lift γ Z) (θ + τ) = _
  rw [contourLogIntegrand_eq_log_add_normalized (ContourC1Space.contDiff_lift Z)
    hc hZ θ τ (abs_le.mpr hτ) hne, add_smul]
  simp only [contourSelfLogFiniteKernel, norm_neg]

/-- Genuine infinite input smoothness of the original scalar self-log
integral on the actual open positive-chord locus. -/
theorem contDiffOn_selfLogIntegral_fixed (hγ : 0 < (γ : ℝ)) (θ : ℝ) :
    ContDiffOn ℝ ∞ (fun Z : ContourC1Space γ => ContourC1Space.selfLogIntegral Z θ)
      {Z : ContourC1Space γ | ContourC1Space.HasPositiveChordArc Z} := by
  apply (contDiffOn_contourSelfLogBasePresentation hγ θ).congr
  intro Z hZ
  obtain ⟨c, hc, hZ⟩ := hZ
  exact selfLogIntegral_eq_contourSelfLogBasePresentation hγ Z hc hZ θ

theorem contDiffAt_selfLogIntegral_fixed (hγ : 0 < (γ : ℝ)) (θ : ℝ)
    (Z : ContourC1Space γ) (hZ : ContourC1Space.HasPositiveChordArc Z) :
    ContDiffAt ℝ ∞ (fun W : ContourC1Space γ => ContourC1Space.selfLogIntegral W θ) Z :=
  (contDiffOn_selfLogIntegral_fixed hγ θ Z hZ).contDiffAt
    ((ContourC1Space.isOpen_hasPositiveChordArc γ).mem_nhds hZ)

end Euler2D

end
