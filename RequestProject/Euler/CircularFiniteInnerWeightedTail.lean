module

public import RequestProject.Euler.CircularFiniteInnerPointwiseForcing
public import RequestProject.Euler.WeightedPolynomialForcingBudget
public import RequestProject.Euler.CircularRigidRotationGauge
public import RequestProject.Euler.ActualTorusContourSourceContinuity

/-! The same-S complete inner forcing on an actual finite target
path has the original weighted polynomial tail. The original stage
gauge is evaluated at its absolute shifted time, not restarted. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

def actualInnerPolynomialForcingCoefficient (η b Cb e L : ℝ) : ℝ :=
  (2 / b) * (finiteLabelMassBound * cauchyContourNormBudget 5 η 1 e L) * Cb ^ 4

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualInner_weighted_tail {b Cw : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hCw : 0 ≤ Cw) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {s A₀ R ρ q T c d δ D : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρhalf : ρ ≤ b / 2)
        (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hsmall : ρ ^ 2 < b) (hhalf : ρ ^ 2 ≤ b / 2)
        (houter : b * ρ ^ 2 < 1) (hc : 0 < c) (hd : 0 < d) (hd16 : d * R ≤ 1 / 16)
        (hδ : 0 ≤ δ) (hD : 0 ≤ D),
      b * finiteEulerUniformRadialCoefficient K b R ρ c d δ * (radialStageRadiusConstant C Cw b) ^ 3 *
        ρ ^ 2 * (1 + D) ^ 3 ≤ C / 2 →
      radialStageRadiusConstant C Cw b * ρ * (1 + D) ≤ c / 2 →
      radialStageRadiusConstant C Cw b * ρ * (1 + D) ≤ d →
      ∀ (N k : ℕ) (hk : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ {a H : ℝ}, 0 ≤ a → a ≤ H → H ≤ T →
      H - a ≤ D / ((1 - b) * ampScale A₀ b k) →
      (∀ t ∈ Icc a H, ∀ y ∈ torusBox, d * R < ‖y - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t y = 0) →
      (∀ t ∈ Icc a H, P.FiniteOuterMaterialTube s R ρ N k S t c δ) →
      (∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward a y - torusCenter‖ ≤ Cw * ρ * radScale R ρ k) →
      ∀ (η : ℝ≥0), (η : ℝ) ≤ 1 → ∀ {e L σ lower upper Ω τ₀ : ℝ}, 0 < e → 0 < σ →
      8 * (radialStageRadiusConstant C Cw b * ρ * (1 + D)) ≤ e →
      0 ≤ lower → upper ≤ ampScale A₀ b k * (H - a) →
      ∀ (Z Q : ℝ → Fin 2 → LittleContourSpace η), ContinuousOn Q (Icc lower upper) →
      (∀ u ∈ Icc lower upper, ∀ i x,
        e * radScale R ρ k ≤ ‖ContourC1Space.toBCF η (Z u i).val x‖) →
      (∀ u ∈ Icc lower upper, ∀ i, ‖Z u i‖ ≤ radScale R ρ k * L) →
      (∀ u ∈ Icc lower upper, ∀ i θ, LittleContourSpace.lift η (Q u i) θ =
        velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S
          (a + u / ampScale A₀ b k)) (LittleContourSpace.lift η (Z u i) θ)) →
      let p := fun u => rigidRotationGauge Ω 0 (τ₀ + u) •
        ((ampScale A₀ b k * radScale R ρ k)⁻¹ • Q u)
      (∫ u in Icc lower upper, Real.exp (-σ * u) * ‖p u‖) ≤
        actualInnerPolynomialForcingCoefficient (η : ℝ) b (radialStageRadiusConstant C Cw b) e L *
          ρ ^ 6 * polynomialForcingTail σ lower := by
  obtain ⟨C, K, hC, hK, hpoint⟩ := P.exists_uniform_actualInner_pointwise_contourLittle hb hb1 hCw
  refine ⟨C, K, hC, hK, ?_⟩
  intro s A₀ R ρ q T c d δ D _ hs hA hR hRmax hρ hρ1 hρhalf hq hqE hsmall hhalf houter
    hc hd hd16 hδ hD hsmallDim hcoreDim hchartDim N k hk S hS a H ha haH hHT htime hglobal G hstart
    η hη e L σ lower upper Ω τ₀ he hσ hsep hlower hupper Z Q hQc hZ hL hQ
  let A := ampScale A₀ b k
  let r := radScale R ρ k
  let Cb := radialStageRadiusConstant C Cw b
  let B := actualInnerPolynomialForcingCoefficient (η : ℝ) b Cb e L
  have hApos : 0 < A := div_pos hA (pow_pos hb k)
  have hr : 0 < r := radScale_pos hR hρ k
  have hden : b / 2 ≤ b * (1 - ρ ^ 2 / b) := by
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hb.ne']
    linarith
  have hshape : 0 ≤ cauchyContourNormBudget 5 (η : ℝ) 1 e L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1) he 0).trans (le_max_left _ _)
  have hB : 0 ≤ B := by unfold B actualInnerPolynomialForcingCoefficient; positivity [finiteLabelMassBound_nonneg]
  have hnorm (u : ℝ) (hu : u ∈ Icc lower upper) : ‖Q u‖ / (A * r) ≤ B * ρ ^ 6 * (1 + u) ^ 4 := by
    have hut : a + u / A ∈ Icc a H := by
      have hu0 : 0 ≤ u := hlower.trans hu.1
      have huu : u ≤ A * (H - a) := hu.2.trans hupper
      have hdiv : u / A ≤ H - a := (div_le_iff₀ hApos).mpr (by nlinarith only [huu])
      exact ⟨le_add_of_nonneg_right (div_nonneg hu0 hApos.le), by linarith⟩
    have hclock : A * (a + u / A - a) = u := by field_simp [hApos.ne']; ring
    have hi (i : Fin 2) : ‖Q u i‖ / (A * r) ≤ B * ρ ^ 6 * (1 + u) ^ 4 := by
      obtain ⟨Qi, hQi, hn⟩ := hpoint hs hA hR hRmax hρ hρ1 hρhalf hq hqE hsmall houter hc hd hd16 hδ hD
        hsmallDim hcoreDim hchartDim N k hk S hS ha haH hHT htime hglobal G hstart
        (a + u / A) hut η hη he hsep (Z u i) (hZ u hu i) (hL u hu i)
      have heq : Qi = Q u i := littleContour_eq_of_lift_eq (fun θ => (hQi θ).trans (hQ u hu i θ).symm)
      rw [heq] at hn
      change ‖Q u i‖ / (A * r) ≤
        (finiteLabelMassBound * cauchyContourNormBudget 5 (η : ℝ) 1 e L) * Cb ^ 4 * ρ ^ 6 *
          (1 + A * (a + u / A - a)) ^ 4 / (b * (1 - ρ ^ 2 / b)) at hn
      rw [hclock] at hn
      calc
        _ ≤ (finiteLabelMassBound * cauchyContourNormBudget 5 (η : ℝ) 1 e L) * Cb ^ 4 * ρ ^ 6 *
            (1 + u) ^ 4 / (b * (1 - ρ ^ 2 / b)) := hn
        _ ≤ (finiteLabelMassBound * cauchyContourNormBudget 5 (η : ℝ) 1 e L) * Cb ^ 4 * ρ ^ 6 *
            (1 + u) ^ 4 / (b / 2) :=
          div_le_div_of_nonneg_left (by positivity [finiteLabelMassBound_nonneg]) (half_pos hb) hden
        _ = _ := by unfold B actualInnerPolynomialForcingCoefficient; ring
    apply (div_le_iff₀ (mul_pos hApos hr)).mpr
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ B * ρ ^ 6 * (1 + u) ^ 4 * (A * r))).mpr
    intro i
    exact (div_le_iff₀ (mul_pos hApos hr)).mp (hi i)
  let p : ℝ → Fin 2 → LittleContourSpace η := fun u =>
    rigidRotationGauge Ω 0 (τ₀ + u) • ((A * r)⁻¹ • Q u)
  have hp (u : ℝ) : ‖p u‖ = ‖Q u‖ / (A * r) := by
    dsimp only [p]
    rw [norm_smul, norm_rigidRotationGauge, one_mul, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (mul_pos hApos hr)]
    ring
  have hgc : Continuous (fun u : ℝ => rigidRotationGauge Ω 0 (τ₀ + u)) := by unfold rigidRotationGauge; fun_prop
  have hscale : ContinuousOn (fun u : ℝ => ((A * r)⁻¹ : ℝ) • Q u) (Icc lower upper) := by
    simpa only [Pi.smul_def] using hQc.const_smul ((A * r)⁻¹ : ℝ)
  letI : ContinuousSMul ℂ (Fin 2 → LittleContourSpace η) := IsBoundedSMul.continuousSMul
  have hpc : ContinuousOn p (Icc lower upper) := hgc.continuousOn.smul hscale
  exact weighted_polynomial_forcing_finite_tail hσ hlower hB p hpc
    (fun u hu => by rw [hp]; exact hnorm u hu)

end CircularMaterialTransferProfile
end Euler2D

end



