module

public import RequestProject.Euler.CircularFiniteInnerStageForcing
public import RequestProject.Euler.CircularRetardedBudgetFeedback

/-! The real same-S inner forcing retains its pointwise elapsed-time
polynomial. A common provisional stage horizon is used only to check
the radial fence; it is not substituted into the forcing polynomial. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualInner_pointwise_contourLittle {b Cw : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hCw : 0 ≤ Cw) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {s A₀ R ρ q T c d δ D : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρhalf : ρ ≤ b / 2)
        (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hsmall : ρ ^ 2 < b) (houter : b * ρ ^ 2 < 1)
        (hc : 0 < c) (hd : 0 < d) (hd16 : d * R ≤ 1 / 16) (hδ : 0 ≤ δ) (hD : 0 ≤ D),
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
      ∀ t ∈ Icc a H, ∀ (η : ℝ≥0), (η : ℝ) ≤ 1 → ∀ {e L : ℝ}, 0 < e →
      8 * (radialStageRadiusConstant C Cw b * ρ * (1 + D)) ≤ e →
      ∀ Z : LittleContourSpace η,
      (∀ x, e * radScale R ρ k ≤ ‖ContourC1Space.toBCF η Z.val x‖) →
      ‖Z‖ ≤ radScale R ρ k * L →
      ∃ Q : LittleContourSpace η,
        (∀ θ, LittleContourSpace.lift η Q θ =
          velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t)
            (LittleContourSpace.lift η Z θ)) ∧
        ‖Q‖ / (ampScale A₀ b k * radScale R ρ k) ≤
          (finiteLabelMassBound * cauchyContourNormBudget 5 (η : ℝ) 1 e L) *
            (radialStageRadiusConstant C Cw b) ^ 4 * ρ ^ 6 *
              (1 + ampScale A₀ b k * (t - a)) ^ 4 / (b * (1 - ρ ^ 2 / b)) := by
  obtain ⟨C, K, hC, hK, hlocal⟩ := P.exists_uniform_actualInnerStage_contourLittle_rhoSix hb hb1 hCw
  refine ⟨C, K, hC, hK, ?_⟩
  intro s A₀ R ρ q T c d δ D _ hs hA hR hRmax hρ hρ1 hρhalf hq hqE hsmall houter hc hd hd16 hδ hD
    hsmallDim hcoreDim hchartDim N k hk S hS a H ha haH hHT htime hglobal G hstart t ht
    η hη e L he hsep Z hZ hL
  let A := ampScale A₀ b k
  let Cb := radialStageRadiusConstant C Cw b
  let Dt := (1 - b) * A * (t - a)
  have hApos : 0 < A := div_pos hA (pow_pos hb k)
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hC hCw hb hb1
  have hDt : 0 ≤ Dt := mul_nonneg (mul_nonneg (sub_pos.mpr hb1).le hApos.le) (sub_nonneg.mpr ht.1)
  have hDtD : Dt ≤ D := by
    have hh := (le_div_iff₀ (mul_pos (sub_pos.mpr hb1) hApos)).mp htime
    have hh' := mul_le_mul_of_nonneg_left (show t - a ≤ H - a by linarith [ht.2]) (mul_pos (sub_pos.mpr hb1) hApos).le
    dsimp only [Dt, A] at *
    nlinarith only [hh, hh']
  have hDtOwn : Dt ≤ A * (t - a) := by
    dsimp only [Dt]
    nlinarith only [mul_nonneg hb.le (mul_nonneg hApos.le (sub_nonneg.mpr ht.1))]
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hmass := circularFiniteL1Coefficient_nonneg_of_ratio hb hsmall
  have hcoef : 0 ≤ finiteEulerUniformRadialCoefficient K b R ρ c d δ := by
    have hden : 0 < 1 - b * ρ ^ 2 := sub_pos.mpr houter
    unfold finiteEulerUniformRadialCoefficient
    positivity
  have hsmallLocal : b * finiteEulerUniformRadialCoefficient K b R ρ c d δ * Cb ^ 3 *
      ρ ^ 2 * (1 + Dt) ^ 3 ≤ C / 2 :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Dt) (by linarith : 1 + Dt ≤ 1 + D) 3)
      (by positivity)).trans hsmallDim
  have hlinear : Cb * ρ * (1 + Dt) ≤ Cb * ρ * (1 + D) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCb.le hρ.le)
  have htimeLocal : t - a ≤ Dt / ((1 - b) * A) := by
    dsimp only [Dt]
    rw [mul_div_cancel_left₀ _ (mul_pos (sub_pos.mpr hb1) hApos).ne']
  obtain ⟨Q, hQ, hn⟩ := hlocal hs hA hR hRmax hρ hρ1 hρhalf hq hqE hsmall houter hc hd hd16 hδ hDt
    hsmallLocal (hlinear.trans hcoreDim) (hlinear.trans hchartDim) N k hk S hS
    ha ht.1 (ht.2.trans hHT) htimeLocal
    (fun τ hτ => hglobal τ ⟨hτ.1, hτ.2.trans ht.2⟩)
    (fun τ hτ => G τ ⟨hτ.1, hτ.2.trans ht.2⟩) hstart t ⟨ht.1, le_rfl⟩ η hη he
    ((mul_le_mul_of_nonneg_left hlinear (by norm_num : (0 : ℝ) ≤ 8)).trans hsep) Z hZ hL
  have hshape : 0 ≤ cauchyContourNormBudget 5 (η : ℝ) 1 e L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1) he 0).trans (le_max_left _ _)
  have hden : 0 < b * (1 - ρ ^ 2 / b) := mul_pos hb (sub_pos.mpr ((div_lt_one hb).mpr hsmall))
  refine ⟨Q, hQ, hn.trans ?_⟩
  apply div_le_div_of_nonneg_right _ hden.le
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Dt) (by linarith : 1 + Dt ≤ 1 + A * (t - a)) 4)
    (by positivity [finiteLabelMassBound_nonneg])

end CircularMaterialTransferProfile
end Euler2D

end
