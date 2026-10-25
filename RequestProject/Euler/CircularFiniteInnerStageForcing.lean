module

public import RequestProject.Euler.CircularFiniteInnerStageConfinement
public import RequestProject.Euler.CircularFiniteClusterContourForcing

/-! The actual stage radial fence supplies the relative support needed by
the original Little-space inner-cluster forcing estimate.  All particles
and all transported labels belong to the same finite Euler system. -/

@[expose] public section

set_option maxHeartbeats 3600000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualInnerStage_contourLittle_rhoSix {b Cw : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hCw : 0 ≤ Cw) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {s A₀ R ρ q T c d δ D : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (_hA : 0 < A₀)
        (hR : 0 < R) (_hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (_hρ1 : ρ ≤ 1) (_hρhalf : ρ ≤ b / 2)
        (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (_hsmall : ρ ^ 2 < b) (_houter : b * ρ ^ 2 < 1)
        (_hc : 0 < c) (_hd : 0 < d) (_hd16 : d * R ≤ 1 / 16) (_hδ : 0 ≤ δ) (_hD : 0 ≤ D),
      b * finiteEulerUniformRadialCoefficient K b R ρ c d δ * (radialStageRadiusConstant C Cw b) ^ 3 *
        ρ ^ 2 * (1 + D) ^ 3 ≤ C / 2 →
      radialStageRadiusConstant C Cw b * ρ * (1 + D) ≤ c / 2 →
      radialStageRadiusConstant C Cw b * ρ * (1 + D) ≤ d →
      ∀ N k : ℕ, k ≤ N → ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ {a H : ℝ}, 0 ≤ a → a ≤ H → H ≤ T →
      H - a ≤ D / ((1 - b) * ampScale A₀ b k) →
      (∀ τ ∈ Icc a H, ∀ y ∈ torusBox, d * R < ‖y - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) τ y = 0) →
      (∀ τ ∈ Icc a H, P.FiniteOuterMaterialTube s R ρ N k S τ c δ) →
      (∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward a y - torusCenter‖ ≤ Cw * ρ * radScale R ρ k) →
      ∀ τ ∈ Icc a H, ∀ (η : ℝ≥0), (η : ℝ) ≤ 1 → ∀ {e L : ℝ}, 0 < e →
      8 * (radialStageRadiusConstant C Cw b * ρ * (1 + D)) ≤ e →
      ∀ (Z : LittleContourSpace η),
      (∀ x, e * radScale R ρ k ≤ ‖ContourC1Space.toBCF η Z.val x‖) →
      ‖Z‖ ≤ radScale R ρ k * L →
      ∃ Q : LittleContourSpace η,
        (∀ θ, LittleContourSpace.lift η Q θ =
          velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S τ)
            (LittleContourSpace.lift η Z θ)) ∧
        ‖Q‖ / (ampScale A₀ b k * radScale R ρ k) ≤
          (finiteLabelMassBound * cauchyContourNormBudget 5 (η : ℝ) 1 e L) *
            (radialStageRadiusConstant C Cw b) ^ 4 * ρ ^ 6 * (1 + D) ^ 4 /
              (b * (1 - ρ ^ 2 / b)) := by
  obtain ⟨C, K, hC, hK, hconf⟩ := P.exists_uniform_actualInnerStage_confinement hb hb1 hCw
  refine ⟨C, K, hC, hK, ?_⟩
  intro s A₀ R ρ q T c d δ D _ hs hA hR hRmax hρ hρ1 hρhalf hq hqE hsmall houter hc hd hd16 hδ hD
    hsmallDim hcoreDim hchartDim N k hk S hS a H ha haH hHT hduration hglobal G hstart τ hτ
    η hη e L he hsep Z hZ hL
  have hsupp := (hconf hs hA hR hRmax hρ hρ1 hρhalf hq hqE hsmall houter hc hd hd16 hδ hD
    hsmallDim hcoreDim hchartDim N k hk S hS ha haH hHT hduration hglobal G hstart τ hτ).2
  have hr : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hrR : radScale R ρ k ≤ R :=
    mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hCb := radialStageRadiusConstant_pos hC hCw hb hb1
  have ha1 : radialStageRadiusConstant C Cw b * ρ * radScale R ρ k * (1 + D) < 1 := by
    calc
      _ = (radialStageRadiusConstant C Cw b * ρ * (1 + D)) * radScale R ρ k := by ring
      _ ≤ (radialStageRadiusConstant C Cw b * ρ * (1 + D)) * R :=
        mul_le_mul_of_nonneg_left hrR (by positivity)
      _ ≤ d * R := mul_le_mul_of_nonneg_right hchartDim hR.le
      _ < 1 := hd16.trans_lt (by norm_num)
  exact P.exists_finiteInnerCluster_contourLittle_rhoSix hη hs hA hb hR hRmax hρ hρ1 hsmall
    N k S hS ⟨ha.trans hτ.1, hτ.2.trans hHT⟩ hCb.le hD ha1 hsupp he hsep Z hZ hL

end CircularMaterialTransferProfile
end Euler2D

end
