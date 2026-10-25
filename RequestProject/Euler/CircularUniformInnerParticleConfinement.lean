module

public import RequestProject.Euler.CircularFiniteInnerParticleConfinement

/-! The actual inner-particle confinement constants are chosen before both
the amplitude ratio and the initial particle radius coefficient. This follows
from the same finite Euler particle dynamics and scalar fence. -/

@[expose] public section

set_option maxHeartbeats 7000000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualInnerStage_particle_confinement_constants :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ {b Cw : ℝ}, 0 < b → b < 1 → 0 ≤ Cw →
      ∀ {s A₀ R ρ q T c d δ D : ℝ},
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
      ∀ τ ∈ Icc a H,
        (∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
          ‖S.forward τ y - torusCenter‖ ≤
            radialStageRadiusConstant C Cw b * ρ * radScale R ρ k *
              (1 + (1 - b) * ampScale A₀ b k * (τ - a))) ∧
        (∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
          ‖S.forward τ y - torusCenter‖ ≤
            radialStageRadiusConstant C Cw b * ρ * radScale R ρ k * (1 + D)) := by
  obtain ⟨C, K, hC, hK, hstage⟩ := P.exists_uniform_actualFiniteEuler_stageInnerParticles
  refine ⟨C, K, hC, hK, ?_⟩
  intro b Cw hb hb1 hCw s A₀ R ρ q T c d δ D _ hs hA hR hRmax hρ hρ1 hρhalf hq hqE hsmall houter hc hd hd16 hδ hD
    hsmallDim hcoreDim hchartDim N k hk S hS a H ha haH hHT hduration hglobal G hstart τ hτ
  let Cb := radialStageRadiusConstant C Cw b
  let r := radScale R ρ k
  let A := ampScale A₀ b k
  let B := Cb * ρ * r * (1 + D)
  let V := finiteEulerRadialSelfBudget C A₀ b R ρ k
  let Lcoef := (32 / (15 * c ^ 4) * circularRadialPerturbationWeight) * δ / (1 - b * ρ ^ 2) +
    K * d ^ 4 * circularFiniteL1Coefficient b ρ * R ^ 8 * (b * ρ ^ 2) ^ k
  let Lu := finiteEulerUniformRadialCoefficient K b R ρ c d δ
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hC hCw hb hb1
  have hr : 0 < r := radScale_pos hR hρ k
  have hAk : 0 < A := div_pos hA (pow_pos hb k)
  have hρb : ρ < b := by linarith
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hden' : 0 < 1 - b * ρ ^ 2 := sub_pos.mpr houter
  have hdenMass : 0 < 1 - ρ ^ 2 / b := sub_pos.mpr ((div_lt_one hb).mpr hsmall)
  have hmass : 0 ≤ circularFiniteL1Coefficient b ρ := by
    unfold circularFiniteL1Coefficient finiteContourPatchMassBound
    exact add_nonneg (div_nonneg ENNReal.toReal_nonneg hdenMass.le)
      (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) measureReal_nonneg))
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hLcoef : 0 ≤ Lcoef := by dsimp [Lcoef]; positivity
  have hLu : Lcoef ≤ Lu := by
    dsimp [Lcoef, Lu, finiteEulerUniformRadialCoefficient]
    apply add_le_add le_rfl
    exact mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by positivity : 0 ≤ b * ρ ^ 2) houter.le)
  have hV : 0 < V := by unfold V finiteEulerRadialSelfBudget; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hBcubic : finiteEulerRadialFeedbackBudget K A₀ b R ρ c d δ k * B ^ 3 ≤ V / 2 := by
    calc
      _ = (Lcoef * A / r ^ 2) * B ^ 3 := by change (Lcoef * (A / r ^ 2)) * B ^ 3 = _; ring
      _ ≤ _ := radialStage_cubic_budget hC hb hAk hr hρ hρb hD hCb.le hLcoef hLu hsmallDim
  have hF : finiteEulerRadialSelfBudget C A₀ b R ρ k +
      finiteEulerRadialFeedbackBudget K A₀ b R ρ c d δ k * B ^ 3 < 2 * V := by
    change V + _ < 2 * V
    linarith
  have hbudget : (Cw + 1) * ρ * r + (2 * V) * (H - a) ≤ B :=
    radialStage_linear_budget hC hCw hb hb1 hAk hr hρ hρhalf hD (sub_nonneg.mpr haH) hduration
  have hBcore : B ≤ c * radScale R ρ k / 2 := by
    convert mul_le_mul_of_nonneg_right hcoreDim hr.le using 1 <;> dsimp [B, Cb, r] <;> ring
  have hrR : r ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hBchart : B ≤ d * R := by
    calc
      _ = (Cb * ρ * (1 + D)) * r := by dsimp [B]; ring
      _ ≤ (Cb * ρ * (1 + D)) * R := mul_le_mul_of_nonneg_left hrR (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hchartDim hR.le
  have hB1 : B < 1 := hBchart.trans_lt (hd16.trans_lt (by norm_num))
  have hparticles := hstage hs hA hb hR hRmax hρ hρ1 hρb hq hqE hsmall houter hc hd hd16 hδ N k hk S hS
    ha haH hHT (by positivity : 0 ≤ Cw * ρ * r)
    (by nlinarith [mul_pos hρ hr] : Cw * ρ * r ≤ (Cw + 1) * ρ * r)
    (by positivity : 0 < (Cw + 1) * ρ * r) hB hB1 hBcore hBchart hF hbudget hglobal G hstart τ hτ
  let Dt := (1 - b) * A * (τ - a)
  have hDt : 0 ≤ Dt := mul_nonneg (mul_pos (sub_pos.mpr hb1) hAk).le (sub_nonneg.mpr hτ.1)
  have htimeLocal : τ - a ≤ Dt / ((1 - b) * A) := by
    dsimp only [Dt]
    rw [mul_div_cancel_left₀ _ (mul_pos (sub_pos.mpr hb1) hAk).ne']
  have hlinear := radialStage_linear_budget hC hCw hb hb1 hAk hr hρ hρhalf hDt
    (sub_nonneg.mpr hτ.1) htimeLocal
  have hDtD : Dt ≤ D := by
    have hh := (le_div_iff₀ (mul_pos (sub_pos.mpr hb1) hAk)).mp hduration
    have hh' := mul_le_mul_of_nonneg_left (show τ - a ≤ H - a by linarith [hτ.2])
      (mul_pos (sub_pos.mpr hb1) hAk).le
    dsimp only [Dt]
    nlinarith only [hh, hh']
  have hcap : Cb * ρ * r * (1 + Dt) ≤ Cb * ρ * r * (1 + D) :=
    mul_le_mul_of_nonneg_left (by linarith only [hDtD]) (by positivity)
  refine ⟨?_, ?_⟩
  · intro y hy
    exact (hparticles y hy).trans hlinear
  · intro y hy
    exact ((hparticles y hy).trans hlinear).trans hcap

end CircularMaterialTransferProfile
end Euler2D

end