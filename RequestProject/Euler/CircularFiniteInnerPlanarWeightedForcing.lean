module

public import RequestProject.Euler.CircularFiniteClusterContourForcing
public import RequestProject.Euler.CircularFiniteInnerInteractionRow

/-! The same actual deep cluster has its own planar Little budget on
every ancestor target, with the original sixth-power ancestor weight. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_finiteInnerCluster_planar_weighted_contourLittle
    {η : ℝ≥0} (hη : (η : ℝ) ≤ 1) {s A₀ b R ρ c D C₀ e L : ℝ}
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ 2 < b)
    (hc : 0 ≤ c) (hD : 0 ≤ D) (hC₀ : 1 ≤ C₀)
    (N k j : ℕ) (hjk : j ≤ k) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (hS : IsFourfoldBoundedEulerParticleSystem S)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (ha1 : c * ρ * radScale R ρ k * (1 + D) < 1)
    (hsupp : ∀ x ∈ torusBox, c * ρ * radScale R ρ k * (1 + D) < ‖x - torusCenter‖ →
      P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0)
    (he : 0 < e) (hsep : 8 * (c * ρ * radScale R ρ k * (1 + D)) ≤ e * radScale R ρ j)
    (Z : LittleContourSpace η)
    (hZ : ∀ x, e * radScale R ρ j ≤ ‖ContourC1Space.toBCF η Z.val x‖)
    (hL : ‖Z‖ ≤ radScale R ρ j * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t)
          (LittleContourSpace.lift η Z θ)) ∧
      ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
        (C₀ * ρ ^ 6) ^ (k - j) *
          ((finiteLabelMassBound * cauchyContourNormBudget 5 (η : ℝ) 1 e L) *
            c ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b))) := by
  have hrj : 0 < radScale R ρ j := radScale_pos hR hρ j
  have hrk : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have ha : 0 ≤ c * ρ * radScale R ρ k * (1 + D) := by positivity
  obtain ⟨Q, hQ, hn⟩ := P.exists_finiteInnerCluster_contourLittle hη hs hA.le hb hR hRmax
    hρ hρ1 hsmall N k S hS ht ha ha1 hsupp (mul_pos he hrj) hsep Z hZ
  let M := (c * ρ * radScale R ρ k * (1 + D)) ^ 4 * finiteInnerClusterMassBudget A₀ b R ρ k
  have hM : 0 ≤ M := (integral_nonneg (fun z => by positivity)).trans
    (P.finiteInnerClusterComplexSource_fourthAbsoluteMoment_le hs hA.le hb hR hRmax
      hρ hρ1 hsmall N k S t hsupp)
  have hn' := hn.trans (cauchyContourNormBudget_mono_length 5 (η : ℝ) hM
    (mul_pos he hrj) (norm_nonneg Z) hL)
  rw [mul_comm e, cauchyContourNormBudget_physical_scale 5 (η : ℝ) hM hrj he L] at hn'
  let B := (finiteLabelMassBound * cauchyContourNormBudget 5 (η : ℝ) 1 e L) *
    c ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b))
  have hshape : 0 ≤ cauchyContourNormBudget 5 (η : ℝ) 1 e L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1) he 0).trans (le_max_left _ _)
  have hden : 0 < b * (1 - ρ ^ 2 / b) := mul_pos hb (sub_pos.mpr ((div_lt_one hb).mpr hsmall))
  have hB : 0 ≤ B := by unfold B; positivity [finiteLabelMassBound_nonneg]
  have hphysical : ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤ B * (radScale R ρ k / radScale R ρ j) ^ 6 := by
    calc
      _ ≤ ((M / radScale R ρ j ^ 5) * cauchyContourNormBudget 5 (η : ℝ) 1 e L) /
          (ampScale A₀ b k * radScale R ρ j) :=
        div_le_div_of_nonneg_right hn' (mul_pos hAk hrj).le
      _ = _ := by
        unfold B M finiteInnerClusterMassBudget
        field_simp [hrj.ne', hAk.ne', hb.ne']
        <;> ring
  have hweight : (radScale R ρ k / radScale R ρ j) ^ 6 ≤ (C₀ * ρ ^ 6) ^ (k - j) := by
    rw [radScale_ratio_eq_pow hR.ne' hρ.ne' hjk, ← pow_mul, Nat.mul_comm (k - j) 6, pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hC₀ (by positivity : 0 ≤ ρ ^ 6)]
  refine ⟨Q, hQ, hphysical.trans ?_⟩
  change B * (radScale R ρ k / radScale R ρ j) ^ 6 ≤ (C₀ * ρ ^ 6) ^ (k - j) * B
  exact (mul_le_mul_of_nonneg_left hweight hB).trans_eq (mul_comm _ _)

end CircularMaterialTransferProfile
end Euler2D

end
