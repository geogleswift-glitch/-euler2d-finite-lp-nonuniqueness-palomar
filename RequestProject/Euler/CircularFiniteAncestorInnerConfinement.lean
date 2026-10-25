module

public import RequestProject.Euler.CircularFiniteInnerInitialRadius
public import RequestProject.Euler.CircularFiniteAncestorGeometricForcing

/-! One cumulative current-cell horizon confines the real inner
source of every ancestor. Each starting radius comes from the same
original finite datum; the only contour tubes are the active ancestor
prefix, and no deep contour is assumed to stay circular. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualAncestorInner_confinement {b : ℝ}
    (hb : 0 < b) (hb1 : b < 1) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {s A₀ R ρ q T c d δ D H : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρhalf : ρ ≤ b / 2)
        (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hsmall : ρ ^ 2 < b) (houter : b * ρ ^ 2 < 1)
        (hc : 0 < c) (hd : 0 < d) (hd16 : d * R ≤ 1 / 16) (hδ : 0 ≤ δ) (hD : 0 ≤ D),
      b * finiteEulerUniformRadialCoefficient K b R ρ c d δ *
          (radialStageRadiusConstant C (5 / 4) b) ^ 3 * ρ ^ 2 * (1 + D) ^ 3 ≤ C / 2 →
      radialStageRadiusConstant C (5 / 4) b * ρ * (1 + D) ≤ c / 2 →
      radialStageRadiusConstant C (5 / 4) b * ρ * (1 + D) ≤ d →
      ∀ (N k : ℕ) (hk : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → 0 ≤ H → H ≤ T →
      H ≤ D / ((1 - b) * ampScale A₀ b k) →
      (∀ τ ∈ Icc (0 : ℝ) H, ∀ y ∈ torusBox, d * R < ‖y - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) τ y = 0) →
      (∀ τ ∈ Icc (0 : ℝ) H, P.FiniteOuterMaterialTube s R ρ N (k - 1) S τ c δ) →
      ∀ j : Fin k, ∀ τ ∈ Icc (0 : ℝ) H, ∀ y ∈ torusBox,
        radialStageRadiusConstant C (5 / 4) b * ρ * radScale R ρ j * (1 + D) <
          ‖y - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N j S τ y = 0 := by
  obtain ⟨C, K, hC, hK, hconf⟩ :=
    P.exists_uniform_actualInnerStage_confinement hb hb1 (by norm_num : (0 : ℝ) ≤ 5 / 4)
  refine ⟨C, K, hC, hK, ?_⟩
  intro s A₀ R ρ q T c d δ D H _ hs hA hR hRmax hρ hρ1 hρhalf hq hqE hsmall houter
    hc hd hd16 hδ hD hsmallDim hcoreDim hchartDim N k hk S hS hH hHT htime hglobal G j τ hτ y hy hfar
  have hjk : (j : ℕ) ≤ k := Nat.le_of_lt j.isLt
  have hjN : (j : ℕ) ≤ N := hjk.trans hk
  have hAj : 0 < ampScale A₀ b j := div_pos hA (pow_pos hb j)
  have hAk : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hAmp : ampScale A₀ b j ≤ ampScale A₀ b k :=
    div_le_div_of_nonneg_left hA.le (pow_pos hb k)
      (pow_le_pow_of_le_one hb.le hb1.le hjk)
  have htimej : H - 0 ≤ D / ((1 - b) * ampScale A₀ b j) := by
    have hh : D / ((1 - b) * ampScale A₀ b k) ≤
        D / ((1 - b) * ampScale A₀ b j) :=
      div_le_div_of_nonneg_left hD (mul_pos (sub_pos.mpr hb1) hAj)
        (mul_le_mul_of_nonneg_left hAmp (sub_pos.mpr hb1).le)
    simpa only [sub_zero] using htime.trans hh
  have hstart := P.finiteInnerActiveInitial_forward_zero_radius (A₀ := A₀) (b := b)
    hs hR hRmax hρ hρ1 N j S
  exact (hconf hs hA hR hRmax hρ hρ1 hρhalf hq hqE hsmall houter hc hd hd16 hδ hD
    hsmallDim hcoreDim hchartDim N j hjN S hS (a := 0) (H := H) le_rfl hH hHT htimej
    hglobal (fun t ht => P.finiteOuterMaterialTubeRestrict (G t ht) (by omega)) hstart τ hτ).2 y hy hfar

end CircularMaterialTransferProfile
end Euler2D

end
