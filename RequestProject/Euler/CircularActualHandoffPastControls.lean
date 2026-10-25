module

public import RequestProject.Euler.CircularActualParentWholePastMoment
public import RequestProject.Euler.CircularCanonicalCrossPrefixReset

/-! Full-past controls at the real next handoff. Raw past agreement,
capture-segment controls and the SAME actual particle flow are spliced
at the actual physical capture entrance, without restarting time. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule

theorem norm_canonicalPrefixStage_current_eq_material_current {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (A₀ b R ρ : ℝ) (k : ℕ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (τ : ℝ) :
    ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ k‖ =
      ‖canonicalPrefixMaterialCurrentCell A₀ b R ρ k X τ - littleCircularReference hγ hγ1‖ := by
  rw [norm_canonicalPrefixMaterialCurrent_sub_reference,
    ← canonicalPrefixAlignedCurrentCell_zero_entrance,
    norm_canonicalPrefixAlignedCurrentCell_sub_reference]

theorem canonicalPrefix_current_le_of_full_material_history {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (A₀ b R ρ : ℝ) (k : ℕ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    {rate η exit τ : ℝ} (hrate : 0 ≤ rate) (hη : 0 ≤ η) (hτ : τ ∈ Icc (0 : ℝ) exit)
    (hhistory : ∀ u ∈ Icc (0 : ℝ) exit,
      ‖canonicalPrefixMaterialCurrentCell A₀ b R ρ k X u - littleCircularReference hγ hγ1‖ ≤
        η * Real.exp (-rate * (exit - u))) :
    ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ k‖ ≤ η := by
  rw [norm_canonicalPrefixStage_current_eq_material_current]
  have he : Real.exp (-rate * (exit - τ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrate) (sub_nonneg.mpr hτ.2))
  exact (hhistory τ hτ).trans (mul_le_of_le_one_right hη he)

theorem canonicalPrefix_whole_past_weighted_splice {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {A₀ b R ρ h entrance D shift : ℝ}
    (hA : 0 < A₀) (hb : 0 < b) (hentrance : 0 ≤ entrance)
    (hshift : 0 ≤ shift) (hshiftD : shift ≤ D) (k : ℕ)
    (X Ypast : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hpastEq : EqOn X Ypast (Icc (0 : ℝ) entrance))
    (hpast : ∀ t ∈ Icc (0 : ℝ) entrance,
      weightedFamilyNorm h k
        (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Ypast (ampScale A₀ b k * t)) ≤ 1)
    (hcapture : ∀ u ∈ Icc (0 : ℝ) D,
      weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X u) ≤ 1) :
    ∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance + shift),
      weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ) ≤ 1 := by
  have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  intro τ hτ
  let t := τ / ampScale A₀ b k
  have hclock : physicalTimeFromNormalized (ampScale A₀ b k) 0 τ = t := by
    simp only [physicalTimeFromNormalized, zero_add, t]
  by_cases hearly : τ ≤ ampScale A₀ b k * entrance
  · have ht : t ∈ Icc (0 : ℝ) entrance := by
      refine ⟨div_nonneg hτ.1 hAmp.le, ?_⟩
      exact (div_le_iff₀ hAmp).mpr (by simpa only [mul_comm] using hearly)
    have heq (j : ℕ) (hj : j ≤ k) :
        canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Ypast τ j =
          canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ j :=
      canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hb.ne' R ρ le_rfl
        X Ypast t 0 τ 0 τ hclock hclock (fun p => congrFun (hpastEq ht).symm p) j hj
    rw [← weightedFamilyNorm_congr_prefix h k (fun j => heq j j.isLt.le)]
    have hτeq : ampScale A₀ b k * t = τ := by
      dsimp only [t]
      field_simp [hAmp.ne']
    simpa only [hτeq] using hpast t ht
  · let u := τ - ampScale A₀ b k * entrance
    have hu : u ∈ Icc (0 : ℝ) D := by
      refine ⟨?_, ?_⟩
      · dsimp only [u]
        linarith only [hearly]
      · dsimp only [u]
        linarith only [hτ.2, hshiftD]
    have hclockCapture : physicalTimeFromNormalized (ampScale A₀ b k) entrance u = t := by
      dsimp only [physicalTimeFromNormalized, u, t]
      field_simp [hAmp.ne'] <;> ring
    have heq (j : ℕ) (hj : j ≤ k) :
        canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X u j =
          canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ j :=
      canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hb.ne' R ρ le_rfl
        X X t 0 τ entrance u hclock hclockCapture (fun _ => rfl) j hj
    rw [← weightedFamilyNorm_congr_prefix h k (fun j => heq j j.isLt.le)]
    exact hcapture u hu

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actual_inner_particle_handoff_radius_splice
    {s A₀ b R ρ entrance D shift Cb : ℝ}
    (hA : 0 < A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (hCb : 0 ≤ Cb)
    (hshift : 0 ≤ shift) (hshiftD : shift ≤ D)
    (hsmall : Cb * ρ * (1 + D) ≤ 2) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (hpast : ∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
      ‖S.forward t z - torusCenter‖ ≤ 2 * radScale R ρ k)
    (hcapture : ∀ u ∈ Icc (0 : ℝ) D, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
      ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance u) z - torusCenter‖ ≤
        Cb * ρ * radScale R ρ k * (1 + u)) :
    ∀ t ∈ Icc (0 : ℝ) (entrance + shift / ampScale A₀ b k),
      ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
      ‖S.forward t z - torusCenter‖ ≤ 2 * radScale R ρ k := by
  have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hrad : 0 < radScale R ρ k := radScale_pos hR hρ k
  intro t ht z hz
  by_cases hearly : t ≤ entrance
  · exact hpast t ⟨ht.1, hearly⟩ z hz
  · let u := ampScale A₀ b k * (t - entrance)
    have hupper : ampScale A₀ b k * t ≤ ampScale A₀ b k * entrance + shift := by
      calc
        _ ≤ ampScale A₀ b k * (entrance + shift / ampScale A₀ b k) :=
          mul_le_mul_of_nonneg_left ht.2 hAmp.le
        _ = _ := by field_simp [hAmp.ne'] <;> ring
    have hu : u ∈ Icc (0 : ℝ) D := by
      refine ⟨mul_nonneg hAmp.le (by linarith only [hearly]), ?_⟩
      dsimp only [u]
      nlinarith only [hupper, hshiftD]
    have hclock : physicalTimeFromNormalized (ampScale A₀ b k) entrance u = t := by
      dsimp only [physicalTimeFromNormalized, u]
      field_simp [hAmp.ne'] <;> ring
    have hbound := hcapture u hu z hz
    rw [hclock] at hbound
    calc
      _ ≤ Cb * ρ * radScale R ρ k * (1 + u) := hbound
      _ ≤ Cb * ρ * radScale R ρ k * (1 + D) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hu.2) (by positivity)
      _ = (Cb * ρ * (1 + D)) * radScale R ρ k := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hrad.le

end CircularMaterialTransferProfile
end Euler2D

end
