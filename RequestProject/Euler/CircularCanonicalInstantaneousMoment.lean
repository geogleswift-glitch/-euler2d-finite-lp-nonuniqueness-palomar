module

public import RequestProject.Euler.CircularQuarterPhaseSymmetry
public import RequestProject.Euler.CircularCanonicalHandoffEntry
public import RequestProject.Euler.CircularActualEntryDensityCloseness
public import RequestProject.Euler.ActualFinitePlanarSourceIdentity
public import RequestProject.Euler.RotatingNormalizedPhysicalMoment
public import RequestProject.Euler.CircularCaptureBackwardMoment

/-! The literal boxed child moment of the original Euler system is
the boundary moment of its SAME actual aligned canonical contour,
with exact physical amplitude, length and rotation factors. This
identity holds during capture and does not require an observer or
matching to a different model moment. -/

@[expose] public section

set_option maxHeartbeats 20000000
set_option maxRecDepth 7000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower

theorem circularCanonicalHandoffAlignment_self {γ : ℝ≥0} (τ : ℝ)
    (Y : Fin 2 → LittleContourSpace γ) :
    circularCanonicalHandoffAlignmentCLM γ τ 0 τ Y = Y := by
  unfold circularCanonicalHandoffAlignmentCLM
  simp only [ContinuousLinearMap.comp_apply, neg_zero]
  have hrot : contourRotationFamilyLittleCLM γ 0 (circularCoRotationCLM γ τ Y) =
      circularCoRotationCLM γ τ Y := by
    funext i
    exact contourRotationLittleCLM_zero _
  rw [hrot, circularCoRotationCLM_add, neg_add_cancel, circularCoRotationCLM_zero]

theorem canonicalPrefix_aligned_current_raw {γ : ℝ≥0}
    {A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (k : ℕ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (entrance τ t : ℝ)
    (htime : physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t) :
    ∀ i, (X t (Fin.last k, i)).val = radScale R ρ k •
      ContourC1Space.complexScale (Complex.exp (((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ) * I))
        (contourParameterShiftC1 (circularContourAngularVelocities i * (ampScale A₀ b k * entrance))
          (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ i).val) := by
  have hh := canonicalPrefix_handoff_entry_contours hR hρ k X entrance τ t τ 0 htime
  simpa only [circularCanonicalHandoffAlignment_self, add_zero, sub_zero, add_sub_cancel_right] using hh

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_instantaneous_boxed_moment :
    ∃ C > 0, ∀ {s A₀ b R ρ q T Hglob c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < c → c * R ≤ 1 / 4 →
      ∀ N : ℕ,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      ∀ {k : ℕ} (hkN : k ≤ N) {a D : ℝ}, 0 ≤ D →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S D X →
      ∀ t ∈ Icc (0 : ℝ) D, ∀ entrance τ : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t →
      momentN (boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) 4 =
        (ampScale A₀ b k : ℂ) * (radScale R ρ k : ℂ) ^ 6 *
          Complex.exp (-(4 * (((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ)) * I)) *
            circularBoundaryFourthMoment (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ) := by
  obtain ⟨Ci, hCi, himages⟩ := P.exists_uniform_actualCanonical_prefix_material_images
  obtain ⟨Cl, hCl, hlocalize⟩ := P.exists_uniform_actualFinite_boxed_label_eq_singlePlanar
  let C := Ci + Cl + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCiC : Ci ≤ C := by dsimp only [C]; linarith only [hCl]
  have hClC : Cl ≤ C := by dsimp only [C]; linarith only [hCi]
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T Hglob c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hdrift hcR
    N S k hkN a D hD X hX t ht entrance τ htime
  have hHglob : 0 ≤ Hglob := hD.trans (hX.mem D ⟨hD, le_rfl⟩).1.2
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hdriftC (C' : ℝ) (hC' : C' ≤ C) : 5 / 4 + (C' * A₀ / (1 - ρ / b)) * Hglob < c := by
    exact lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hA.le) hden.le) hHglob)) hdrift
  have htglob : t ∈ Icc (0 : ℝ) Hglob := (hX.mem t ht).1
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, htglob.2.trans hglobT⟩
  have hboxed := hlocalize hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hHglob hglobT
    (hdriftC Cl hClC) (hcR.trans_lt (by norm_num : (1 / 4 : ℝ) < 1)) N S t htglob k
  let j : Fin (N + 1) := ⟨k, Nat.lt_succ_of_le hkN⟩
  let Y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X τ
  let θ := t * finiteAncestorAngularVelocity A₀ b k
  let β := fun i : Fin 2 => circularContourAngularVelocities i * (ampScale A₀ b k * entrance)
  let Zend := fun i : Fin 2 => (X t (Fin.last k, i)).val
  have hscale := canonicalPrefix_aligned_current_raw hR hρ k X entrance τ t htime
  have hIm : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (LittleContourSpace.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)))) =
        complexTorusPoint '' contourRadialFill (LittleContourSpace.lift γ (X t (Fin.last k, i))) := by
    intro i
    exact himages hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hglobT (hdriftC Ci hCiC)
      hcR N S hkN hD X hX t ht (Fin.last k, i)
  have hdensity : S.rotatingNormalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N k)
      (ampScale A₀ b k) (radScale R ρ k) θ t = circularPhasePatchPlanarVorticity Y := by
    funext z
    exact P.rotatingNormalized_finiteSinglePlanarLabel_eq_circularPhasePatch
      hA hb hR hρ N j S htT θ β Y Zend hscale hIm z
  have hY : Y ∈ circularQuarterPhaseDomain hγ hγ1 :=
    canonicalPrefixAlignedCurrentCell_mem_quarterPhaseDomain hγ hγ1 hR hρ A₀ b k X t
      (hX.mem t ht).2.1 (hX.mem t ht).2.2.2.1 entrance τ htime
  have hAmp : ampScale A₀ b k ≠ 0 := (div_pos hA (pow_pos hb k)).ne'
  rw [hboxed, S.momentN_singlePlanar_eq_rotatingNormalizedFourthMoment _ _ hAmp
    (radScale_pos hR hρ k) θ t, hdensity,
      planarFourthMoment_circularPhasePatchPlanarVorticity hγ hγ1 hY]

end CircularMaterialTransferProfile
end Euler2D

end
