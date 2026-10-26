module

public import RequestProject.Euler.CircularSinglePlanarLabelTransport
public import RequestProject.Euler.RotatingNormalizedFiniteParticleTransport

/-! The same single integrable planar label has uniform normalized
amplitude and mass at every actual entrance time and angle. The
constants are independent of the finite cutoff and label index. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem norm_normalized_finiteSinglePlanarLabel_le
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (N j : ℕ) {f : Lp ℝ 2 μT} {T t : ℝ} (S : BoundedEulerParticleSystem f T)
    (ht : t ∈ Icc (0 : ℝ) T) (z : R2) :
    ‖S.normalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j)
      (ampScale A₀ b j) (radScale R ρ j) t z‖ ≤ finiteLabelAmplitudeBound := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  apply S.norm_normalizedPlanarLabelSource_le _ _ _ (radScale_pos hR hρ j).ne'
    (entrance := 0) ⟨le_rfl, hT⟩ ht ?_ z
  intro y
  rw [P.normalized_finiteSinglePlanarInitialLabel_zero hA hb hR hρ N j S hT]
  split_ifs
  · exact (norm_circularPhasePatchPlanarVorticity_le hγ hγ1 (P.ancient_domain s hs) y).trans
      (le_max_right _ _)
  · exact (norm_cellW_le_four y).trans (le_max_left _ _)

theorem integral_norm_normalized_finiteSinglePlanarLabel_le
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (N j : ℕ) {f : Lp ℝ 2 μT} {T t : ℝ} (S : BoundedEulerParticleSystem f T)
    (ht : t ∈ Icc (0 : ℝ) T) (harea : MeasurePreserving (S.forward t) volume volume) :
    (∫ z : R2, ‖S.normalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j)
      (ampScale A₀ b j) (radScale R ρ j) t z‖) ≤ finiteLabelMassBound := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hback : S.backward 0 = id := by
    funext z
    simpa only [S.initial, id_eq] using S.backward_forward 0 ⟨le_rfl, hT⟩ z
  rw [S.integral_norm_normalizedPlanarLabelSource _ _ (radScale_pos hR hρ j)
    (entrance := 0) ⟨le_rfl, hT⟩ ht (by rw [hback]; exact MeasurePreserving.id volume) harea]
  have he : S.normalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j)
      (ampScale A₀ b j) (radScale R ρ j) 0 =
        if j = N then circularPhasePatchPlanarVorticity (P.ancient s) else cellW := by
    funext z
    rw [P.normalized_finiteSinglePlanarInitialLabel_zero hA hb hR hρ N j S hT]
    split_ifs <;> rfl
  rw [he]
  split_ifs
  · simp only [Real.norm_eq_abs, finiteLabelMassBound]
    exact (integral_abs_circularPhasePatchPlanarVorticity_le hγ hγ1 (P.ancient_domain s hs)).trans
        (le_max_right _ _)
  · simp only [Real.norm_eq_abs, finiteLabelMassBound]
    exact le_max_left (∫ z : R2, |cellW z|) (finiteContourPatchMassBound circularContourStrengths circularContourRadii)

theorem rotatingNormalized_finiteSinglePlanarLabel_uniform_bounds
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (N j : ℕ) {f : Lp ℝ 2 μT} {T t : ℝ} (S : BoundedEulerParticleSystem f T)
    (ht : t ∈ Icc (0 : ℝ) T) (harea : MeasurePreserving (S.forward t) volume volume) (θ : ℝ) :
    let w := S.rotatingNormalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j)
      (ampScale A₀ b j) (radScale R ρ j) θ t
    Integrable w ∧ (∀ z, ‖w z‖ ≤ finiteLabelAmplitudeBound) ∧
      (∫ z : R2, ‖w z‖) ≤ finiteLabelMassBound := by
  refine ⟨S.integrable_rotatingNormalizedPlanarLabelSource _ _ _ _ _
    (P.integrable_normalized_finiteSinglePlanarLabel hs hA hb hR hρ N j S ht harea), ?_, ?_⟩
  · intro z
    exact P.norm_normalized_finiteSinglePlanarLabel_le hs hA hb hR hρ N j S ht _
  · rw [S.integral_norm_rotatingNormalizedPlanarLabelSource]
    exact P.integral_norm_normalized_finiteSinglePlanarLabel_le hs hA hb hR hρ N j S ht harea

end CircularMaterialTransferProfile
end Euler2D

end
