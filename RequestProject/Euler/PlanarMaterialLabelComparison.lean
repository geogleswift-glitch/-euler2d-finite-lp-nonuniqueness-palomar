module

public import RequestProject.Euler.PlanarRegularizedTransport

/-! Actual whole-plane initial-label integrals for material flows.
A globally Lipschitz bounded kernel gives a uniform comparison of
the true self-consistent velocities of two particle configurations. -/

@[expose] public section

set_option maxHeartbeats 2200000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

def planarMaterialLabelVelocity (K : R2 → R2) (w : R2 → ℝ) (X : R2 → R2) (x : R2) : R2 :=
  ∫ b, w b • K (x - X b)

theorem integrable_planarMaterialLabel_integrand {K : R2 → R2} {w : R2 → ℝ} {M : ℝ≥0}
    (hw : Integrable w) (hK : Continuous K) (hM : ∀ x, ‖K x‖ ≤ M)
    {X : R2 → R2} (hX : Continuous X) (x : R2) : Integrable (fun b => w b • K (x - X b)) :=
  hw.smul_bdd (M : ℝ) ((hK.comp (continuous_const.sub hX)).aestronglyMeasurable)
    (ae_of_all _ (fun b => hM (x - X b)))

theorem norm_planarMaterialLabelVelocity_le {K : R2 → R2} {w : R2 → ℝ} {M : ℝ≥0}
    (hw : Integrable w) (hM : ∀ x, ‖K x‖ ≤ M) (X : R2 → R2) (x : R2) :
    ‖planarMaterialLabelVelocity K w X x‖ ≤ (M : ℝ) * ∫ b, ‖w b‖ := by
  unfold planarMaterialLabelVelocity
  calc
    _ ≤ ∫ b, (M : ℝ) * ‖w b‖ := norm_integral_le_of_norm_le (hw.norm.const_mul _)
      (ae_of_all _ (fun b => by
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)).trans_eq (mul_comm _ _)))
    _ = _ := integral_const_mul _ _

theorem norm_planarMaterialLabelVelocity_sub_le
    {K : R2 → R2} {w : R2 → ℝ} {L M : ℝ≥0}
    (hw : Integrable w) (hK : LipschitzWith L K) (hM : ∀ x, ‖K x‖ ≤ M)
    {X Y : R2 → R2} (hX : Continuous X) (hY : Continuous Y)
    {D : ℝ} (hD : ∀ b, ‖X b - Y b‖ ≤ D) (a : R2) :
    ‖planarMaterialLabelVelocity K w X (X a) - planarMaterialLabelVelocity K w Y (Y a)‖ ≤
      (2 * (L : ℝ) * ∫ b, ‖w b‖) * D := by
  unfold planarMaterialLabelVelocity
  rw [← integral_sub (integrable_planarMaterialLabel_integrand hw hK.continuous hM hX (X a))
    (integrable_planarMaterialLabel_integrand hw hK.continuous hM hY (Y a))]
  have hpoint (b : R2) : ‖w b • K (X a - X b) - w b • K (Y a - Y b)‖ ≤
      (2 * (L : ℝ) * D) * ‖w b‖ := by
    have he : X a - X b - (Y a - Y b) = (X a - Y a) - (X b - Y b) := by abel
    have harg : ‖X a - X b - (Y a - Y b)‖ ≤ 2 * D := by
      rw [he]
      exact (norm_sub_le _ _).trans ((add_le_add (hD a) (hD b)).trans_eq (by ring))
    have hk : ‖K (X a - X b) - K (Y a - Y b)‖ ≤ (L : ℝ) * (2 * D) := by
      have hh := (hK.dist_le_mul (X a - X b) (Y a - Y b)).trans
        (mul_le_mul_of_nonneg_left (show dist (X a - X b) (Y a - Y b) ≤ 2 * D by
          simpa only [dist_eq_norm] using harg) L.coe_nonneg)
      simpa only [dist_eq_norm] using hh
    rw [← smul_sub, norm_smul]
    exact (mul_le_mul_of_nonneg_left hk (norm_nonneg _)).trans_eq (by ring)
  calc
    _ ≤ ∫ b, (2 * (L : ℝ) * D) * ‖w b‖ :=
      norm_integral_le_of_norm_le (hw.norm.const_mul _) (ae_of_all _ hpoint)
    _ = _ := by rw [integral_const_mul]; ring

theorem SmoothPlanarRegularizedParticleSystem.velocity_eq_materialLabelVelocity
    {K : R2 → R2} {w : R2 → ℝ} {T : ℝ} {L M : ℝ≥0}
    (S : SmoothPlanarRegularizedParticleSystem K w T L M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    S.velocity t x = planarMaterialLabelVelocity K (planarBoxSource w) (S.particles.forward t) x := by
  rw [S.label_integral t ht x]
  change (∫ b in torusBox, w b • K (x - S.particles.forward t b)) = _
  rw [← integral_indicator measurableSet_torusBox]
  apply integral_congr_ae
  exact ae_of_all _ (fun b => by
    dsimp only [planarMaterialLabelVelocity]
    by_cases hb : b ∈ torusBox <;> simp [planarBoxSource, hb])

end Euler2D

end
