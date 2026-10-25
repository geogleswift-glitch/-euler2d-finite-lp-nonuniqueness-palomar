module

public import RequestProject.Euler.BoundedEulerExistence
public import RequestProject.Euler.LogFlowCompactness

/-!
# Genuine transported domains of the constructed Euler flow

The actual inverse flow makes each map a homeomorphism. In particular,
the image of a patch is an actual open domain and its boundary is the
transported boundary. The displacement estimate uses the genuine ODE.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def homeomorph (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : R2 ≃ₜ R2 where
  toFun := S.forward t
  invFun := S.backward t
  left_inv := S.backward_forward t ht
  right_inv := S.forward_backward t ht
  continuous_toFun := S.forward_continuous.comp (continuous_const.prodMk continuous_id)
  continuous_invFun := S.backward_continuous.comp (continuous_const.prodMk continuous_id)

theorem image_eq_preimage_backward (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (D : Set R2) :
    S.forward t '' D = S.backward t ⁻¹' D :=
  (S.homeomorph t ht).image_eq_preimage_symm D

theorem isOpen_image (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    {D : Set R2} (hD : IsOpen D) : IsOpen (S.forward t '' D) :=
  (S.homeomorph t ht).isOpenMap D hD

theorem image_frontier (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (D : Set R2) :
    S.forward t '' frontier D = frontier (S.forward t '' D) :=
  (S.homeomorph t ht).image_frontier D

theorem indicator_backward (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (D : Set R2) (c : ℝ) (x : R2) :
    D.indicator (fun _ => c) (S.backward t x) =
      (S.forward t '' D).indicator (fun _ => c) x := by
  classical
  rw [S.image_eq_preimage_backward t ht D]
  by_cases hx : S.backward t x ∈ D
  · simp only [indicator_of_mem hx, indicator_of_mem (show x ∈ S.backward t ⁻¹' D from hx)]
  · simp only [indicator_of_notMem hx,
      indicator_of_notMem (show x ∉ S.backward t ⁻¹' D from hx)]

theorem displacement_le {B : ℝ} (hT : 0 ≤ T) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    ‖S.forward t a - a‖ ≤
      (B * ∫ y in torusBox, ‖torusBiotSavartKernel y‖) * t := by
  have hb := norm_trajectory_sub_time_le
    (fun s hs => S.derivative s hs a)
    (fun s _ x => norm_particleVelocityRepresentative_le f hB
      S.backward S.backward_area s x) (s := 0) ⟨le_rfl, hT⟩ ht
  simpa only [S.initial a, sub_zero, abs_of_nonneg ht.1] using hb

end BoundedEulerParticleSystem
end Euler2D

end
