module

public import RequestProject.Euler.GlobalPlanarEulerExistence

/-! True translation covariance of the original singular planar
equation. The source box is only a construction device: an actual
centered compact source is retained exactly after shifting back. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

theorem planarBiotSavart_translate (w : R2 → ℝ) (c x : R2) :
    planarKernelVelocity kernelK (fun y => w (y - c)) x = planarKernelVelocity kernelK w (x - c) := by
  unfold planarKernelVelocity
  calc
    _ = ∫ z, w (z + c - c) • kernelK (x - (z + c)) :=
      (integral_add_right_eq_self (μ := volume) (fun y : R2 => w (y - c) • kernelK (x - y)) c).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        dsimp only
        rw [add_sub_cancel_right]
        congr 2
        abel)

namespace GlobalPlanarEulerParticleSystem

variable {w : R2 → ℝ} (S : GlobalPlanarEulerParticleSystem w)

def translate (c : R2) : GlobalPlanarEulerParticleSystem (fun x => w (x - c)) where
  velocity := fun t x => S.velocity t (x - c)
  forward := fun t a => S.forward t (a - c) + c
  backward := fun t a => S.backward t (a - c) + c
  continuous_velocity := S.continuous_velocity.comp
    (continuous_fst.prodMk (continuous_snd.sub continuous_const))
  continuous_forward := (S.continuous_forward.comp
    (continuous_fst.prodMk (continuous_snd.sub continuous_const))).add continuous_const
  continuous_backward := (S.continuous_backward.comp
    (continuous_fst.prodMk (continuous_snd.sub continuous_const))).add continuous_const
  initial := fun a => by rw [S.initial, sub_add_cancel]
  derivative := fun t ht a => by
    simpa only [add_sub_cancel_right] using (S.derivative t ht (a - c)).add_const c
  left_inv := fun t ht a => by rw [add_sub_cancel_right, S.left_inv t ht, sub_add_cancel]
  right_inv := fun t ht a => by rw [add_sub_cancel_right, S.right_inv t ht, sub_add_cancel]
  forward_area := fun t ht => by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right volume c).comp
        ((S.forward_area t ht).comp (measurePreserving_add_right volume (-c)))
  backward_area := fun t => by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right volume c).comp
        ((S.backward_area t).comp (measurePreserving_add_right volume (-c)))
  selfconsistent := fun t x => by
    simp only [add_sub_cancel_right]
    rw [S.selfconsistent]
    exact (planarBiotSavart_translate (fun y => w (S.backward t y)) c x).symm

end GlobalPlanarEulerParticleSystem

theorem exists_globalPlanarEulerParticleSystem_of_shifted_box
    {w : R2 → ℝ} {B : ℝ} (hw : Integrable w) (hB : 0 ≤ B)
    (hwB : ∀ x, ‖w x‖ ≤ B) (c : R2)
    (hsource : ∀ x, w x ≠ 0 → x + c ∈ torusBox) :
    Nonempty (GlobalPlanarEulerParticleSystem w) := by
  let wc : R2 → ℝ := fun x => w (x - c)
  have hwc : Integrable wc := by
    simpa only [wc, Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right volume (-c)).integrable_comp_of_integrable hw
  have hbox : planarBoxSource wc = wc := by
    funext x
    by_cases hx : x ∈ torusBox
    · exact indicator_of_mem hx wc
    · have hz : wc x = 0 := by
        by_contra hn
        have hm := hsource (x - c) hn
        rw [sub_add_cancel] at hm
        exact hx hm
      simp only [planarBoxSource, indicator_of_notMem hx, hz]
  obtain ⟨S⟩ := exists_globalPlanarEulerParticleSystem (w := wc)
    hwc.integrableOn hB (fun x _ => hwB (x - c))
  have S' : GlobalPlanarEulerParticleSystem wc := hbox ▸ S
  simpa only [wc, sub_neg_eq_add, add_sub_cancel_right] using (show
    Nonempty (GlobalPlanarEulerParticleSystem (fun x => wc (x - -c))) from ⟨S'.translate (-c)⟩)

end Euler2D

end
