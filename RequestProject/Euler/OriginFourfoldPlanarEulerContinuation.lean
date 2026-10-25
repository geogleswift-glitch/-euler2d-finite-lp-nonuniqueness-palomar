module

public import RequestProject.Euler.FourfoldPlanarEulerConstruction
public import RequestProject.Euler.GlobalPlanarEulerBounds

/-! Fourfold symmetry about the physical origin after an exact
translation to the construction box and back. The original density is
retained in full, and actual forward and inverse particle maps commute
with the physical rotation. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

structure IsOriginFourfoldGlobalPlanarEulerParticleSystem {w : R2 → ℝ}
    (S : GlobalPlanarEulerParticleSystem w) : Prop where
  forward : ∀ t, 0 ≤ t → ∀ a, S.forward t (perpJ a) = perpJ (S.forward t a)
  backward : ∀ t a, S.backward t (perpJ a) = perpJ (S.backward t a)

theorem exists_originFourfoldGlobalPlanarEulerParticleSystem_of_shifted_box
    {w : R2 → ℝ} {B : ℝ} (hw : Integrable w) (hB : 0 ≤ B)
    (hwB : ∀ x, ‖w x‖ ≤ B) (hwrot : ∀ x, w (perpJ x) = w x)
    (hsource : ∀ x, w x ≠ 0 → x + torusCenter ∈ torusBox) :
    ∃ S : GlobalPlanarEulerParticleSystem w, IsOriginFourfoldGlobalPlanarEulerParticleSystem S := by
  let wc : R2 → ℝ := fun x => w (x - torusCenter)
  have hwc : Integrable wc := by
    simpa only [wc, Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right volume (-torusCenter)).integrable_comp_of_integrable hw
  have hbox : planarBoxSource wc = wc := by
    funext x
    by_cases hx : x ∈ torusBox
    · exact indicator_of_mem hx wc
    · have hz : wc x = 0 := by
        by_contra hn
        have hm := hsource (x - torusCenter) hn
        rw [sub_add_cancel] at hm
        exact hx hm
      simp only [planarBoxSource, indicator_of_notMem hx, hz]
  have hwcrot (x : R2) : wc (torusQuarterTurn x) = wc x := by
    simpa only [wc, torusQuarterTurn, add_sub_cancel_left] using hwrot (x - torusCenter)
  have hwbcrot (x : R2) : planarBoxSource wc (torusQuarterTurn x) = planarBoxSource wc x := by
    rw [hbox]
    exact hwcrot x
  have hex : ∃ S : GlobalPlanarEulerParticleSystem wc, IsFourfoldGlobalPlanarEulerParticleSystem S := by
    exact hbox ▸ exists_fourfoldGlobalPlanarEulerParticleSystem
      (w := wc) hwc.integrableOn hB (fun x _ => hwB (x - torusCenter)) hwbcrot
  obtain ⟨S, hS⟩ := hex
  have harg (a : R2) : perpJ a - -torusCenter = torusQuarterTurn (a - -torusCenter) := by
    ext i
    fin_cases i <;> simp [torusQuarterTurn, perpJ] <;> ring
  have hshift (x : R2) : torusQuarterTurn x + -torusCenter = perpJ (x + -torusCenter) := by
    dsimp only [torusQuarterTurn]
    rw [add_comm torusCenter (perpJ (x - torusCenter)), add_assoc, add_neg_cancel, add_zero]
    rfl
  have hF (t : ℝ) (ht : 0 ≤ t) (a : R2) :
      (S.translate (-torusCenter)).forward t (perpJ a) =
        perpJ ((S.translate (-torusCenter)).forward t a) := by
    change S.forward t (perpJ a - -torusCenter) + -torusCenter =
      perpJ (S.forward t (a - -torusCenter) + -torusCenter)
    rw [harg, hS.forward t ht, hshift]
  have hG (t : ℝ) (a : R2) :
      (S.translate (-torusCenter)).backward t (perpJ a) =
        perpJ ((S.translate (-torusCenter)).backward t a) := by
    change S.backward t (perpJ a - -torusCenter) + -torusCenter =
      perpJ (S.backward t (a - -torusCenter) + -torusCenter)
    rw [harg, hS.backward, hshift]
  have hresult : ∃ E : GlobalPlanarEulerParticleSystem (fun x => wc (x - -torusCenter)),
      IsOriginFourfoldGlobalPlanarEulerParticleSystem E :=
    ⟨S.translate (-torusCenter), ⟨hF, hG⟩⟩
  have he : (fun x => wc (x - -torusCenter)) = w := by
    funext x
    simp only [wc, sub_neg_eq_add, add_sub_cancel_right]
  exact he ▸ hresult

namespace IsOriginFourfoldGlobalPlanarEulerParticleSystem

variable {w : R2 → ℝ} {S : GlobalPlanarEulerParticleSystem w}
    (hS : IsOriginFourfoldGlobalPlanarEulerParticleSystem S)

include hS

theorem vorticity (hwrot : ∀ x, w (perpJ x) = w x) (t : ℝ) (x : R2) :
    S.vorticity t (perpJ x) = S.vorticity t x := by
  change w (S.backward t (perpJ x)) = w (S.backward t x)
  rw [hS.backward, hwrot]

theorem velocity (hwrot : ∀ x, w (perpJ x) = w x) (t : ℝ) (x : R2) :
    S.velocity t (perpJ x) = perpJ (S.velocity t x) := by
  rw [S.selfconsistent, S.selfconsistent]
  apply planarKernelVelocity_perpJ kernelK_perpJ
  intro y
  rw [hS.backward, hwrot]

end IsOriginFourfoldGlobalPlanarEulerParticleSystem

end Euler2D

end
