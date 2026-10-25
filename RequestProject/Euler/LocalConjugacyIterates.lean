module

public import RequestProject.Euler.BanachFixedPointIterates

@[expose] public section

noncomputable section

open Filter Topology

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Type*}

theorem eventually_conjugacy_iterates {F : E → E} {G : B → B} (Φ : E → B)
    (hF0 : F 0 = 0) (hf : ContDiffAt ℝ 1 F 0)
    (hconj : ∀ᶠ z : E in 𝓝 0, Φ (F z) = G (Φ z)) (m : ℕ) :
    ∀ᶠ z : E in 𝓝 0, Φ (F^[m] z) = G^[m] (Φ z) := by
  induction m with
  | zero => exact Filter.Eventually.of_forall (fun _ => rfl)
  | succ m ih =>
    have ht : Tendsto F^[m] (𝓝 0) (𝓝 0) := by
      have hh : Tendsto F^[m] (𝓝 0) (𝓝 (F^[m] 0)) :=
        (contDiffAt_iterate_zero hF0 hf m).continuousAt
      rwa [iterate_zero_of_map_zero hF0 m] at hh
    filter_upwards [ht hconj, ih] with z hz hi
    simpa only [Function.iterate_succ_apply'] using hz.trans (congrArg G hi)

end Euler2D

end
