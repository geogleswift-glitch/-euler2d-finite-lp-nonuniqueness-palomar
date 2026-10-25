module

public import RequestProject.Euler.BanachBackwardGraphUniformCommutingInvariance

/-! A common local bound and single-return covariance suffice for
invariance of the same double-return weighted backward graph. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric

namespace Euler2D
namespace IsLocalWeightedBackwardGraph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_uniform_local_family_invariant_radius_of_double_return
    {F : E → E} {P : E →L[ℝ] E} {ρ r : ℝ} {x : E → ℕ → E}
    (h : IsLocalWeightedBackwardGraph (banachDoubleReturn F) P ρ r x)
    (hρ : 1 ≤ ρ) (hr : 0 < r) (hP : ∀ v, P (P v) = P v)
    (hF0 : F 0 = 0) (hFc : ContinuousAt F 0)
    {ι : Type*} (T : ι → E → E) {C : ℝ} (hC : 0 < C)
    (hlocal : ∀ᶠ v in 𝓝 (0 : E), ∀ i, ‖T i v‖ ≤ C * ‖v‖ ∧ F (T i v) = T i (F v)) :
    ∃ η > 0, η ≤ r / 2 ∧ ∀ i ξ, P ξ = ξ → ‖ξ‖ ≤ η →
      ‖P (T i (x ξ 0))‖ ≤ r / 2 ∧
      x (P (T i (x ξ 0))) = (fun n => T i (x ξ n)) := by
  have hlocalF : ∀ᶠ v in 𝓝 (0 : E), ∀ i,
      ‖T i (F v)‖ ≤ C * ‖F v‖ ∧ F (T i (F v)) = T i (F (F v)) := by
    have hnear : ∀ᶠ z in 𝓝 (F 0), ∀ i,
        ‖T i z‖ ≤ C * ‖z‖ ∧ F (T i z) = T i (F z) := by
      rw [hF0]
      exact hlocal
    exact hFc.eventually hnear
  apply h.exists_uniform_commuting_family_invariant_radius hρ hr hP T hC
  filter_upwards [hlocal, hlocalF] with v hv hFv
  intro i
  refine ⟨(hv i).1, ?_⟩
  change F (F (T i v)) = T i (F (F v))
  rw [(hv i).2, (hFv i).2]

end IsLocalWeightedBackwardGraph
end Euler2D

end
