module

public import RequestProject.Euler.BanachFixedGraphBlockFlattening

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section

open scoped ContDiff

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_fixedGraph_flattening_of_uniform_invariance
    {F : E → E} {P : E →L[ℝ] E} {ρ r : ℝ} {x : E → ℕ → E}
    (hg : IsLocalWeightedBackwardGraph F P ρ r x) (hρ : 1 ≤ ρ) (hr : 0 < r)
    (hP : ∀ v, P (P v) = P v)
    (T : E → E) (hT : ContDiffAt ℝ 2 T 0) (hT0 : T 0 = 0)
    (A : E →L[ℝ] E) (hTA : HasFDerivAt T A 0) (hcomm : A.comp P = P.comp A)
    {d H : ℝ} (hd : 0 < d) (hdr : d ≤ r / 2) (hH : 0 < H)
    (hquad : ∀ α, P α = α → ‖α‖ ≤ d → ∀ β, P β = β → ‖β‖ ≤ d →
      ‖(x α 0 - α) - (x β 0 - β)‖ ≤ H * (‖α‖ + ‖β‖) * ‖α - β‖)
    (hinv : ∀ {r' : ℝ}, 0 < r' → ∀ y : E → ℕ → E,
      IsLocalWeightedBackwardGraph F P ρ r' y →
        ∃ η > 0, η ≤ r' / 2 ∧ ∀ α, P α = α → ‖α‖ ≤ η →
          ‖P (T (y α 0))‖ ≤ r' / 2 ∧ y (P (T (y α 0))) = (fun n => T (y α n))) :
    ∃ C > 0, ∃ s > 0, s ≤ d ∧ ∀ α w, P α = α → P w = 0 → ‖α‖ + ‖w‖ ≤ s →
      let g := fun v => x v 0 - v
      let z := α + g α + w
      ‖P (T z) - A α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 ∧
      ‖(T z - P (T z)) - g (P (T z)) - A w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖ := by
  obtain ⟨η, hη, _, hInv⟩ := hinv hr x hg
  exact exists_fixed_backwardGraph_block_flattened_bounds hg hρ hr hP T hT hT0 A hTA hcomm
    hd hdr hH hη hquad hInv

end Euler2D

end
