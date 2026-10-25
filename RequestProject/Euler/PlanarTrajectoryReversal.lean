module

public import RequestProject.Euler.PlanarLogFlowSelection
public import RequestProject.Euler.InverseLogFlowCompactness

/-! Reversal of genuine planar velocities and particle curves. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

def reversePlanarVelocity (S : ℝ) (v : ℝ → R2 → R2) : ℝ → R2 → R2 :=
  fun t x => -v (S - t) x

theorem continuous_reversePlanarVelocity (S : ℝ) {v : ℝ → R2 → R2}
    (hv : Continuous (Function.uncurry v)) :
    Continuous (Function.uncurry (reversePlanarVelocity S v)) :=
  (hv.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)).neg

theorem isBoundedLipschitzVelocity_reverse (S : ℝ) {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) :
    IsBoundedLipschitzVelocity (reversePlanarVelocity S v) K M := by
  refine ⟨continuous_reversePlanarVelocity S hv.continuous, ?_, ?_⟩
  · intro t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [reversePlanarVelocity, dist_eq_norm, neg_sub_neg, norm_sub_rev] using
      (hv.lipschitz (S - t)).dist_le_mul x y
  · intro t x
    simpa only [reversePlanarVelocity, norm_neg] using hv.norm_le (S - t) x

theorem logMod_reversePlanarVelocity (S : ℝ) {v : ℝ → R2 → R2} {C : ℝ≥0}
    (hv : ∀ t x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v t x - v t y‖ ≤ (C : ℝ) * logFlowModulus ‖x - y‖) :
    ∀ t x y, ‖x - y‖ ≤ 1 / 2 →
      ‖reversePlanarVelocity S v t x - reversePlanarVelocity S v t y‖ ≤
        (C : ℝ) * logFlowModulus ‖x - y‖ := by
  intro t x y hxy
  simpa only [reversePlanarVelocity, neg_sub_neg, norm_sub_rev] using hv (S - t) x y hxy

theorem tendstoUniformly_reversePlanarVelocity (S : ℝ)
    {vn : ℕ → ℝ → R2 → R2} {v : ℝ → R2 → R2}
    (h : TendstoUniformly (fun n (p : ℝ × R2) => vn n p.1 p.2) (Function.uncurry v) atTop) :
    TendstoUniformly (fun n (p : ℝ × R2) => reversePlanarVelocity S (vn n) p.1 p.2)
      (Function.uncurry (reversePlanarVelocity S v)) atTop :=
  uniformContinuous_neg.comp_tendstoUniformly (h.comp (fun p : ℝ × R2 => (S - p.1, p.2)))

theorem hasDerivAt_reverse_particleCurve {S : ℝ} {v : ℝ → R2 → R2} {X : ℝ → R2}
    (hX : ∀ t ∈ Icc (0 : ℝ) S, HasDerivAt X (v t (X t)) t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) S) :
    HasDerivAt (fun t => X (S - t))
      (reversePlanarVelocity S v s (X (S - s))) s := by
  have ht : S - s ∈ Icc (0 : ℝ) S := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  simpa only [reversePlanarVelocity, Function.comp_def, zero_sub, neg_one_smul] using
    (hX (S - s) ht).scomp s ((hasDerivAt_const s S).sub (hasDerivAt_id s))

theorem reversePlanarVelocity_reverse (S : ℝ) (v : ℝ → R2 → R2) :
    reversePlanarVelocity S (reversePlanarVelocity S v) = v := by
  funext t x
  simp only [reversePlanarVelocity, neg_neg]
  congr 1
  ring

end Euler2D

end
