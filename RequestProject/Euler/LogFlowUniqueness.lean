module

public import RequestProject.Euler.Osgood

/-!
# Uniqueness of nearby logarithmic-modulus particle trajectories

The square of the distance is differentiable even at coincidence.
Its genuine derivative inequality reduces to the proved Osgood comparison.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Real

namespace Euler2D

theorem logFlow_unique_of_nearby {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    {v : ℝ → E → E} {X Y : ℝ → E}
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (v t (X t)) t)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (v t (Y t)) t)
    (hinit : X 0 = Y 0)
    (hclose : ∀ t ∈ Icc 0 T, ‖X t - Y t‖ ≤ 1 / 2)
    (hlip : ∀ t ∈ Icc 0 T, ∀ x y : E, ‖x - y‖ ≤ 1 / 2 →
      ‖v t x - v t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    ∀ t ∈ Icc 0 T, X t = Y t := by
  let f := fun t => ‖X t - Y t‖ ^ 2
  let f' := fun t => 2 * inner ℝ (X t - Y t) (v t (X t) - v t (Y t))
  have hf (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt f (f' t) t :=
    ((hX t ht).sub (hY t ht)).norm_sq
  have hsmall (t : ℝ) (ht : t ∈ Icc 0 T) : f t ∈ Icc 0 (1 / 2) := by
    have hd := hclose t ht
    have hn := norm_nonneg (X t - Y t)
    exact ⟨sq_nonneg _, by dsimp only [f]; nlinarith⟩
  have hzero : f 0 = 0 := by simp [f, hinit]
  have hbound (t : ℝ) (ht : t ∈ Ioo 0 T) : f' t ≤ (2 * C) * logFlowModulus (f t) := by
    have htc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
    let d := ‖X t - Y t‖
    have hd : 0 ≤ d := norm_nonneg _
    have hdhalf : d ≤ 1 / 2 := hclose t htc
    have hv := hlip t htc (X t) (Y t) hdhalf
    have hi := (le_abs_self (inner ℝ (X t - Y t) (v t (X t) - v t (Y t)))).trans
      (abs_real_inner_le_norm _ _)
    have hb : f' t ≤ 2 * (d * (C * logFlowModulus d)) := by
      exact (mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hd) (by norm_num))
    change f' t ≤ 2 * C * logFlowModulus (d ^ 2)
    by_cases hz : d = 0
    · rw [hz] at hb ⊢
      simpa [logFlowModulus] using hb
    · have hlog : Real.log d ≤ 0 := Real.log_nonpos hd (by linarith)
      have hsign : 0 ≤ 2 * C * d ^ 2 * (-Real.log d) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg d))
          (neg_nonneg.mpr hlog)
      change f' t ≤ 2 * C * (d ^ 2 - d ^ 2 * Real.log (d ^ 2))
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      dsimp only [logFlowModulus] at hb
      exact hb.trans (by nlinarith only [hsign])
  have hz := eq_zero_of_logFlow_bound hT (mul_nonneg (by norm_num) hC) hf hsmall hzero hbound
  intro t ht
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (hz t ht)))

end Euler2D

end
