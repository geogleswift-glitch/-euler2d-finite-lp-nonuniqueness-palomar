module

public import RequestProject.Euler.ContinuousCaptureSection

/-! A joint bootstrap on every actually existing stopped interval.
Only its two continuous scalar controls enter the first-exit argument. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Set Metric

namespace Euler2D

theorem continuous_joint_bootstrap {f g : ℝ → ℝ} {D a b : ℝ}
    (hD : 0 ≤ D) (ha : 0 < a) (hb : 0 < b)
    (hf : ContinuousOn f (Icc (0 : ℝ) D)) (hg : ContinuousOn g (Icc (0 : ℝ) D))
    (hf0 : ∀ t ∈ Icc (0 : ℝ) D, 0 ≤ f t) (hg0 : ∀ t ∈ Icc (0 : ℝ) D, 0 ≤ g t)
    (hinit : f 0 < a ∧ g 0 < b)
    (himprove : ∀ d ∈ Icc (0 : ℝ) D,
      (∀ t ∈ Icc (0 : ℝ) d, f t ≤ a ∧ g t ≤ b) → f d < a ∧ g d < b) :
    ∀ t ∈ Icc (0 : ℝ) D, f t < a ∧ g t < b := by
  let y : ℝ → ℝ × ℝ := fun t => (f t / a, g t / b)
  have hy : ContinuousOn y (Icc (0 : ℝ) D) := (hf.div_const a).prodMk (hg.div_const b)
  have hnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) : ‖y t‖ = max (f t / a) (g t / b) := by
    simp only [y, Prod.norm_def, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (hf0 t ht) ha.le), abs_of_nonneg (div_nonneg (hg0 t ht) hb.le)]
  have hstart : ‖y 0‖ < 1 := by
    rw [hnorm 0 ⟨le_rfl, hD⟩, max_lt_iff]
    exact ⟨(div_lt_one ha).mpr hinit.1, (div_lt_one hb).mpr hinit.2⟩
  intro t ht
  by_contra hn
  push_neg at hn
  have hend : 1 ≤ ‖y t‖ := by
    rw [hnorm t ht]
    by_cases hfa : a ≤ f t
    · exact ((le_div_iff₀ ha).mpr (by simpa only [one_mul] using hfa)).trans (le_max_left _ _)
    · exact ((le_div_iff₀ hb).mpr (by simpa only [one_mul] using hn (lt_of_not_ge hfa))).trans (le_max_right _ _)
  obtain ⟨s, hs, hvalue, hpre⟩ := exists_first_continuous_norm_section ht.1 y
    (hy.mono (Icc_subset_Icc_right ht.2)) hstart hend
  have hsD : s ∈ Icc (0 : ℝ) D := ⟨hs.1.le, hs.2.trans ht.2⟩
  have hhistory (u : ℝ) (hu : u ∈ Icc (0 : ℝ) s) : f u ≤ a ∧ g u ≤ b := by
    have huD : u ∈ Icc (0 : ℝ) D := ⟨hu.1, hu.2.trans hsD.2⟩
    have huy : ‖y u‖ ≤ 1 := by
      rcases hu.2.lt_or_eq with hlt | heq
      · exact (hpre u ⟨hu.1, hlt⟩).le
      · simpa only [heq] using hvalue.le
    rw [hnorm u huD] at huy
    exact ⟨(div_le_one ha).mp ((le_max_left _ _).trans huy),
      (div_le_one hb).mp ((le_max_right _ _).trans huy)⟩
  have hsstrict := himprove s hsD hhistory
  have hlt : ‖y s‖ < 1 := by
    rw [hnorm s hsD, max_lt_iff]
    exact ⟨(div_lt_one ha).mpr hsstrict.1, (div_lt_one hb).mpr hsstrict.2⟩
  exact (ne_of_lt hlt) hvalue

end Euler2D

end
