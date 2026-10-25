module

public import Mathlib

/-! A finite horizon at which a capture lower envelope crosses the
section, with bounded one-step overshoot and its logarithmic time. -/

@[expose] public section

set_option maxHeartbeats 1600000

noncomputable section

namespace Euler2D

theorem exists_capture_finite_horizon {lam a δ : ℝ}
    (hLam : 1 < lam) (ha : 0 < a) (haδ : a < δ) :
    ∃ N : ℕ, 0 < N ∧ δ < (3 / 4 : ℝ) * a * lam ^ N ∧
      a * lam ^ N ≤ (4 / 3 : ℝ) * lam * δ ∧
      (N : ℝ) ≤ Real.log ((4 / 3 : ℝ) * δ / a) / Real.log lam + 1 := by
  have hl0 : 0 < lam := zero_lt_one.trans hLam
  have hδ : 0 < δ := ha.trans haδ
  have hx : 1 ≤ (4 / 3 : ℝ) * δ / a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith only [haδ, hδ]
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hx hLam
  refine ⟨n + 1, Nat.succ_pos n, ?_, ?_, ?_⟩
  · have hh := (div_lt_iff₀ ha).mp hn'
    nlinarith only [hh]
  · have hh := (le_div_iff₀ ha).mp hn
    rw [pow_succ]
    have hmul := mul_le_mul_of_nonneg_right hh hl0.le
    nlinarith only [hmul]
  · have hlog : (n : ℝ) * Real.log lam ≤ Real.log ((4 / 3 : ℝ) * δ / a) := by
      have hh := Real.log_le_log (pow_pos hl0 n) hn
      rwa [Real.log_pow] at hh
    have hnlog := (le_div_iff₀ (Real.log_pos hLam)).mpr hlog
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hnlog]

theorem capture_first_section_log_bounds {E : Type*} [NormedAddCommGroup E]
    (v : ℕ → E) {lam δ : ℝ} (hLam : 1 < lam) (ha : 0 < ‖v 0‖)
    (haδ : ‖v 0‖ < δ) {n : ℕ}
    (hexit : δ ≤ ‖v n‖) (hfirst : ∀ j < n, ‖v j‖ < δ)
    (hlower : ∀ j ≤ n, (3 / 4 : ℝ) * ‖v 0‖ * lam ^ j ≤ ‖v j‖)
    (hupper : ‖v n‖ ≤ (5 / 4 : ℝ) * ‖v 0‖ * lam ^ n) :
    Real.log (δ / ((5 / 4 : ℝ) * ‖v 0‖)) / Real.log lam ≤ (n : ℝ) ∧
      (n : ℝ) < Real.log (δ / ((3 / 4 : ℝ) * ‖v 0‖)) / Real.log lam + 1 := by
  have hl0 : 0 < lam := zero_lt_one.trans hLam
  have hlog : 0 < Real.log lam := Real.log_pos hLam
  have hδ : 0 < δ := ha.trans haδ
  have hn : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hh
    subst n
    exact (not_le.mpr haδ) hexit
  constructor
  · have he : δ / ((5 / 4 : ℝ) * ‖v 0‖) ≤ lam ^ n :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hexit, hupper])
    have hh := Real.log_le_log (by positivity : 0 < δ / ((5 / 4 : ℝ) * ‖v 0‖)) he
    rw [Real.log_pow] at hh
    exact (div_le_iff₀ hlog).mpr hh
  · have hj : n - 1 < n := Nat.sub_lt hn (by decide)
    have hh : lam ^ (n - 1) < δ / ((3 / 4 : ℝ) * ‖v 0‖) :=
      (lt_div_iff₀ (by positivity)).mpr (by
        have hh₁ := hlower (n - 1) hj.le
        have hh₂ := hfirst (n - 1) hj
        nlinarith only [hh₁, hh₂])
    have hhlog := Real.log_lt_log (pow_pos hl0 _) hh
    rw [Real.log_pow] at hhlog
    have hpred := (lt_div_iff₀ hlog).mpr hhlog
    have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel hn).symm
    rw [hcast]
    linarith only [hpred]

end Euler2D

end
