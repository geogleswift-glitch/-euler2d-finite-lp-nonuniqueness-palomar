module

public import RequestProject.Euler.CircularFiniteOuterInteractionRow

/-! The actual periodic label coefficient has the same two interaction
powers in the unchanged current clock, with an additional R^8 factor. -/

@[expose] public section

set_option maxHeartbeats 1800000

noncomputable section

namespace Euler2D

theorem torus_inner_current_clock_identity {A₀ b R ρ : ℝ}
    (hA : A₀ ≠ 0) (hb : b ≠ 0) (hR : R ≠ 0) (hρ : ρ ≠ 0)
    {j l k : ℕ} (hjl : j ≤ l) (hlk : l ≤ k) :
    (ampScale A₀ b l * radScale R ρ j ^ 2 * radScale R ρ l ^ 6) / ampScale A₀ b k =
      radScale R ρ j ^ 8 * b ^ (k - l) * ρ ^ (6 * (l - j)) := by
  have hrj : radScale R ρ j ≠ 0 := by unfold radScale; exact mul_ne_zero hR (pow_ne_zero _ hρ)
  calc
    _ = radScale R ρ j ^ 8 *
        ((ampScale A₀ b l * (radScale R ρ l / radScale R ρ j) ^ 6) / ampScale A₀ b k) := by
      field_simp [hrj]
      <;> ring
    _ = _ := by rw [inner_contour_current_clock_identity hA hb hR hρ hjl hlk]; ring

theorem torus_outer_current_clock_identity {A₀ b R ρ : ℝ}
    (hA : A₀ ≠ 0) (hb : b ≠ 0) (hR : R ≠ 0) (hρ : ρ ≠ 0)
    {l j k : ℕ} (hlj : l ≤ j) (hlk : l ≤ k) :
    (ampScale A₀ b l * radScale R ρ j ^ 2 * radScale R ρ l ^ 6) / ampScale A₀ b k =
      radScale R ρ l ^ 8 * b ^ (k - l) * ρ ^ (2 * (j - l)) := by
  have hrl : radScale R ρ l ≠ 0 := by unfold radScale; exact mul_ne_zero hR (pow_ne_zero _ hρ)
  calc
    _ = radScale R ρ l ^ 8 *
        ((ampScale A₀ b l * (radScale R ρ j / radScale R ρ l) ^ 2) / ampScale A₀ b k) := by
      field_simp [hrl]
      <;> ring
    _ = _ := by rw [outer_contour_current_clock_identity hA hb hR hρ hlj hlk]; ring

theorem torus_inner_current_clock_le {A₀ b R ρ : ℝ}
    (hA : A₀ ≠ 0) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {j l k : ℕ} (hjl : j ≤ l) (hlk : l ≤ k) :
    (ampScale A₀ b l * radScale R ρ j ^ 2 * radScale R ρ l ^ 6) / ampScale A₀ b k ≤
      R ^ 8 * b ^ (k - l) * ρ ^ (6 * (l - j)) := by
  rw [torus_inner_current_clock_identity hA hb.ne' hR.ne' hρ.ne' hjl hlk]
  have hjR : radScale R ρ j ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hj8 : radScale R ρ j ^ 8 ≤ R ^ 8 :=
    pow_le_pow_left₀ (radScale_pos hR hρ j).le hjR 8
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hj8 (pow_pos hb _).le)
    (pow_pos hρ _).le

theorem torus_outer_current_clock_le {A₀ b R ρ : ℝ}
    (hA : A₀ ≠ 0) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {l j k : ℕ} (hlj : l ≤ j) (hlk : l ≤ k) :
    (ampScale A₀ b l * radScale R ρ j ^ 2 * radScale R ρ l ^ 6) / ampScale A₀ b k ≤
      R ^ 8 * b ^ (k - l) * ρ ^ (2 * (j - l)) := by
  rw [torus_outer_current_clock_identity hA hb.ne' hR.ne' hρ.ne' hlj hlk]
  have hlR : radScale R ρ l ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hl8 : radScale R ρ l ^ 8 ≤ R ^ 8 :=
    pow_le_pow_left₀ (radScale_pos hR hρ l).le hlR 8
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl8 (pow_pos hb _).le)
    (pow_pos hρ _).le

end Euler2D

end
