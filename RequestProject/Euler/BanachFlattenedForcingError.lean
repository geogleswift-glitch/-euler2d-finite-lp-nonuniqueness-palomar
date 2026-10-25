module

public import RequestProject.Euler.BanachQuadraticGraphFlattening

/-! Perturbing the actual return value has a controlled effect on the
flattened coordinates. Only the proved local quadratic Lipschitz graph
bound is used; no smoothness of that graph is assumed. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Set Metric

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_flattenedCoordinate_sub_le
    (P : E →L[ℝ] E) (hP : ∀ v, P (P v) = P v) (g : E → E) {r H : ℝ}
    (hr : 0 ≤ r) (hH : 0 ≤ H)
    (hglip : ∀ α, P α = α → ‖α‖ ≤ r / 2 → ∀ β, P β = β → ‖β‖ ≤ r / 2 →
      ‖g α - g β‖ ≤ H * (‖α‖ + ‖β‖) * ‖α - β‖)
    (x y : E) (hx : ‖P x‖ ≤ r / 2) (hy : ‖P y‖ ≤ r / 2) :
    ‖(y - P y - g (P y)) - (x - P x - g (P x))‖ ≤
      (1 + ‖P‖ + H * r * ‖P‖) * ‖y - x‖ := by
  have hgg : ‖g (P y) - g (P x)‖ ≤ H * r * ‖P‖ * ‖y - x‖ := by
    calc
      _ ≤ H * (‖P y‖ + ‖P x‖) * ‖P y - P x‖ := hglip _ (hP _) hy _ (hP _) hx
      _ ≤ H * r * ‖P y - P x‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : ‖P y‖ + ‖P x‖ ≤ r) hH) (norm_nonneg _)
      _ = H * r * ‖P (y - x)‖ := by rw [P.map_sub]
      _ ≤ H * r * (‖P‖ * ‖y - x‖) :=
        mul_le_mul_of_nonneg_left (P.le_opNorm _) (mul_nonneg hH hr)
      _ = _ := by ring
  have he : (y - P y - g (P y)) - (x - P x - g (P x)) =
      (y - x) - P (y - x) - (g (P y) - g (P x)) := by rw [P.map_sub]; abel
  rw [he]
  calc
    _ ≤ ‖y - x‖ + ‖P (y - x)‖ + ‖g (P y) - g (P x)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ‖y - x‖ + ‖P‖ * ‖y - x‖ + H * r * ‖P‖ * ‖y - x‖ :=
      add_le_add (add_le_add le_rfl (P.le_opNorm _)) hgg
    _ = _ := by ring

theorem flattenedReturn_bounds_of_return_error
    (P L : E →L[ℝ] E) (hP : ∀ v, P (P v) = P v) (g : E → E) {r H : ℝ}
    (hr : 0 ≤ r) (hH : 0 ≤ H)
    (hglip : ∀ α, P α = α → ‖α‖ ≤ r / 2 → ∀ β, P β = β → ‖β‖ ≤ r / 2 →
      ‖g α - g β‖ ≤ H * (‖α‖ + ‖β‖) * ‖α - β‖)
    (x y α w : E) {C η : ℝ}
    (hx : ‖P x‖ ≤ r / 2) (hy : ‖P y‖ ≤ r / 2) (herror : ‖y - x‖ ≤ η)
    (hu : ‖P x - L α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2)
    (hw : ‖(x - P x) - g (P x) - L w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖) :
    ‖P y - L α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 + ‖P‖ * η ∧
    ‖(y - P y) - g (P y) - L w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖ +
      (1 + ‖P‖ + H * r * ‖P‖) * η := by
  constructor
  · calc
      _ ≤ ‖P x - L α‖ + ‖P y - P x‖ := by
        have he : P y - L α = (P x - L α) + (P y - P x) := by abel
        rw [he]
        exact norm_add_le _ _
      _ ≤ C * (‖α‖ + ‖w‖) ^ 2 + ‖P‖ * η := add_le_add hu (by
        rw [← P.map_sub]
        exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left herror (norm_nonneg P)))
  · have hflat := norm_flattenedCoordinate_sub_le P hP g hr hH hglip x y hx hy
    calc
      _ ≤ ‖(x - P x) - g (P x) - L w‖ +
          ‖(y - P y - g (P y)) - (x - P x - g (P x))‖ := by
        have he : (y - P y) - g (P y) - L w = ((x - P x) - g (P x) - L w) +
            ((y - P y - g (P y)) - (x - P x - g (P x))) := by abel
        rw [he]
        exact norm_add_le _ _
      _ ≤ C * (‖α‖ + ‖w‖) * ‖w‖ + (1 + ‖P‖ + H * r * ‖P‖) * η :=
        add_le_add hw (hflat.trans (mul_le_mul_of_nonneg_left herror (by positivity)))

end Euler2D

end
