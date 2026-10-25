module

public import RequestProject.Euler.BanachWeightedRemainder
public import Mathlib.Topology.MetricSpace.Contracting

/-! A genuine contraction constructs the weighted nonlinear orbit
sequence, with quantitative distance from its prescribed linear source. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_weightedNonlinearSequence_fixedPoint {R : E → E} {ρ r δ : ℝ}
    (hρ : 1 ≤ ρ) (hr : 0 < r) (hδ : 0 ≤ δ) (hR : R 0 = 0)
    (hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖R x - R y‖ ≤ δ * ‖x - y‖)
    (G : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E)) (hsmall : ‖G‖ * δ ≤ 1 / 2)
    (s : ℕ →ᵇ E) (hs : ‖s‖ ≤ r / 2) :
    ∃ u : closedBall (0 : ℕ →ᵇ E) r,
      u.val = s + G (weightedSequenceRemainder hρ hr.le hδ hR hLip u) ∧
      ‖u.val‖ ≤ 2 * ‖s‖ ∧
      ‖u.val - s‖ ≤ (2 * (‖G‖ * δ)) * ‖s‖ := by
  let N := weightedSequenceRemainder hρ hr.le hδ hR hLip
  let q : ℝ≥0 := NNReal.mk (‖G‖ * δ) (mul_nonneg (norm_nonneg G) hδ)
  have hq : (q : ℝ) ≤ 1 / 2 := by
    simpa only [q, NNReal.coe_mk] using hsmall
  have hN (u : closedBall (0 : ℕ →ᵇ E) r) : ‖N u‖ ≤ δ * ‖u.val‖ :=
    norm_weightedSequenceRemainder_le hρ hr.le hδ hR hLip u
  have hbound (u : closedBall (0 : ℕ →ᵇ E) r) : ‖s + G (N u)‖ ≤ r := by
    have hu : ‖u.val‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using u.property
    calc
      _ ≤ ‖s‖ + ‖G (N u)‖ := norm_add_le _ _
      _ ≤ r / 2 + ‖G‖ * (δ * ‖u.val‖) := add_le_add hs
        ((G.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hN u) (norm_nonneg G)))
      _ = r / 2 + (q : ℝ) * ‖u.val‖ := by simp only [q, NNReal.coe_mk]; ring
      _ ≤ r / 2 + (1 / 2 : ℝ) * r := add_le_add le_rfl
        (mul_le_mul hq hu (norm_nonneg u.val) (by norm_num))
      _ = r := by ring
  let M : closedBall (0 : ℕ →ᵇ E) r → closedBall (0 : ℕ →ᵇ E) r := fun u =>
    ⟨s + G (N u), by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hbound u⟩
  have hcontract : ContractingWith q M := by
    constructor
    · change (q : ℝ) < 1
      linarith
    · apply LipschitzWith.of_dist_le_mul
      intro u v
      change dist (s + G (N u)) (s + G (N v)) ≤ (q : ℝ) * dist u.val v.val
      rw [dist_eq_norm, dist_eq_norm]
      have he : (s + G (N u)) - (s + G (N v)) = G (N u - N v) := by rw [map_sub]; abel
      rw [he]
      calc
        _ ≤ ‖G‖ * ‖N u - N v‖ := G.le_opNorm _
        _ ≤ ‖G‖ * (δ * ‖u.val - v.val‖) := mul_le_mul_of_nonneg_left
          (norm_weightedSequenceRemainder_sub_le hρ hr.le hδ hR hLip u v) (norm_nonneg G)
        _ = _ := by simp only [q, NNReal.coe_mk]; ring
  letI : CompleteSpace (closedBall (0 : ℕ →ᵇ E) r) := isClosed_closedBall.completeSpace_coe
  letI : Nonempty (closedBall (0 : ℕ →ᵇ E) r) := ⟨⟨0, mem_closedBall_self hr.le⟩⟩
  let u := ContractingWith.fixedPoint M hcontract
  have hfix : M u = u := hcontract.fixedPoint_isFixedPt
  have heq : u.val = s + G (N u) := (congrArg (fun z : closedBall (0 : ℕ →ᵇ E) r => z.val) hfix).symm
  have hu0 : 0 ≤ ‖u.val‖ := norm_nonneg _
  have hnorm : ‖u.val‖ ≤ 2 * ‖s‖ := by
    have h1 : ‖u.val‖ ≤ ‖s‖ + (q : ℝ) * ‖u.val‖ := by
      calc
        _ = ‖s + G (N u)‖ := congrArg norm heq
        _ ≤ ‖s‖ + ‖G (N u)‖ := norm_add_le _ _
        _ ≤ ‖s‖ + ‖G‖ * (δ * ‖u.val‖) := add_le_add le_rfl
          ((G.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hN u) (norm_nonneg G)))
        _ = _ := by simp only [q, NNReal.coe_mk]; ring
    have h2 := mul_le_mul_of_nonneg_right hq hu0
    nlinarith
  refine ⟨u, heq, hnorm, ?_⟩
  have herr : u.val - s = G (N u) := by rw [heq]; abel
  rw [herr]
  calc
    _ ≤ ‖G‖ * (δ * ‖u.val‖) :=
      (G.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hN u) (norm_nonneg G))
    _ = (q : ℝ) * ‖u.val‖ := by simp only [q, NNReal.coe_mk]; ring
    _ ≤ (q : ℝ) * (2 * ‖s‖) := mul_le_mul_of_nonneg_left hnorm q.coe_nonneg
    _ = _ := by simp only [q, NNReal.coe_mk]; ring

end Euler2D

end
