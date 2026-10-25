module

public import RequestProject.Euler.BanachSequenceGreen

/-! The actual sequence Green operator solves the weighted backward
recurrence. Its pointwise series and recurrence follow from genuine
operator-norm convergence, not from a stipulated inverse property. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology
open scoped BoundedContinuousFunction

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def natSequenceEvalCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    (ℕ →ᵇ E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => f n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by
      change ‖f n‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using BoundedContinuousFunction.norm_coe_le_norm f n)

variable [CompleteSpace E]

theorem hasSum_stableSequenceGreen_apply {ρ β C : ℝ}
    (hρ : 0 < ρ) (hβ0 : 0 ≤ β) (hβρ : β < ρ) (A : E →L[ℝ] E)
    (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * β ^ k) (f : ℕ →ᵇ E) (n : ℕ) :
    HasSum (fun k : ℕ => (ρ⁻¹) ^ (k + 1) • (A ^ k) (f (n + (k + 1))))
      (stableSequenceGreenCLM ρ A f n) := by
  let ev : ((ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E)) →L[ℝ] E :=
    (natSequenceEvalCLM E n).comp (ContinuousLinearMap.apply ℝ (ℕ →ᵇ E) f)
  have h := ev.hasSum (summable_stableSequenceGreenTermCLM hρ hβ0 hβρ A hA).hasSum
  have hterm : (fun k : ℕ => ev (stableSequenceGreenTermCLM ρ A k)) =
      (fun k : ℕ => (ρ⁻¹) ^ (k + 1) • (A ^ k) (f (n + (k + 1)))) := by
    funext k
    change stableSequenceGreenTermCLM ρ A k f n = _
    exact stableSequenceGreenTermCLM_apply ρ A k f n
  have hvalue : ev (∑' k : ℕ, stableSequenceGreenTermCLM ρ A k) = stableSequenceGreenCLM ρ A f n := rfl
  rw [hterm, hvalue] at h
  exact h

theorem stableSequenceGreenCLM_apply {ρ β C : ℝ}
    (hρ : 0 < ρ) (hβ0 : 0 ≤ β) (hβρ : β < ρ) (A : E →L[ℝ] E)
    (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * β ^ k) (f : ℕ →ᵇ E) (n : ℕ) :
    stableSequenceGreenCLM ρ A f n =
      ∑' k : ℕ, (ρ⁻¹) ^ (k + 1) • (A ^ k) (f (n + (k + 1))) :=
  (hasSum_stableSequenceGreen_apply hρ hβ0 hβρ A hA f n).tsum_eq.symm

theorem stableSequenceGreenCLM_recurrence {ρ β C : ℝ}
    (hρ : 0 < ρ) (hβ0 : 0 ≤ β) (hβρ : β < ρ) (A : E →L[ℝ] E)
    (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * β ^ k) (f : ℕ →ᵇ E) (n : ℕ) :
    stableSequenceGreenCLM ρ A f n =
      ρ⁻¹ • (A (stableSequenceGreenCLM ρ A f (n + 1)) + f (n + 1)) := by
  let v : ℕ → ℕ → E := fun m k => (ρ⁻¹) ^ (k + 1) • (A ^ k) (f (m + (k + 1)))
  let B : E →L[ℝ] E := ρ⁻¹ • A
  have hs (m : ℕ) : HasSum (v m) (stableSequenceGreenCLM ρ A f m) :=
    hasSum_stableSequenceGreen_apply hρ hβ0 hβρ A hA f m
  have he (k : ℕ) : v n (k + 1) = B (v (n + 1) k) := by
    dsimp only [v]
    rw [show A ^ (k + 1) = A * A ^ k from pow_succ' A k, ContinuousLinearMap.mul_apply]
    have hi : n + (k + 1 + 1) = n + 1 + (k + 1) := by omega
    rw [hi]
    change (ρ⁻¹) ^ (k + 1 + 1) • A ((A ^ k) (f (n + 1 + (k + 1)))) =
      ρ⁻¹ • A ((ρ⁻¹) ^ (k + 1) • (A ^ k) (f (n + 1 + (k + 1))))
    rw [map_smul, smul_smul, pow_succ]
    congr 1
    ring
  have htail : (∑' k : ℕ, v n (k + 1)) = B (stableSequenceGreenCLM ρ A f (n + 1)) := by
    calc
      _ = ∑' k : ℕ, B (v (n + 1) k) := tsum_congr he
      _ = _ := (B.hasSum (hs (n + 1))).tsum_eq
  have hhead : v n 0 = ρ⁻¹ • f (n + 1) := by
    dsimp only [v]
    simp only [zero_add, pow_one, pow_zero, ContinuousLinearMap.one_apply]
  calc
    _ = ∑' k : ℕ, v n k := (hs n).tsum_eq.symm
    _ = v n 0 + ∑' k : ℕ, v n (k + 1) := (hs n).summable.tsum_eq_zero_add
    _ = ρ⁻¹ • f (n + 1) + B (stableSequenceGreenCLM ρ A f (n + 1)) := by rw [hhead, htail]
    _ = _ := by
      change ρ⁻¹ • f (n + 1) + ρ⁻¹ • A (stableSequenceGreenCLM ρ A f (n + 1)) = _
      module

end Euler2D

end
