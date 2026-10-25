module

public import RequestProject.Euler.BanachSequencePastGreen
public import RequestProject.Euler.BanachSequenceGreenIdentity

/-! The actual causal Green operator has zero initial unstable
coordinate and solves the expanding weighted backward recurrence. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology
open scoped BoundedContinuousFunction

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem unstableSequenceGreenTermCLM_apply (ρ a : ℝ) (k : ℕ) (f : ℕ →ᵇ E) (n : ℕ) :
    unstableSequenceGreenTermCLM E ρ a k f n =
      if k < n then ((-a⁻¹) * (ρ / a) ^ k) • f (n - k) else 0 := by
  change ((-a⁻¹) * (ρ / a) ^ k) • natSequencePastShiftCLM E k f n = _
  rw [natSequencePastShiftCLM_apply]
  split_ifs <;> simp

theorem hasSum_unstableSequenceGreen_apply {ρ a : ℝ}
    (hρ : 0 < ρ) (hρa : ρ < a) (f : ℕ →ᵇ E) (n : ℕ) :
    HasSum (fun k : ℕ => if k < n then ((-a⁻¹) * (ρ / a) ^ k) • f (n - k) else 0)
      (unstableSequenceGreenCLM E ρ a f n) := by
  let ev : ((ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E)) →L[ℝ] E :=
    (natSequenceEvalCLM E n).comp (ContinuousLinearMap.apply ℝ (ℕ →ᵇ E) f)
  have h := ev.hasSum (summable_unstableSequenceGreenTermCLM (E := E) hρ hρa).hasSum
  have hterm : (fun k : ℕ => ev (unstableSequenceGreenTermCLM E ρ a k)) =
      (fun k : ℕ => if k < n then ((-a⁻¹) * (ρ / a) ^ k) • f (n - k) else 0) := by
    funext k
    change unstableSequenceGreenTermCLM E ρ a k f n = _
    exact unstableSequenceGreenTermCLM_apply ρ a k f n
  have hvalue : ev (∑' k : ℕ, unstableSequenceGreenTermCLM E ρ a k) =
      unstableSequenceGreenCLM E ρ a f n := rfl
  rw [hterm, hvalue] at h
  exact h

theorem unstableSequenceGreenCLM_zero {ρ a : ℝ}
    (hρ : 0 < ρ) (hρa : ρ < a) (f : ℕ →ᵇ E) : unstableSequenceGreenCLM E ρ a f 0 = 0 := by
  have h := (hasSum_unstableSequenceGreen_apply hρ hρa f 0).tsum_eq.symm
  simpa only [Nat.not_lt_zero, ite_false, tsum_zero] using h

theorem unstableSequenceGreenCLM_recurrence {ρ a : ℝ}
    (hρ : 0 < ρ) (hρa : ρ < a) (f : ℕ →ᵇ E) (n : ℕ) :
    unstableSequenceGreenCLM E ρ a f (n + 1) =
      (ρ / a) • unstableSequenceGreenCLM E ρ a f n - a⁻¹ • f (n + 1) := by
  let v : ℕ → ℕ → E := fun m k => if k < m then ((-a⁻¹) * (ρ / a) ^ k) • f (m - k) else 0
  let B : E →L[ℝ] E := (ρ / a) • ContinuousLinearMap.id ℝ E
  have hs (m : ℕ) : HasSum (v m) (unstableSequenceGreenCLM E ρ a f m) :=
    hasSum_unstableSequenceGreen_apply hρ hρa f m
  have he (k : ℕ) : v (n + 1) (k + 1) = B (v n k) := by
    dsimp only [v]
    by_cases hk : k < n
    · rw [if_pos (by omega : k + 1 < n + 1), if_pos hk]
      have hi : n + 1 - (k + 1) = n - k := by omega
      rw [hi]
      change ((-a⁻¹) * (ρ / a) ^ (k + 1)) • f (n - k) =
        (ρ / a) • (((-a⁻¹) * (ρ / a) ^ k) • f (n - k))
      rw [smul_smul, pow_succ]
      congr 1
      ring
    · rw [if_neg (by omega : ¬k + 1 < n + 1), if_neg hk, map_zero]
  have htail : (∑' k : ℕ, v (n + 1) (k + 1)) = B (unstableSequenceGreenCLM E ρ a f n) := by
    calc
      _ = ∑' k : ℕ, B (v n k) := tsum_congr he
      _ = _ := (B.hasSum (hs n)).tsum_eq
  have hhead : v (n + 1) 0 = (-a⁻¹) • f (n + 1) := by
    simp only [v, Nat.zero_lt_succ, ite_true, pow_zero, mul_one, Nat.sub_zero]
  calc
    _ = ∑' k : ℕ, v (n + 1) k := (hs (n + 1)).tsum_eq.symm
    _ = v (n + 1) 0 + ∑' k : ℕ, v (n + 1) (k + 1) := (hs (n + 1)).summable.tsum_eq_zero_add
    _ = (-a⁻¹) • f (n + 1) + B (unstableSequenceGreenCLM E ρ a f n) := by rw [hhead, htail]
    _ = _ := by
      change (-a⁻¹) • f (n + 1) + (ρ / a) • unstableSequenceGreenCLM E ρ a f n = _
      module

end Euler2D

end
