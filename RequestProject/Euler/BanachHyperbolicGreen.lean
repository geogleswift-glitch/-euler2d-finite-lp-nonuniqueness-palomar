module

public import RequestProject.Euler.BanachSequencePastGreenIdentity

/-! The stable and unstable series solve one actual backward equation
in the original Banach space. The splitting maps are bounded operators;
all recurrence identities are deduced from the convergent series. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology
open scoped BoundedContinuousFunction

namespace Euler2D

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]

theorem unstableSequenceGreenCLM_eigen {ρ a : ℝ}
    (hρ : 0 < ρ) (hρa : ρ < a) (L P : E →L[ℝ] E)
    (hLP : ∀ v, L (P v) = a • P v) (f : ℕ →ᵇ E) (n : ℕ) :
    L (unstableSequenceGreenCLM E ρ a (P.compLeftContinuousBounded ℕ f) n) =
      a • unstableSequenceGreenCLM E ρ a (P.compLeftContinuousBounded ℕ f) n := by
  let g := P.compLeftContinuousBounded ℕ f
  let t : ℕ → E := fun k => if k < n then ((-a⁻¹) * (ρ / a) ^ k) • g (n - k) else 0
  have hs : HasSum t (unstableSequenceGreenCLM E ρ a g n) :=
    hasSum_unstableSequenceGreen_apply hρ hρa g n
  have ht (k : ℕ) : L (t k) = a • t k := by
    dsimp only [t]
    split_ifs
    · change L (((-a⁻¹) * (ρ / a) ^ k) • P (f (n - k))) =
        a • (((-a⁻¹) * (ρ / a) ^ k) • P (f (n - k)))
      rw [map_smul, hLP, smul_comm]
    · rw [map_zero, smul_zero]
  have hm := L.hasSum hs
  have heq : (fun k => L (t k)) = (fun k => a • t k) := funext ht
  rw [heq] at hm
  exact hm.unique (hs.const_smul a)

theorem unstableSequenceGreenCLM_projection {ρ a : ℝ}
    (hρ : 0 < ρ) (hρa : ρ < a) (P : E →L[ℝ] E)
    (hP : ∀ v, P (P v) = P v) (f : ℕ →ᵇ E) (n : ℕ) :
    P (unstableSequenceGreenCLM E ρ a (P.compLeftContinuousBounded ℕ f) n) =
      unstableSequenceGreenCLM E ρ a (P.compLeftContinuousBounded ℕ f) n := by
  let g := P.compLeftContinuousBounded ℕ f
  let t : ℕ → E := fun k => if k < n then ((-a⁻¹) * (ρ / a) ^ k) • g (n - k) else 0
  have hs : HasSum t (unstableSequenceGreenCLM E ρ a g n) :=
    hasSum_unstableSequenceGreen_apply hρ hρa g n
  have ht (k : ℕ) : P (t k) = t k := by
    dsimp only [t]
    split_ifs
    · change P (((-a⁻¹) * (ρ / a) ^ k) • P (f (n - k))) =
        ((-a⁻¹) * (ρ / a) ^ k) • P (f (n - k))
      rw [map_smul, hP]
    · rw [map_zero]
  have hm := P.hasSum hs
  have heq : (fun k => P (t k)) = t := funext ht
  rw [heq] at hm
  exact hm.unique hs

def hyperbolicSequenceGreenCLM (ρ a : ℝ) (A : K →L[ℝ] K)
    (J : K →L[ℝ] E) (Q : E →L[ℝ] K) (P : E →L[ℝ] E) :
    (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E) :=
  (unstableSequenceGreenCLM E ρ a).comp (P.compLeftContinuousBounded ℕ) +
    (J.compLeftContinuousBounded ℕ).comp
      ((stableSequenceGreenCLM ρ A).comp (Q.compLeftContinuousBounded ℕ))

theorem hyperbolicSequenceGreenCLM_apply (ρ a : ℝ) (A : K →L[ℝ] K)
    (J : K →L[ℝ] E) (Q : E →L[ℝ] K) (P : E →L[ℝ] E) (f : ℕ →ᵇ E) (n : ℕ) :
    hyperbolicSequenceGreenCLM ρ a A J Q P f n =
      unstableSequenceGreenCLM E ρ a (P.compLeftContinuousBounded ℕ f) n +
        J (stableSequenceGreenCLM ρ A (Q.compLeftContinuousBounded ℕ f) n) := rfl

theorem hyperbolicSequenceGreenCLM_recurrence {ρ a β C : ℝ}
    (hρ : 0 < ρ) (hρa : ρ < a) (hβ0 : 0 ≤ β) (hβρ : β < ρ)
    (L : E →L[ℝ] E) (A : K →L[ℝ] K)
    (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * β ^ k)
    (J : K →L[ℝ] E) (Q : E →L[ℝ] K) (P : E →L[ℝ] E)
    (hLP : ∀ v, L (P v) = a • P v)
    (hLJ : ∀ v, L (J v) = J (A v)) (hJQ : ∀ v, J (Q v) = v - P v)
    (f : ℕ →ᵇ E) (n : ℕ) :
    ρ • hyperbolicSequenceGreenCLM ρ a A J Q P f n =
      L (hyperbolicSequenceGreenCLM ρ a A J Q P f (n + 1)) + f (n + 1) := by
  let u := unstableSequenceGreenCLM E ρ a (P.compLeftContinuousBounded ℕ f)
  let s := stableSequenceGreenCLM ρ A (Q.compLeftContinuousBounded ℕ f)
  have hu : ρ • u n = L (u (n + 1)) + P (f (n + 1)) := by
    have he := unstableSequenceGreenCLM_eigen hρ hρa L P hLP f (n + 1)
    have hr := unstableSequenceGreenCLM_recurrence hρ hρa (P.compLeftContinuousBounded ℕ f) n
    change u (n + 1) = (ρ / a) • u n - a⁻¹ • P (f (n + 1)) at hr
    change L (u (n + 1)) = a • u (n + 1) at he
    rw [he, hr, smul_sub, smul_smul, smul_smul]
    have ha : a ≠ 0 := (hρ.trans hρa).ne'
    rw [show a * (ρ / a) = ρ by field_simp, mul_inv_cancel₀ ha, one_smul]
    module
  have hs : ρ • J (s n) = L (J (s (n + 1))) + (f (n + 1) - P (f (n + 1))) := by
    have hr := stableSequenceGreenCLM_recurrence hρ hβ0 hβρ A hA
      (Q.compLeftContinuousBounded ℕ f) n
    change s n = ρ⁻¹ • (A (s (n + 1)) + Q (f (n + 1))) at hr
    rw [hr, map_smul, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, map_add, ← hLJ, hJQ]
  rw [hyperbolicSequenceGreenCLM_apply, hyperbolicSequenceGreenCLM_apply]
  change ρ • (u n + J (s n)) = L (u (n + 1) + J (s (n + 1))) + f (n + 1)
  rw [smul_add, hu, hs, L.map_add]
  abel

theorem hyperbolicSequenceGreenCLM_projection_zero {ρ a : ℝ}
    (hρ : 0 < ρ) (hρa : ρ < a) (A : K →L[ℝ] K)
    (J : K →L[ℝ] E) (Q : E →L[ℝ] K) (P : E →L[ℝ] E)
    (hPJ : ∀ v, P (J v) = 0) (f : ℕ →ᵇ E) :
    P (hyperbolicSequenceGreenCLM ρ a A J Q P f 0) = 0 := by
  rw [hyperbolicSequenceGreenCLM_apply, unstableSequenceGreenCLM_zero hρ hρa, zero_add, hPJ]

end Euler2D

end
