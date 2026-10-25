module

public import RequestProject.Euler.BanachBackwardSequence
public import RequestProject.Euler.BanachHyperbolicGreen
public import RequestProject.Euler.BanachWeightedFixedPoint

/-! A genuine nonlinear ancient discrete orbit is constructed by a
contraction from a true C¹ map and bounded invariant splitting data.
The initial expanding coordinate is prescribed exactly, and the graph
error can be made arbitrarily small relative to that coordinate. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction ContDiff

namespace Euler2D

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]

theorem exists_banachBackwardOrbit_of_splitting
    (F : E → E) (hf : ContDiffAt ℝ 1 F 0) (hzero : F 0 = 0)
    (L : E →L[ℝ] E) (hderiv : fderiv ℝ F 0 = L)
    {ρ a β C : ℝ} (hρ : 1 < ρ) (hρa : ρ < a) (hβ0 : 0 ≤ β) (hβρ : β < ρ)
    (A : K →L[ℝ] K) (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * β ^ k)
    (J : K →L[ℝ] E) (Q : E →L[ℝ] K) (P : E →L[ℝ] E)
    (hLP : ∀ v, L (P v) = a • P v)
    (hLJ : ∀ v, L (J v) = J (A v)) (hJQ : ∀ v, J (Q v) = v - P v)
    (hPJ : ∀ v, P (J v) = 0)
    {ε rmax : ℝ} (hε : 0 < ε) (hrmax : 0 < rmax) :
    ∃ r > 0, r ≤ rmax ∧ ∀ ξ : E, P ξ = ξ → ‖ξ‖ ≤ r / 2 →
      ∃ x : ℕ → E,
        (∀ n, F (x (n + 1)) = x n) ∧
        (∀ n, x n ∈ closedBall 0 r) ∧
        (∀ n, ‖x n‖ ≤ 2 * (ρ⁻¹) ^ n * ‖ξ‖) ∧
        P (x 0) = ξ ∧ ‖x 0 - ξ‖ ≤ ε * ‖ξ‖ ∧
        Tendsto x atTop (𝓝 (0 : E)) := by
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  let G := hyperbolicSequenceGreenCLM ρ a A J Q P
  let δ : ℝ := min (1 / (2 * (‖G‖ + 1))) (ε / (2 * (‖G‖ + 1)))
  have hden : 0 < 2 * (‖G‖ + 1) := by positivity
  have hδ : 0 < δ := lt_min (div_pos zero_lt_one hden) (div_pos hε hden)
  have hd1 : δ * (2 * (‖G‖ + 1)) ≤ 1 := (le_div_iff₀ hden).mp (min_le_left _ _)
  have hdε : δ * (2 * (‖G‖ + 1)) ≤ ε := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hsmall : ‖G‖ * δ ≤ 1 / 2 := by nlinarith [norm_nonneg G]
  have herror : 2 * (‖G‖ * δ) ≤ ε := by nlinarith [norm_nonneg G]
  obtain ⟨r₁, hr₁, hLip₁⟩ := exists_closedBall_lipschitz_banachLocalRemainder hf hδ
  let r := min r₁ rmax
  have hr : 0 < r := lt_min hr₁ hrmax
  have hLip : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ‖banachLocalRemainder F x - banachLocalRemainder F y‖ ≤ δ * ‖x - y‖ := by
    intro x hx y hy
    exact hLip₁ x (closedBall_subset_closedBall (min_le_left _ _) hx)
      y (closedBall_subset_closedBall (min_le_left _ _) hy)
  have hR := banachLocalRemainder_zero hzero
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  intro ξ hξ hξr
  let s := geometricBanachSequence (ρ / a) (div_nonneg hρ0.le (hρ0.trans hρa).le)
    ((div_lt_one (hρ0.trans hρa)).mpr hρa).le ξ
  have hs : ‖s‖ = ‖ξ‖ := norm_geometricBanachSequence _ _ _ _
  have hs0 : s 0 = ξ := geometricBanachSequence_zero _ _ _ _
  have hLξ : L ξ = a • ξ := by rw [← hξ, hLP, hξ]
  have hsrec (n : ℕ) : ρ • s n = L (s (n + 1)) :=
    geometricBanachSequence_backward hρ0 hρa L ξ hLξ n
  obtain ⟨u, hfix, hunorm, huerror⟩ := exists_weightedNonlinearSequence_fixedPoint
    hρ.le hr hδ.le hR hLip G hsmall s (by rw [hs]; exact hξr)
  let y := weightedSequenceRemainder hρ.le hr.le hδ.le hR hLip u
  have heval (n : ℕ) : u.val n = s n + G y n := by
    exact congrArg (fun z : ℕ →ᵇ E => z n) hfix
  have hGrec (n : ℕ) : ρ • G y n = L (G y (n + 1)) + y (n + 1) :=
    hyperbolicSequenceGreenCLM_recurrence hρ0 hρa hβ0 hβρ L A hA J Q P hLP hLJ hJQ y n
  have hrec (n : ℕ) : ρ • u.val n = L (u.val (n + 1)) + y (n + 1) := by
    rw [heval n, heval (n + 1), smul_add, hsrec n, hGrec n, L.map_add]
    abel
  let x : ℕ → E := fun n => (ρ⁻¹) ^ n • u.val n
  have hx0 : x 0 = u.val 0 := by simp only [x, pow_zero, one_smul]
  have huBall : ‖u.val‖ ≤ r := by
    simpa only [mem_closedBall, dist_eq_norm, sub_zero] using u.property
  refine ⟨x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply unweightedBoundedSequence_backward hρ.le F u.val
    intro n
    rw [hderiv]
    exact hrec n
  · intro n
    exact weightedSequence_argument_mem_closedBall hρ.le u.val huBall n
  · intro n
    have hw := real_weight_inverse_pow_facts hρ.le n
    change ‖(ρ⁻¹) ^ n • u.val n‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw.2.1]
    calc
      _ ≤ (ρ⁻¹) ^ n * ‖u.val‖ := mul_le_mul_of_nonneg_left
        (BoundedContinuousFunction.norm_coe_le_norm u.val n) hw.2.1
      _ ≤ (ρ⁻¹) ^ n * (2 * ‖ξ‖) := mul_le_mul_of_nonneg_left
        (by simpa only [hs] using hunorm) hw.2.1
      _ = _ := by ring
  · rw [hx0, heval 0, P.map_add, hs0, hξ]
    have hz : P (G y 0) = 0 :=
      hyperbolicSequenceGreenCLM_projection_zero hρ0 hρa A J Q P hPJ y
    rw [hz, add_zero]
  · calc
      _ = ‖(u.val - s) 0‖ := by rw [hx0]; congr 1; change u.val 0 - ξ = u.val 0 - s 0; rw [hs0]
      _ ≤ ‖u.val - s‖ := BoundedContinuousFunction.norm_coe_le_norm _ 0
      _ ≤ (2 * (‖G‖ * δ)) * ‖s‖ := huerror
      _ ≤ ε * ‖ξ‖ := by rw [hs]; exact mul_le_mul_of_nonneg_right herror (norm_nonneg ξ)
  · exact tendsto_unweightedBoundedSequence hρ u.val

end Euler2D

end
