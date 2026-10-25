module

public import RequestProject.Euler.BanachBackwardGraphCommutingInvariance
public import RequestProject.Euler.BanachDoubleReturn

/-! Uniform graph invariance for a family of commuting maps with a
common local linear bound. The same weighted backward-orbit uniqueness
gives one radius before the family parameter is selected. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology Metric

namespace Euler2D
namespace IsLocalWeightedBackwardGraph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : E → E} {P : E →L[ℝ] E} {ρ r : ℝ} {x : E → ℕ → E}

theorem exists_uniform_commuting_family_invariant_radius
    (h : IsLocalWeightedBackwardGraph F P ρ r x) (hρ : 1 ≤ ρ) (hr : 0 < r)
    (hP : ∀ v, P (P v) = P v) {ι : Type*} (T : ι → E → E) {C : ℝ} (hC : 0 < C)
    (hlocal : ∀ᶠ z : E in 𝓝 0, ∀ i, ‖T i z‖ ≤ C * ‖z‖ ∧ F (T i z) = T i (F z)) :
    ∃ η > 0, η ≤ r / 2 ∧ ∀ i ξ, P ξ = ξ → ‖ξ‖ ≤ η →
      ‖P (T i (x ξ 0))‖ ≤ r / 2 ∧
      x (P (T i (x ξ 0))) = (fun n => T i (x ξ n)) := by
  obtain ⟨s, hs, hspec⟩ := Metric.eventually_nhds_iff.mp hlocal
  let η := min (r / 4) (min (s / 4) (r / (4 * C * (‖P‖ + 1))))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηr : η ≤ r / 2 := by
    have hh : η ≤ r / 4 := min_le_left _ _
    linarith
  refine ⟨η, hη, hηr, ?_⟩
  intro i ξ hξ hξη
  have hξr : ‖ξ‖ ≤ r / 2 := hξη.trans hηr
  have hξs : ‖ξ‖ ≤ s / 4 := hξη.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hξC : ‖ξ‖ ≤ r / (4 * C * (‖P‖ + 1)) :=
    hξη.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : 4 * C * (‖P‖ + 1) * ‖ξ‖ ≤ r := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * C * (‖P‖ + 1))).mp hξC
    nlinarith only [hh]
  have hin (n : ℕ) : dist (x ξ n) (0 : E) < s := by
    rw [dist_zero_right]
    have hn := h.norm_le ξ hξ hξr n
    have hp := (real_weight_inverse_pow_facts hρ n).2.2.1
    have hh := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 2 * ‖ξ‖)
    nlinarith
  have hyn (n : ℕ) : ‖T i (x ξ n)‖ ≤ 2 * C * ‖ξ‖ * (ρ⁻¹) ^ n := by
    calc
      _ ≤ C * ‖x ξ n‖ := (hspec (hin n) i).1
      _ ≤ C * (2 * (ρ⁻¹) ^ n * ‖ξ‖) :=
        mul_le_mul_of_nonneg_left (h.norm_le ξ hξ hξr n) hC.le
      _ = _ := by ring
  have hproj : ‖P (T i (x ξ 0))‖ ≤ r / 2 := by
    have hn : ‖T i (x ξ 0)‖ ≤ 2 * C * ‖ξ‖ := by
      simpa only [pow_zero, mul_one] using hyn 0
    calc
      _ ≤ ‖P‖ * ‖T i (x ξ 0)‖ := P.le_opNorm _
      _ ≤ ‖P‖ * (2 * C * ‖ξ‖) := mul_le_mul_of_nonneg_left hn (norm_nonneg P)
      _ ≤ r / 2 := by nlinarith [norm_nonneg P, norm_nonneg ξ]
  refine ⟨hproj, ?_⟩
  symm
  apply h.unique _ (hP _) hproj
  · intro n
    rw [(hspec (hin (n + 1)) i).2, h.backward ξ hξ hξr n]
  · intro n
    have hc : 2 * C * ‖ξ‖ ≤ r := by nlinarith [norm_nonneg P, norm_nonneg ξ]
    exact (hyn n).trans (mul_le_mul_of_nonneg_right hc (real_weight_inverse_pow_facts hρ n).2.1)
  · rfl

theorem exists_uniform_commuting_family_invariant_radius_of_double_return
    {G : E → E} (h : IsLocalWeightedBackwardGraph (banachDoubleReturn G) P ρ r x)
    (hρ : 1 ≤ ρ) (hr : 0 < r) (hP : ∀ v, P (P v) = P v)
    (hG0 : G 0 = 0) (hGc : ContinuousAt G 0)
    {ι : Type*} (T : ι → E → E) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ i v, ‖T i v‖ ≤ C * ‖v‖)
    (hcov : ∃ δ > 0, ∀ i v, ‖v‖ < δ → G (T i v) = T i (G v)) :
    ∃ η > 0, η ≤ r / 2 ∧ ∀ i ξ, P ξ = ξ → ‖ξ‖ ≤ η →
      ‖P (T i (x ξ 0))‖ ≤ r / 2 ∧
      x (P (T i (x ξ 0))) = (fun n => T i (x ξ n)) := by
  obtain ⟨δ, hδ, hcov⟩ := hcov
  have hnearG : ∀ᶠ v in 𝓝 (0 : E), ‖G v‖ < δ :=
    hGc.norm.eventually (eventually_lt_nhds (by
      change ‖G 0‖ < δ
      rw [hG0, norm_zero]
      exact hδ))
  have hnearV : ∀ᶠ v in 𝓝 (0 : E), ‖v‖ < δ :=
    (continuous_norm.tendsto _).eventually (eventually_lt_nhds (by simpa only [norm_zero] using hδ))
  apply h.exists_uniform_commuting_family_invariant_radius hρ hr hP T hC
  filter_upwards [hnearV, hnearG] with v hv hGv
  intro i
  refine ⟨hbound i v, ?_⟩
  change G (G (T i v)) = T i (G (G v))
  rw [hcov i v hv, hcov i (G v) hGv]

end IsLocalWeightedBackwardGraph
end Euler2D

end
