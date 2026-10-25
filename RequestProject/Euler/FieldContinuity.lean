module

public import Mathlib
public import RequestProject.Euler.MultipoleFields

/-!
# Time continuity of separated fields (Lemma `ib:lem:field-continuity`, `C⁰` part)

For the planar Biot–Savart velocity `velocityC` we prove:

* `velocity_diff_separated`: if `ω₁, ω₂` are integrable and vanish in `B_δ(z)`, then
  `|K * ω₁(z) − K * ω₂(z)| ≤ (2πδ)⁻¹ ‖ω₁ − ω₂‖₁`.
* `separated_field_continuous`: if transported labels `ω(t)` vary continuously in `L¹` and stay
  at distance `≥ δ` from a target set `U`, then their velocity field is continuous in time,
  uniformly on `U` (continuity in the spatial `C⁰` norm).

The paper's statement for every spatial `C^m` norm (`m ≥ 1`) is not formalized.
-/

@[expose] public section

open MeasureTheory Complex Set Filter Topology

namespace Euler2D

lemma aestronglyMeasurable_velocity_integrand {ω : ℂ → ℝ} (hω : Integrable ω) (z : ℂ) :
    AEStronglyMeasurable (fun w => (ω w : ℂ) * (I * (z - w) / (2 * Real.pi * ‖z - w‖ ^ 2))) := by
  refine (Complex.continuous_ofReal.comp_aestronglyMeasurable hω.1).mul ?_
  exact (Measurable.aestronglyMeasurable (by fun_prop))

lemma norm_velocity_integrand_le {g : ℂ → ℝ} {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : ∀ w, ‖z - w‖ < δ → g w = 0) (w : ℂ) :
    ‖(g w : ℂ) * (I * (z - w) / (2 * Real.pi * ‖z - w‖ ^ 2))‖ ≤ |g w| / (2 * Real.pi * δ) := by
  rw [norm_velocity_integrand]
  by_cases h : ‖z - w‖ < δ
  · simp [hz w h]
  · push_neg at h
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_left h (by positivity))

lemma integrable_velocity_integrand_of_sep {g : ℂ → ℝ} (hg : Integrable g) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : ∀ w, ‖z - w‖ < δ → g w = 0) :
    Integrable (fun w => (g w : ℂ) * (I * (z - w) / (2 * Real.pi * ‖z - w‖ ^ 2))) :=
  Integrable.mono' (hg.abs.div_const (2 * Real.pi * δ))
    (aestronglyMeasurable_velocity_integrand hg z)
    (Eventually.of_forall (norm_velocity_integrand_le hδ hz))

/-- The velocity difference of two sources that vanish near the target point. -/
theorem velocity_diff_separated {ω₁ ω₂ : ℂ → ℝ} (h₁ : Integrable ω₁) (h₂ : Integrable ω₂)
    {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hz₁ : ∀ w, ‖z - w‖ < δ → ω₁ w = 0)
    (hz₂ : ∀ w, ‖z - w‖ < δ → ω₂ w = 0) :
    ‖velocityC ω₁ z - velocityC ω₂ z‖ ≤ (∫ w, |ω₁ w - ω₂ w|) / (2 * Real.pi * δ) := by
  have hz : ∀ w, ‖z - w‖ < δ → (ω₁ - ω₂) w = 0 := fun w hw => by
    simp [hz₁ w hw, hz₂ w hw]
  unfold velocityC
  rw [← integral_sub (integrable_velocity_integrand_of_sep h₁ hδ hz₁)
    (integrable_velocity_integrand_of_sep h₂ hδ hz₂), ← integral_div]
  refine norm_integral_le_of_norm_le ((h₁.sub h₂).abs.div_const _) (Eventually.of_forall ?_)
  intro w
  have := norm_velocity_integrand_le hδ hz w
  simp only [Pi.sub_apply, Complex.ofReal_sub] at this
  rw [← sub_mul]
  exact this

/-- **Lemma `ib:lem:field-continuity`** (`C⁰` norm). If the labels vary continuously in `L¹`
and stay `δ`-separated from the target set `U`, the velocity is continuous in time uniformly
on `U`. -/
theorem separated_field_continuous {ω : ℝ → ℂ → ℝ} (hint : ∀ t, Integrable (ω t))
    (hcont : ∀ t₀, Tendsto (fun t => ∫ w, |ω t w - ω t₀ w|) (𝓝 t₀) (𝓝 0))
    {U : Set ℂ} {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ t, ∀ x ∈ U, ∀ w, ‖x - w‖ < δ → ω t w = 0)
    (t₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ x ∈ U, ‖velocityC (ω t) x - velocityC (ω t₀) x‖ < ε := by
  have hpos : 0 < ε * (2 * Real.pi * δ) := by positivity
  filter_upwards [(hcont t₀).eventually (gt_mem_nhds hpos)] with t ht x hx
  refine (velocity_diff_separated (hint t) (hint t₀) hδ (hsep t x hx) (hsep t₀ x hx)).trans_lt ?_
  rw [div_lt_iff₀ (by positivity)]
  exact ht

end Euler2D
