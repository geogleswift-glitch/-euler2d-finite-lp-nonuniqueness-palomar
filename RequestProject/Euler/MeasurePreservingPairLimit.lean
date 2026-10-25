module

public import Mathlib

/-! Actual forward and inverse particle limits preserve an outer
regular measure, including infinite planar volume. Fatou first proves
both measure inequalities; the genuine inverse identities give equality. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

theorem map_le_of_ae_tendsto_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [BorelSpace β]
    {μ : Measure α} {ν : Measure β} [ν.OuterRegular]
    {F : ℕ → α → β} {G : α → β}
    (hF : ∀ n, MeasurePreserving (F n) μ ν) (hG : Measurable G)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (G a))) :
    μ.map G ≤ ν := by
  have hopen (U : Set β) (hU : IsOpen U) : μ.map G U ≤ ν U := by
    have hlow : ∀ᵐ a ∂μ, (G ⁻¹' U).indicator (1 : α → ℝ≥0∞) a ≤
        liminf (fun n => (F n ⁻¹' U).indicator (1 : α → ℝ≥0∞) a) atTop := by
      filter_upwards [hlim] with a ha
      by_cases hmem : G a ∈ U
      · have hEventually : (fun n => (F n ⁻¹' U).indicator (1 : α → ℝ≥0∞) a) =ᶠ[atTop]
            (fun _ => (1 : ℝ≥0∞)) := by
          filter_upwards [ha (hU.mem_nhds hmem)] with n hn
          exact indicator_of_mem (show a ∈ F n ⁻¹' U from hn) (1 : α → ℝ≥0∞)
        rw [liminf_congr hEventually]
        simp only [indicator_of_mem (show a ∈ G ⁻¹' U from hmem), Pi.one_apply, liminf_const, le_refl]
      · simp only [indicator_of_notMem (show a ∉ G ⁻¹' U from hmem), zero_le]
    have hmeas (n : ℕ) : Measurable ((F n ⁻¹' U).indicator (1 : α → ℝ≥0∞)) :=
      measurable_const.indicator (hU.measurableSet.preimage (hF n).measurable)
    have hI (n : ℕ) : (∫⁻ a, (F n ⁻¹' U).indicator (1 : α → ℝ≥0∞) a ∂μ) = ν U := by
      rw [lintegral_indicator_one (hU.measurableSet.preimage (hF n).measurable)]
      exact (hF n).measure_preimage hU.measurableSet.nullMeasurableSet
    rw [Measure.map_apply hG hU.measurableSet, ← lintegral_indicator_one (hU.measurableSet.preimage hG)]
    calc
      _ ≤ ∫⁻ a, liminf (fun n => (F n ⁻¹' U).indicator (1 : α → ℝ≥0∞) a) atTop ∂μ :=
        lintegral_mono_ae hlow
      _ ≤ liminf (fun n => ∫⁻ a, (F n ⁻¹' U).indicator (1 : α → ℝ≥0∞) a ∂μ) atTop :=
        lintegral_liminf_le hmeas
      _ = _ := by simp only [hI, liminf_const]
  apply Measure.le_iff.mpr
  intro S hS
  rw [S.measure_eq_iInf_isOpen ν]
  apply le_iInf
  intro U
  apply le_iInf
  intro hSU
  apply le_iInf
  intro hU
  exact (measure_mono hSU).trans (hopen U hU)

theorem measurePreserving_of_inverse_pair_map_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → α}
    (hf : Measurable f) (hg : Measurable g)
    (hfμ : μ.map f ≤ μ) (hgμ : μ.map g ≤ μ)
    (hright : Function.RightInverse g f) : MeasurePreserving f μ μ := by
  refine ⟨hf, le_antisymm hfμ ?_⟩
  have hm := Measure.map_mono hgμ hf
  rw [Measure.map_map hf hg, show f ∘ g = id from funext hright, Measure.map_id] at hm
  exact hm

theorem measurePreserving_inverse_pair_of_ae_tendsto
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    {μ : Measure α} [μ.OuterRegular] {F G : ℕ → α → α} {f g : α → α}
    (hF : ∀ n, MeasurePreserving (F n) μ μ) (hG : ∀ n, MeasurePreserving (G n) μ μ)
    (hf : Measurable f) (hg : Measurable g)
    (hflim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a)))
    (hglim : ∀ᵐ a ∂μ, Tendsto (fun n => G n a) atTop (𝓝 (g a)))
    (hleft : Function.LeftInverse g f) (hright : Function.RightInverse g f) :
    MeasurePreserving f μ μ ∧ MeasurePreserving g μ μ := by
  have hfμ := map_le_of_ae_tendsto_measurePreserving hF hf hflim
  have hgμ := map_le_of_ae_tendsto_measurePreserving hG hg hglim
  exact ⟨measurePreserving_of_inverse_pair_map_le hf hg hfμ hgμ hright,
    measurePreserving_of_inverse_pair_map_le hg hf hgμ hfμ hleft⟩

end Euler2D

end
