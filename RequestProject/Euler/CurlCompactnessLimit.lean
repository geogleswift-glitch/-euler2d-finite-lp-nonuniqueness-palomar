module

public import RequestProject.Euler.BoxFourierCompactness
public import RequestProject.Euler.FiniteApproximation
public import RequestProject.Euler.CurlLimit

/-!
# Compactness of finite Euler solutions from their actual vorticity bounds

The Fourier operators and their errors are proved in the original torus
model. They are no longer inputs to the limit argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Euler2D

theorem uniform_subseq_on_interval_of_curl_bounds
    {T : ℝ} (U : ℕ → ℝ → L2T)
    (L : ℝ≥0) (hlip : ∀ n, LipschitzWith L (fun t : Icc (0 : ℝ) T => U n t))
    {M : ℝ} (hbound : ∀ n t, t ∈ Icc 0 T → ‖U n t‖ ≤ M)
    {q : ENNReal} (hq : 2 ≤ q) {C : ℝ}
    (hdiv : ∀ n t, t ∈ Icc 0 T → DivFree (U n t))
    (hcurl : ∀ n, CurlBoundedBy T q C (U n)) :
    ∃ u : ℝ → L2T, ContinuousOn u (Icc 0 T) ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformlyOn (fun n => U (φ n)) u atTop (Icc 0 T) := by
  obtain ⟨v, _, φ, hφ, hv⟩ := compactness_of_uniform_curl_bounds
    (fun n (t : Icc (0 : ℝ) T) => U n t) L hlip
    (fun n t => hbound n t t.property) hq
    (fun n t => ⟨hdiv n t t.property, hcurl n t t.property⟩)
  let u : ℝ → L2T := fun t => if ht : t ∈ Icc 0 T then v ⟨t, ht⟩ else 0
  have hlim : TendstoUniformlyOn (fun n => U (φ n)) u atTop (Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hv ε hε] with n hn t ht
    simpa only [u, dif_pos ht] using hn ⟨t, ht⟩
  refine ⟨u, hlim.continuousOn (Eventually.of_forall fun n => ?_).frequently,
    φ, hφ, hlim⟩
  exact continuousOn_iff_continuous_restrict.mpr (hlip (φ n)).continuous

/-- Actual uniform vorticity bounds give a strong limit of finite weak
solutions retaining the same vorticity bound and a positive departure. -/
theorem weak_limit_with_departure_of_curl_bounds
    {T a b c : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hb : b < T) (hc : 0 < c)
    {U : ℕ → ℝ → L2T} {u₀n : ℕ → L2T} {u₀ : L2T}
    (hU : ∀ n, IsWeakEulerSolution T (u₀n n) (U n))
    (hinit : Tendsto u₀n atTop (𝓝 u₀))
    (L : ℝ≥0) (hlip : ∀ n, LipschitzWith L (fun t : Icc (0 : ℝ) T => U n t))
    {M : ℝ} (hbound : ∀ n t, t ∈ Icc 0 T → ‖U n t‖ ≤ M)
    {q : ENNReal} (hq : 2 ≤ q) {C : ℝ}
    (hcurl : ∀ n, CurlBoundedBy T q C (U n))
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc a b)
    (hdep : ∀ n, c ≤ ‖U n (τ n) - u₀‖) :
    ∃ u : ℝ → L2T, IsWeakEulerSolution T u₀ u ∧ CurlBoundedBy T q C u ∧
      ∃ t ∈ Ioo 0 T, c ≤ ‖u t - u₀‖ ∧ u t ≠ u₀ := by
  obtain ⟨u, hu, φ, hφ, hlim⟩ := uniform_subseq_on_interval_of_curl_bounds
    U L hlip hbound hq (fun n => (hU n).divFree) hcurl
  have hweak : IsWeakEulerSolution T u₀ u :=
    isWeakEulerSolution_of_tendstoUniformlyOn hT (fun n => hU (φ n))
      hlim (hinit.comp hφ.tendsto_atTop)
  have hcU : CurlBoundedBy T q C u := curlBoundedBy_of_tendsto hq
    (fun n => hcurl (φ n)) (fun t ht => hlim.tendsto_at ht)
  obtain ⟨t, ht, hct⟩ := exists_departure_lowerBound_of_tendstoUniformlyOn
    ha.le hb.le hu hlim (tendsto_const_nhds (x := u₀))
    (fun n => hτ (φ n)) (fun n => hdep (φ n))
  exact ⟨u, hweak, hcU, t, ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩, hct,
    sub_ne_zero.mp (norm_pos_iff.mp (hc.trans_le hct))⟩

end Euler2D

end
