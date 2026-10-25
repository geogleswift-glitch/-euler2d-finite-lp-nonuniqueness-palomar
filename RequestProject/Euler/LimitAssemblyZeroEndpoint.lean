module

public import RequestProject.Euler.LimitAssembly

/-! Uniform velocity departure on [0,b], b<T, suffices: the limit's
genuine initial condition excludes departure at zero. This retains
the original strict positive departure time in the conclusion. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Euler2D

theorem weak_limit_with_departure_of_uniform_curl_zero_endpoint
    {T b c : ℝ} (hT : 0 < T) (hb : b < T) (hc : 0 < c)
    {U : ℕ → ℝ → L2T} {initial : ℕ → L2T} {datum : L2T}
    (hU : ∀ n, IsWeakEulerSolution T (initial n) (U n))
    (hinit : Tendsto initial atTop (𝓝 datum))
    {q : ENNReal} (hq : 2 ≤ q) {C : ℝ}
    (hcurl : ∀ n, CurlBoundedBy T q C (U n))
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc 0 b)
    (hdeparture : ∀ n, c ≤ ‖U n (τ n) - datum‖) :
    ∃ u : ℝ → L2T, IsWeakEulerSolution T datum u ∧ CurlBoundedBy T q C u ∧
      ∃ t ∈ Ioo 0 T, c ≤ ‖u t - datum‖ ∧ u t ≠ datum := by
  obtain ⟨u, hu, φ, hφ, hlim⟩ := uniform_subseq_of_weakEuler_curl_and_initial_convergence
    hT hU hinit hq hcurl
  have hweak : IsWeakEulerSolution T datum u :=
    isWeakEulerSolution_of_tendstoUniformlyOn hT.le (fun n => hU (φ n))
      hlim (hinit.comp hφ.tendsto_atTop)
  have hcU : CurlBoundedBy T q C u := curlBoundedBy_of_tendsto hq
    (fun n => hcurl (φ n)) (fun t ht => hlim.tendsto_at ht)
  obtain ⟨t, ht, hct⟩ := exists_departure_lowerBound_of_tendstoUniformlyOn
    (le_refl (0 : ℝ)) hb.le hu hlim (tendsto_const_nhds (x := datum))
    (fun n => hτ (φ n)) (fun n => hdeparture (φ n))
  have hne : u t ≠ datum := sub_ne_zero.mp (norm_pos_iff.mp (hc.trans_le hct))
  have htne : t ≠ 0 := by
    intro heq
    apply hne
    rw [heq, hweak.initial]
  exact ⟨u, hweak, hcU, t, ⟨lt_of_le_of_ne ht.1 (Ne.symm htne), ht.2.trans_lt hb⟩, hct, hne⟩

end Euler2D

end
