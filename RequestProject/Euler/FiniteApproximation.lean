module

public import RequestProject.Euler.Compactness
public import RequestProject.Euler.LimitPassage

/-!
# A nonstationary weak limit of finite approximants

This assembles the compactness, nonlinear limit passage, and departure-time
steps in the proof of Proposition `cp:limit`. The hypotheses concern actual
weak Euler solutions and actual finite-rank approximations in `L²`.

This does not assert the missing vortex-patch construction or passage of
uniform `Lᵖ` vorticity bounds to the limit.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

/-- Finite-rank spatial approximations and a uniform time modulus supply a
uniformly convergent subsequence of real-time paths on `[0,T]`. -/
theorem uniform_subseq_on_interval_of_truncation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} (U : ℕ → ℝ → E) (L : ℝ≥0)
    (hlip : ∀ n, LipschitzWith L (fun t : Icc (0 : ℝ) T => U n t))
    (M : ℝ) (hbound : ∀ n t, t ∈ Icc 0 T → ‖U n t‖ ≤ M)
    (Q : ℕ → E →L[ℝ] E)
    (hfinite : ∀ m, FiniteDimensional ℝ (LinearMap.range (Q m).toLinearMap))
    (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (happrox : ∀ m n t, t ∈ Icc 0 T → ‖U n t - Q m (U n t)‖ ≤ err m) :
    ∃ u : ℝ → E, ContinuousOn u (Icc 0 T) ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformlyOn (fun n => U (φ n)) u atTop (Icc 0 T) := by
  obtain ⟨v, _, φ, hφ, hv⟩ := compactness_by_truncation
    (fun n (t : Icc (0 : ℝ) T) => U n t) L hlip M
    (fun n t => hbound n t t.property) Q hfinite err herr
    (fun m n t => happrox m n t t.property)
  let u : ℝ → E := fun t => if ht : t ∈ Icc 0 T then v ⟨t, ht⟩ else 0
  have hlim : TendstoUniformlyOn (fun n => U (φ n)) u atTop (Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hv ε hε] with n hn t ht
    simpa only [u, dif_pos ht] using hn ⟨t, ht⟩
  refine ⟨u, hlim.continuousOn (Filter.Eventually.of_forall fun n => ?_).frequently,
    φ, hφ, hlim⟩
  exact continuousOn_iff_continuous_restrict.mpr (hlip (φ n)).continuous

/-- The compactness and departure portion of Proposition `cp:limit`, for a
sequence of genuine finite weak Euler solutions. -/
theorem weak_limit_with_departure
    {T a b c : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hb : b < T) (hc : 0 < c)
    {U : ℕ → ℝ → L2T} {u₀n : ℕ → L2T} {u₀ : L2T}
    (hU : ∀ n, IsWeakEulerSolution T (u₀n n) (U n))
    (hinit : Tendsto u₀n atTop (𝓝 u₀))
    (L : ℝ≥0) (hlip : ∀ n, LipschitzWith L (fun t : Icc (0 : ℝ) T => U n t))
    (M : ℝ) (hbound : ∀ n t, t ∈ Icc 0 T → ‖U n t‖ ≤ M)
    (Q : ℕ → L2T →L[ℝ] L2T)
    (hfinite : ∀ m, FiniteDimensional ℝ (LinearMap.range (Q m).toLinearMap))
    (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (happrox : ∀ m n t, t ∈ Icc 0 T → ‖U n t - Q m (U n t)‖ ≤ err m)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc a b)
    (hdep : ∀ n, c ≤ ‖U n (τ n) - u₀‖) :
    ∃ u : ℝ → L2T, IsWeakEulerSolution T u₀ u ∧
      ∃ t ∈ Ioo 0 T, c ≤ ‖u t - u₀‖ ∧ u t ≠ u₀ := by
  obtain ⟨u, hu, φ, hφ, hlim⟩ := uniform_subseq_on_interval_of_truncation
    U L hlip M hbound Q hfinite err herr happrox
  have hweak : IsWeakEulerSolution T u₀ u :=
    isWeakEulerSolution_of_tendstoUniformlyOn hT (fun n => hU (φ n))
      hlim (hinit.comp hφ.tendsto_atTop)
  obtain ⟨t, ht, hct⟩ := exists_departure_lowerBound_of_tendstoUniformlyOn
    ha.le hb.le hu hlim (tendsto_const_nhds (x := u₀))
    (fun n => hτ (φ n)) (fun n => hdep (φ n))
  refine ⟨u, hweak, t, ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩, hct, ?_⟩
  exact sub_ne_zero.mp (norm_pos_iff.mp (hc.trans_le hct))

end Euler2D

end
