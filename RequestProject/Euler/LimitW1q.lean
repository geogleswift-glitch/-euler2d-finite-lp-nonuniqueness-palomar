module

public import RequestProject.Euler.LimitAssembly
public import RequestProject.Euler.W1pLimit

/-!
# The nonstationary limit from uniform Sobolev bounds

The initial Sobolev regularity and all vorticity bounds are consequences
of the finite solutions' uniform `W¹,ᵠ` bound. They are not separate
hypotheses on the limiting datum or limiting path.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Euler2D

lemma l2_norm_le_of_W1pBoundedBy {q : ENNReal} (hq : 2 ≤ q) {S : ℝ} {u : L2T}
    (h : W1pBoundedBy q S u) :
    ‖u‖ ≤ (ENNReal.ofReal S * μT univ ^ (1 / (2 : ℝ) - 1 / q.toReal)).toReal := by
  have hexp : 0 ≤ 1 / (2 : ℝ) - 1 / q.toReal := by
    by_cases ht : q = ∞
    · simp [ht]
    have hqr : (2 : ℝ) ≤ q.toReal := by
      simpa using ENNReal.toReal_mono ht hq
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hqr)
  have hC : ENNReal.ofReal S * μT univ ^ (1 / (2 : ℝ) - 1 / q.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μT univ))
  rw [Lp.norm_def]
  apply ENNReal.toReal_mono hC
  exact (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq h.1.aestronglyMeasurable).trans
    (mul_le_mul_left h.2.1 _)

/-- The full conclusion of the limit proposition, including a uniform
Sobolev bound, from the finite solutions' quantitative properties.
The finite solutions and their uniform departure still have to be
constructed; this theorem does not postulate their existence. -/
theorem limit_solution_of_W1q_bounds
    {T a b c : ℝ} (hT : 0 < T) (ha : 0 < a) (hb : b < T) (hc : 0 < c)
    {p q : ENNReal} (hp : 1 ≤ p) (hpfin : p ≠ ∞) (hq : 2 ≤ q) (hpq : p ≤ q)
    {u₀ : L2T} (hmean : ∫ x in torusBox, u₀ x = 0) (hstat : IsStationary u₀)
    {U : ℕ → ℝ → L2T} {u₀n : ℕ → L2T}
    (hU : ∀ n, IsWeakEulerSolution T (u₀n n) (U n))
    (hinit : Tendsto u₀n atTop (𝓝 u₀))
    (S : ℝ) (hSob : ∀ n t, t ∈ Icc 0 T → W1pBoundedBy q S (U n t))
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc a b)
    (hdep : ∀ n, c ≤ ‖U n (τ n) - u₀‖) :
    (∫ x in torusBox, u₀ x = 0) ∧ DivFree u₀ ∧ MemW1p p u₀ ∧ IsStationary u₀ ∧
      ∃ u : ℝ → L2T, IsWeakEulerSolution T u₀ u ∧ CurlBounded T p u ∧
        (∀ t ∈ Icc 0 T, W1pBoundedBy q S (u t)) ∧
          ∃ tstar ∈ Ioo 0 T, c ≤ ‖u tstar - u₀‖ ∧ u tstar ≠ u₀ := by
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hinitSob (n : ℕ) : W1pBoundedBy q S (u₀n n) := by
    rw [← (hU n).initial]
    exact hSob n 0 hzero
  have hu₀Sob := w1pBoundedBy_of_tendsto hq hinit hinitSob
  have hu₀div : DivFree u₀ := divFree_of_tendsto hinit
    (Eventually.of_forall fun n => by
      rw [← (hU n).initial]
      exact (hU n).divFree 0 hzero)
  have hqone : 1 ≤ q := (by norm_num : (1 : ENNReal) ≤ 2).trans hq
  have hbound : ∀ n t, t ∈ Icc 0 T → ‖U n t‖ ≤
      (ENNReal.ofReal S * μT univ ^ (1 / (2 : ℝ) - 1 / q.toReal)).toReal :=
    fun n t ht => l2_norm_le_of_W1pBoundedBy hq (hSob n t ht)
  obtain ⟨u, hu, φ, hφ, hlim⟩ := uniform_subseq_of_weakEuler_curl_bounds
    hT hU hbound hq
    (fun n => W1pBoundedBy.curlBoundedBy (hSob n) hqone)
  have hweak : IsWeakEulerSolution T u₀ u :=
    isWeakEulerSolution_of_tendstoUniformlyOn hT.le (fun n => hU (φ n))
      hlim (hinit.comp hφ.tendsto_atTop)
  have huSob : ∀ t ∈ Icc 0 T, W1pBoundedBy q S (u t) :=
    w1pBoundedBy_on_of_tendsto hq (fun n t ht => hSob (φ n) t ht)
      (fun t ht => hlim.tendsto_at ht)
  have hcurl : CurlBounded T p u := curlBounded_mono_exponent hp hpfin hpq
    ⟨2 * max S 0, W1pBoundedBy.curlBoundedBy huSob hqone⟩
  obtain ⟨t, ht, hct⟩ := exists_departure_lowerBound_of_tendstoUniformlyOn
    ha.le hb.le hu hlim (tendsto_const_nhds (x := u₀))
    (fun n => hτ (φ n)) (fun n => hdep (φ n))
  exact ⟨hmean, hu₀div, hu₀Sob.memW1p.mono_exponent hpq, hstat, u, hweak, hcurl, huSob,
    t, ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩, hct,
      sub_ne_zero.mp (norm_pos_iff.mp (hc.trans_le hct))⟩

end Euler2D

end
