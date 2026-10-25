module

public import RequestProject.Euler.EulerCompactness

/-!
# The limit proposition from finite Euler solutions

`FiniteEulerData` lists the finite-solution inputs in the paper's proof
of `cp:limit`. Its existence is not postulated here. Given these inputs,
all the compactness, weak-equation, vorticity-bound and departure steps
are proved, yielding exactly the conclusion used in `Theorems.lean`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

/-- The actual finite-solution properties needed for the limit argument.
Constructing this data, including the uniform positive departure, remains
the finite vortex-patch part of the paper. -/
structure FiniteEulerData (T : ℝ) (p : ENNReal) where
  datum : L2T
  mean_zero : ∫ x in torusBox, datum x = 0
  divergence_free : DivFree datum
  sobolev : MemW1p p datum
  stationary : IsStationary datum
  q : ENNReal
  two_le_q : 2 ≤ q
  p_le_q : p ≤ q
  initial : ℕ → L2T
  initial_limit : Tendsto initial atTop (𝓝 datum)
  solutions : ℕ → ℝ → L2T
  weak_solutions : ∀ n, IsWeakEulerSolution T (initial n) (solutions n)
  curl_bound : ℝ
  uniform_curl : ∀ n, CurlBoundedBy T q curl_bound (solutions n)
  a : ℝ
  b : ℝ
  a_pos : 0 < a
  b_lt : b < T
  departure : ℝ
  departure_pos : 0 < departure
  departure_time : ℕ → ℝ
  departure_time_mem : ∀ n, departure_time n ∈ Icc a b
  uniform_departure : ∀ n, departure ≤ ‖solutions n (departure_time n) - datum‖

/-- **Proposition `cp:limit` from the finite-solution properties.** No
limit solution or vorticity convergence is an input. -/
theorem limit_solution_of_finite_solutions {T : ℝ} (hT : 0 < T)
    {p : ENNReal} (hp : 1 ≤ p) (hpfin : p ≠ ∞) (D : FiniteEulerData T p) :
    ∃ u₀ : L2T, (∫ x in torusBox, u₀ x = 0) ∧ DivFree u₀ ∧ MemW1p p u₀ ∧
      IsStationary u₀ ∧
      ∃ u : ℝ → L2T, IsWeakEulerSolution T u₀ u ∧ CurlBounded T p u ∧
        ∃ tstar ∈ Ioo 0 T, u tstar ≠ u₀ := by
  obtain ⟨u, hu, φ, hφ, hlim⟩ := uniform_subseq_of_weakEuler_curl_and_initial_convergence
    hT D.weak_solutions D.initial_limit D.two_le_q D.uniform_curl
  have hweak : IsWeakEulerSolution T D.datum u :=
    isWeakEulerSolution_of_tendstoUniformlyOn hT.le (fun n => D.weak_solutions (φ n))
      hlim (D.initial_limit.comp hφ.tendsto_atTop)
  have hcurl : CurlBoundedBy T D.q D.curl_bound u :=
    curlBoundedBy_of_tendsto D.two_le_q (fun n => D.uniform_curl (φ n))
      (fun t ht => hlim.tendsto_at ht)
  have hcurlp : CurlBounded T p u :=
    curlBounded_mono_exponent hp hpfin D.p_le_q ⟨D.curl_bound, hcurl⟩
  obtain ⟨t, ht, hdep⟩ := exists_departure_lowerBound_of_tendstoUniformlyOn
    D.a_pos.le D.b_lt.le hu hlim (tendsto_const_nhds (x := D.datum))
    (fun n => D.departure_time_mem (φ n)) (fun n => D.uniform_departure (φ n))
  refine ⟨D.datum, D.mean_zero, D.divergence_free, D.sobolev, D.stationary,
    u, hweak, hcurlp, t, ⟨D.a_pos.trans_le ht.1, ht.2.trans_lt D.b_lt⟩, ?_⟩
  exact sub_ne_zero.mp (norm_pos_iff.mp (D.departure_pos.trans_le hdep))

end Euler2D

end
