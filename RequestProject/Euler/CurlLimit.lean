module

public import RequestProject.Euler.LimitPassage
public import RequestProject.Euler.WeakCompactness
public import RequestProject.Euler.LpWeakClosed

/-!
# Vorticity bounds under strong convergence of velocities

The distributional curl is closed under strong `L²` convergence of the
velocities and a uniform `Lᵠ` bound on the curls, for `2 ≤ q ≤ ∞`.
Only weak compactness of the curls is used, rather than strong convergence.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

instance scalarL2T_secondCountable : SecondCountableTopology (Lp ℝ 2 μT) := by
  letI : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

/-- A continuous scalar function is in every Lebesgue space on the
fundamental square. -/
lemma continuous_memLp_torus {ψ : R2 → ℝ} (hψ : Continuous ψ) (q : ENNReal) :
    MemLp ψ q μT := by
  obtain ⟨C, hC⟩ := bound_on_box hψ
  apply MemLp.of_bound hψ.aestronglyMeasurable C
  rw [ae_restrict_iff' measurableSet_torusBox]
  exact Eventually.of_forall fun x hx => by simpa only [Real.norm_eq_abs] using hC x hx

/-- Testing a scalar `L²` function is its Hilbert pairing with the same
test represented in `L²`. -/
lemma scalar_test_pairing_eq_inner (w : Lp ℝ 2 μT)
    {ψ : R2 → ℝ} (hψ : Continuous ψ) :
    (∫ x in torusBox, w x * ψ x) =
      inner ℝ w ((continuous_memLp_torus hψ 2).toLp ψ) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(continuous_memLp_torus hψ 2).coeFn_toLp] with x hx
  rw [hx]
  simp [mul_comm]

/-- **Lemma `cp:lem:curl-bound`.** Strong convergence of velocities and
uniformly bounded `Lᵠ` curls give an `Lᵠ` curl of the limit with the same
bound. -/
theorem curl_bound_of_tendsto {q : ENNReal} (hq : 2 ≤ q)
    {v : ℕ → L2T} {u : L2T} {M : ℝ}
    (hv : Tendsto v atTop (𝓝 u))
    (hw : ∀ n, ∃ w : R2 → ℝ,
      MemLp w q μT ∧ IsCurl (v n) w ∧ (eLpNorm w q μT).toReal ≤ M) :
    ∃ w : R2 → ℝ,
      MemLp w q μT ∧ IsCurl u w ∧ (eLpNorm w q μT).toReal ≤ M := by
  choose w hwmem hwcurl hwbound using hw
  have hM : 0 ≤ M := ENNReal.toReal_nonneg.trans (hwbound 0)
  have hwENN (n : ℕ) : eLpNorm (w n) q μT ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_toReal (hwmem n).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (hwbound n)
  have hexp : 0 ≤ 1 / (2 : ℝ) - 1 / q.toReal := by
    by_cases ht : q = ∞
    · simp [ht]
    have hqr : (2 : ℝ) ≤ q.toReal := by
      simpa using ENNReal.toReal_mono ht hq
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hqr
    linarith
  let C : ENNReal := ENNReal.ofReal M * μT univ ^ (1 / (2 : ℝ) - 1 / q.toReal)
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μT univ))
  let W : ℕ → Lp ℝ 2 μT := fun n => ((hwmem n).mono_exponent hq).toLp (w n)
  have hWae (n : ℕ) : (W n : R2 → ℝ) =ᵐ[μT] w n :=
    ((hwmem n).mono_exponent hq).coeFn_toLp
  have hWbound (n : ℕ) : ‖W n‖ ≤ C.toReal := by
    change ‖((hwmem n).mono_exponent hq).toLp (w n)‖ ≤ C.toReal
    rw [Lp.norm_toLp]
    apply ENNReal.toReal_mono hC
    calc
      eLpNorm (w n) 2 μT ≤ eLpNorm (w n) q μT *
          μT univ ^ (1 / (2 : ℝ) - 1 / q.toReal) := by
        simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq
          (hwmem n).aestronglyMeasurable
      _ ≤ C := mul_le_mul_left (hwENN n) _
  obtain ⟨ω, _, φ, hφ, hweak⟩ := exists_weakly_convergent_subsequence W C.toReal hWbound
  have hωbound : eLpNorm ω q μT ≤ ENNReal.ofReal M := by
    apply eLpNorm_le_of_inner_tendsto μT ((by norm_num : (1 : ENNReal) ≤ 2).trans hq)
      (fun n => ?_) hweak
    rw [eLpNorm_congr_ae (hWae (φ n))]
    exact hwENN (φ n)
  refine ⟨ω, memLp_iff.mpr (hωbound.trans_lt (by simp)), ?_,
    ENNReal.toReal_le_of_le_ofReal hM hωbound⟩
  intro ψ hψ
  have hψc : Continuous ψ := hψ.1.continuous
  have hleft : Tendsto (fun n => ∫ x in torusBox, w (φ n) x * ψ x) atTop
      (𝓝 (∫ x in torusBox, ω x * ψ x)) := by
    have heq (n : ℕ) : (∫ x in torusBox, w (φ n) x * ψ x) =
        inner ℝ (W (φ n)) ((continuous_memLp_torus hψc 2).toLp ψ) := by
      rw [← scalar_test_pairing_eq_inner (W (φ n)) hψc]
      apply integral_congr_ae
      filter_upwards [hWae (φ n)] with x hx
      rw [hx]
    simp_rw [heq, scalar_test_pairing_eq_inner ω hψc]
    exact hweak _
  have hpd (i : Fin 2) : Continuous (pd i ψ) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hrhs (n : ℕ) :
      (∫ x in torusBox, v n x 0 * pd 1 ψ x - v n x 1 * pd 0 ψ x) =
      (∫ x in torusBox, v n x 0 * pd 1 ψ x) -
        ∫ x in torusBox, v n x 1 * pd 0 ψ x := by
    have hint (i j : Fin 2) : Integrable (fun x => v n x i * pd j ψ x) μT := by
      obtain ⟨C', hC'⟩ := bound_on_box (hpd j)
      exact integrable_lin (v n) i (hpd j).aestronglyMeasurable hC'
    exact integral_sub (hint 0 1) (hint 1 0)
  have huint :
      (∫ x in torusBox, u x 0 * pd 1 ψ x - u x 1 * pd 0 ψ x) =
      (∫ x in torusBox, u x 0 * pd 1 ψ x) -
        ∫ x in torusBox, u x 1 * pd 0 ψ x := by
    have hint (i j : Fin 2) : Integrable (fun x => u x i * pd j ψ x) μT := by
      obtain ⟨C', hC'⟩ := bound_on_box (hpd j)
      exact integrable_lin u i (hpd j).aestronglyMeasurable hC'
    exact integral_sub (hint 0 1) (hint 1 0)
  have hright : Tendsto
      (fun n => ∫ x in torusBox, v (φ n) x 0 * pd 1 ψ x - v (φ n) x 1 * pd 0 ψ x)
      atTop (𝓝 (∫ x in torusBox, u x 0 * pd 1 ψ x - u x 1 * pd 0 ψ x)) := by
    simp_rw [hrhs, huint]
    exact (tendsto_integral_lin (hv.comp hφ.tendsto_atTop) (hpd 1) 0).sub
      (tendsto_integral_lin (hv.comp hφ.tendsto_atTop) (hpd 0) 1)
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall fun n =>
    (hwcurl (φ n) ψ hψ).symm))

/-- Uniform-in-time vorticity bounds are retained by pointwise strong
`L²` limits of paths. -/
theorem curlBoundedBy_of_tendsto {T M : ℝ} {q : ENNReal} (hq : 2 ≤ q)
    {U : ℕ → ℝ → L2T} {u : ℝ → L2T}
    (hU : ∀ n, CurlBoundedBy T q M (U n))
    (hlim : ∀ t ∈ Icc 0 T, Tendsto (fun n => U n t) atTop (𝓝 (u t))) :
    CurlBoundedBy T q M u := by
  intro t ht
  exact curl_bound_of_tendsto hq (hlim t ht) (fun n => hU n t ht)

/-- On the finite torus, a uniform `Lᵠ` vorticity bound gives a uniform
`Lᵖ` bound for every finite exponent `1 ≤ p ≤ q`. -/
theorem curlBounded_mono_exponent {T : ℝ} {p q : ENNReal}
    (hp : 1 ≤ p) (hpfin : p ≠ ∞) (hpq : p ≤ q)
    {u : ℝ → L2T} (hu : CurlBounded T q u) : CurlBounded T p u := by
  obtain ⟨M, hM⟩ := hu
  have hpr : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt ((by norm_num : (0 : ENNReal) < 1).trans_le hp)) hpfin
  have hexp : 0 ≤ 1 / p.toReal - 1 / q.toReal := by
    by_cases ht : q = ∞
    · simp [ht, le_of_lt hpr]
    have hqr : p.toReal ≤ q.toReal := ENNReal.toReal_mono ht hpq
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hpr hqr)
  let C : ENNReal := ENNReal.ofReal (max M 0) *
    μT univ ^ (1 / p.toReal - 1 / q.toReal)
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μT univ))
  refine ⟨C.toReal, fun t ht => ?_⟩
  obtain ⟨w, hw, hcurl, hbound⟩ := hM t ht
  have hwq : eLpNorm w q μT ≤ ENNReal.ofReal (max M 0) := by
    rw [← ENNReal.ofReal_toReal hw.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (hbound.trans (le_max_left _ _))
  have hwp : eLpNorm w p μT ≤ C :=
    (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hw.aestronglyMeasurable).trans
      (mul_le_mul_left hwq _)
  exact ⟨w, hw.mono_exponent hpq, hcurl, ENNReal.toReal_mono hC hwp⟩

end Euler2D

end
