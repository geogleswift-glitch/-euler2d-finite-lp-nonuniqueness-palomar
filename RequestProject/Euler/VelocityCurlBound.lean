module

public import RequestProject.Euler.WeakTestSeparation

/-!
# Velocity bounds from curl and conserved mean

The nonzero Fourier modes are controlled by the actual distributional
curl. The zero mode is controlled by any velocity with the same mean.
This gives a uniform velocity bound without assuming energy conservation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

lemma one_le_frequencySq {k : Fin 2 → ℤ} (hk : k ≠ 0) : 1 ≤ frequencySq k := by
  have hp := frequencySq_pos hk
  unfold frequencySq at hp ⊢
  have hz : (0 : ℤ) < k 0 ^ 2 + k 1 ^ 2 := by exact_mod_cast hp
  have hge : (1 : ℤ) ≤ k 0 ^ 2 + k 1 ^ 2 := by omega
  exact_mod_cast hge

lemma norm_fourier_le_weighted_add_zero (f : FourierL2) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s : Finset (Fin 2 → ℤ),
      ∑ k ∈ s, frequencySq k * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 ≤ M ^ 2) :
    ‖f‖ ≤ M + ‖UnitAddTorus.mFourierCoeff f 0‖ := by
  have hsq : ‖f‖ ^ 2 ≤ M ^ 2 + ‖UnitAddTorus.mFourierCoeff f 0‖ ^ 2 := by
    rw [FourierProjection.norm_sq_eq_tsum UnitAddTorus.mFourierBasis]
    simp only [UnitAddTorus.mFourierBasis_repr]
    apply Real.tsum_le_of_sum_le (fun _ => sq_nonneg _)
    intro s
    have hterm (k : Fin 2 → ℤ) : ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 ≤
        frequencySq k * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 +
          if k = 0 then ‖UnitAddTorus.mFourierCoeff f 0‖ ^ 2 else 0 := by
      by_cases hk : k = 0
      · simp [hk, frequencySq]
      · simp only [hk, ↓reduceIte, add_zero]
        exact le_mul_of_one_le_left (sq_nonneg _) (one_le_frequencySq hk)
    have hzero : (∑ k ∈ s, if k = 0 then ‖UnitAddTorus.mFourierCoeff f 0‖ ^ 2 else 0) ≤
        ‖UnitAddTorus.mFourierCoeff f 0‖ ^ 2 := by
      classical
      simp only [Finset.sum_ite_eq']
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _
    calc
      _ ≤ ∑ k ∈ s, (frequencySq k * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 +
          if k = 0 then ‖UnitAddTorus.mFourierCoeff f 0‖ ^ 2 else 0) :=
        Finset.sum_le_sum fun k _ => hterm k
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (hbound s) hzero
  nlinarith [norm_nonneg f, norm_nonneg (UnitAddTorus.mFourierCoeff f 0)]

lemma norm_mFourierCoeff_le (f : FourierL2) (k : Fin 2 → ℤ) :
    ‖UnitAddTorus.mFourierCoeff f k‖ ≤ ‖f‖ := by
  have h := UnitAddTorus.mFourierBasis.orthonormal.sum_inner_products_le f (s := {k})
  have hs : ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    simpa only [← UnitAddTorus.mFourierBasis_repr, HilbertBasis.repr_apply_apply,
      Finset.sum_singleton] using h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

lemma norm_boxComplexCoord_le (u : L2T) (j : Fin 2) : ‖boxComplexCoord j u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_boxComplexCoord j u] with x hx
  rw [hx, Complex.norm_real, Real.norm_eq_abs]
  exact abs_coord_le _ _

lemma zero_mode_eq_of_integral_eq {u v : L2T}
    (hmean : (∫ x in torusBox, u x) = ∫ x in torusBox, v x) (j : Fin 2) :
    UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord j u)) 0 =
      UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord j v)) 0 := by
  have hcoord (w : L2T) : (∫ x in torusBox, w x) j = ∫ x in torusBox, w x j :=
    ((EuclideanSpace.proj j : R2 →L[ℝ] ℝ).integral_comp_comm
      ((Lp.memLp w).integrable (by norm_num))).symm
  have heq := congrArg (fun x : R2 => x j) hmean
  dsimp only at heq
  rw [hcoord, hcoord] at heq
  rw [mFourierCoeff_velocity_coord, mFourierCoeff_velocity_coord]
  simp only [boxFourierCoeff, boxFourierPhase_apply, Pi.zero_apply, Int.cast_zero,
    zero_mul, Finset.sum_const_zero, Real.cos_zero, mul_one, Real.sin_zero, mul_zero,
    integral_zero, neg_zero, heq]

/-- The actual torus velocity is bounded by its curl and any reference
velocity with the same spatial mean. -/
theorem norm_velocity_le_of_curl_and_mean (u v : L2T) (hu : DivFree u)
    (ω : R2 → ℝ) (hω : MemLp ω 2 μT) (hc : IsCurl u ω)
    (hmean : (∫ x in torusBox, u x) = ∫ x in torusBox, v x) :
    ‖u‖ ≤ 2 * ((eLpNorm ω 2 μT).toReal + ‖v‖) := by
  have hcoord (j : Fin 2) : ‖boxComplexCoord j u‖ ≤ (eLpNorm ω 2 μT).toReal + ‖v‖ := by
    have hbound (s : Finset (Fin 2 → ℤ)) :
        ∑ k ∈ s, frequencySq k *
          ‖UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord j u)) k‖ ^ 2 ≤
            (eLpNorm ω 2 μT).toReal ^ 2 := by
      apply le_trans _ (lifted_velocity_weighted_bound u hu ω hω hc s)
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (frequencySq_nonneg k)
      fin_cases j
      · exact le_add_of_nonneg_right (sq_nonneg _)
      · exact le_add_of_nonneg_left (sq_nonneg _)
    calc
      _ = ‖torusL2Equiv (boxComplexCoord j u)‖ := (torusL2Equiv.norm_map _).symm
      _ ≤ (eLpNorm ω 2 μT).toReal +
          ‖UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord j u)) 0‖ :=
        norm_fourier_le_weighted_add_zero _ ENNReal.toReal_nonneg hbound
      _ ≤ (eLpNorm ω 2 μT).toReal + ‖v‖ := by
        rw [zero_mode_eq_of_integral_eq hmean]
        exact add_le_add le_rfl ((norm_mFourierCoeff_le _ 0).trans
          ((torusL2Equiv.norm_map _).le.trans (norm_boxComplexCoord_le v j)))
  calc
    ‖u‖ = ‖boxRealCoordInjection 0 (boxComplexCoord 0 u) +
        boxRealCoordInjection 1 (boxComplexCoord 1 u)‖ := by rw [boxRealCoordInjection_coords]
    _ ≤ ‖boxRealCoordInjection 0 (boxComplexCoord 0 u)‖ +
        ‖boxRealCoordInjection 1 (boxComplexCoord 1 u)‖ := norm_add_le _ _
    _ ≤ ‖boxComplexCoord 0 u‖ + ‖boxComplexCoord 1 u‖ :=
      add_le_add (norm_boxRealCoordInjection_le 0 _) (norm_boxRealCoordInjection_le 1 _)
    _ ≤ ((eLpNorm ω 2 μT).toReal + ‖v‖) + ((eLpNorm ω 2 μT).toReal + ‖v‖) :=
      add_le_add (hcoord 0) (hcoord 1)
    _ = _ := by ring

def torusLqToL2Bound (q : ENNReal) (M : ℝ) : ℝ :=
  (ENNReal.ofReal M * μT univ ^ (1 / (2 : ℝ) - 1 / q.toReal)).toReal

lemma l2_bound_of_memLp_bound {F : Type*} [NormedAddCommGroup F]
    {q : ENNReal} (hq : 2 ≤ q) {f : R2 → F} (hf : MemLp f q μT) {M : ℝ}
    (hM : (eLpNorm f q μT).toReal ≤ M) :
    (eLpNorm f 2 μT).toReal ≤ torusLqToL2Bound q M := by
  have hexp : 0 ≤ 1 / (2 : ℝ) - 1 / q.toReal := by
    by_cases ht : q = ∞
    · simp [ht]
    have hqr : (2 : ℝ) ≤ q.toReal := by simpa using ENNReal.toReal_mono ht hq
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hqr)
  have hC : ENNReal.ofReal M * μT univ ^ (1 / (2 : ℝ) - 1 / q.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μT univ))
  apply ENNReal.toReal_mono hC
  have hqnorm : eLpNorm f q μT ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hM
  exact (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq hf.aestronglyMeasurable).trans
    (mul_le_mul_left hqnorm _)

/-- Common vorticity bounds and bounded initial data already give a
common velocity bound for weak solutions, by conserved mean. -/
theorem uniform_velocity_bound_of_curl_and_initial {T : ℝ} (hT : 0 < T)
    {U : ℕ → ℝ → L2T} {u₀ : ℕ → L2T}
    (hU : ∀ n, IsWeakEulerSolution T (u₀ n) (U n))
    {B : ℝ} (hinit : ∀ n, ‖u₀ n‖ ≤ B)
    {q : ENNReal} (hq : 2 ≤ q) {C : ℝ}
    (hcurl : ∀ n, CurlBoundedBy T q C (U n)) :
    ∀ n t, t ∈ Icc 0 T → ‖U n t‖ ≤ 2 * (torusLqToL2Bound q C + B) := by
  intro n t ht
  obtain ⟨ω, hω, hc, hωbound⟩ := hcurl n t ht
  calc
    ‖U n t‖ ≤ 2 * ((eLpNorm ω 2 μT).toReal + ‖u₀ n‖) :=
      norm_velocity_le_of_curl_and_mean (U n t) (u₀ n) ((hU n).divFree t ht)
        ω (hω.mono_exponent hq) hc ((hU n).integral_eq_initial hT ht)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (l2_bound_of_memLp_bound hq hω hωbound) (hinit n)) (by norm_num)

end Euler2D

end
