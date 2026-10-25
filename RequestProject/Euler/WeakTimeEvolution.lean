module

public import RequestProject.Euler.TimeWeakDerivative
public import RequestProject.Euler.StationaryLimit

/-!
# Time evolution of smooth spatial test pairings

The integral evolution follows from the original space-time weak Euler
equation. It is not assumed as a second definition of weak solution.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff NNReal

namespace Euler2D

def eulerSpatialPairing (ψ : R2 → R2) (v : L2T) : ℝ :=
  ∑ i : Fin 2, ∫ x in torusBox, v x i * ψ x i

def eulerSpatialFlux (ψ : R2 → R2) (v : L2T) : ℝ :=
  ∫ x in torusBox, ∑ i, ∑ j, v x i * v x j * pd j ψ x i

lemma continuous_eulerSpatialPairing {ψ : R2 → R2} (hψ : Continuous ψ) :
    Continuous (eulerSpatialPairing ψ) := by
  apply continuous_finset_sum
  intro i _
  apply continuous_iff_continuousAt.mpr
  intro v
  exact tendsto_fixed_lin tendsto_id
    ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp hψ) i

lemma continuous_eulerSpatialFlux {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (eulerSpatialFlux ψ) := continuous_stationary_pairing hψ

def separableEulerField (η : ℝ → ℝ) (ψ : R2 → R2) (t : ℝ) (x : R2) : R2 :=
  η t • ψ x

lemma pd_separableEulerField (η : ℝ → ℝ) (ψ : R2 → R2)
    (t : ℝ) (x : R2) (j : Fin 2) :
    pd j (separableEulerField η ψ t) x = η t • pd j ψ x := by
  unfold pd separableEulerField
  rw [show (fun y => η t • ψ y) = η t • ψ from rfl, fderiv_const_smul_field]
  rfl

lemma deriv_separableEulerField {η : ℝ → ℝ} (hη : Differentiable ℝ η)
    (ψ : R2 → R2) (t : ℝ) (x : R2) (i : Fin 2) :
    deriv (fun s => separableEulerField η ψ s x i) t = deriv η t * ψ x i := by
  exact ((hη t).hasDerivAt.mul_const (ψ x i)).deriv

lemma isEulerTest_separable {T : ℝ} {η : ℝ → ℝ} (hη : IsTimeTest T η)
    {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ) (hp : IsTorusPeriodic ψ)
    (hd : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) :
    IsEulerTest T (separableEulerField η ψ) := by
  refine ⟨(hη.1.comp contDiff_fst).smul (hψ.comp contDiff_snd), ?_, ?_, ?_⟩
  · intro t x i
    change η t • ψ (x + EuclideanSpace.single i (2 * Real.pi)) = η t • ψ x
    rw [hp]
  · intro t x
    rw [pd_separableEulerField, pd_separableEulerField]
    simp only [PiLp.smul_apply, smul_eq_mul, ← mul_add, hd, mul_zero]
  · obtain ⟨b, hb, hs⟩ := hη.2
    exact ⟨b, hb, fun t ht x => by simp [separableEulerField, hs t ht]⟩

lemma integral_separableEulerField_pairing (η : ℝ → ℝ) {ψ : R2 → R2}
    (hψ : ContDiff ℝ ∞ ψ) (v : L2T) (t : ℝ) :
    (∫ x in torusBox, ∑ i, v x i * separableEulerField η ψ t x i) =
      η t * eulerSpatialPairing ψ v := by
  have hI (i : Fin 2) : Integrable (fun x => v x i * ψ x i) μT := by
    obtain ⟨C, hC⟩ := bound_on_box
      ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp hψ.continuous)
    exact integrable_lin v i
      ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp hψ.continuous).aestronglyMeasurable hC
  have heq (x : R2) : (∑ i, v x i * separableEulerField η ψ t x i) =
      η t * ∑ i, v x i * ψ x i := by
    simp only [separableEulerField, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [heq]
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => hI i)]
  rfl

lemma integral_separableEulerField_integrand {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ) (v : L2T) (t : ℝ) :
    (∫ x in torusBox, eulerIntegrand v (separableEulerField η ψ) t x) =
      eulerSpatialPairing ψ v * deriv η t + eulerSpatialFlux ψ v * η t := by
  have hc : ContDiff ℝ 1 (Function.uncurry (separableEulerField η ψ)) :=
    ((hη.comp contDiff_fst).smul (hψ.comp contDiff_snd)).of_le (by exact_mod_cast le_top)
  have hconst : ContDiff ℝ 1 (Function.uncurry fun _t : ℝ => ψ) :=
    (hψ.of_le (by exact_mod_cast le_top)).comp contDiff_snd
  rw [integral_eulerIntegrand_eq hc]
  simp_rw [deriv_separableEulerField (hη.differentiable (by simp)), pd_separableEulerField]
  simp only [PiLp.smul_apply, smul_eq_mul]
  have hlin (i : Fin 2) :
      (∫ x in torusBox, v x i * (deriv η t * ψ x i)) =
        deriv η t * ∫ x in torusBox, v x i * ψ x i := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hquad (i j : Fin 2) :
      (∫ x in torusBox, v x i * v x j * (η t * pd j ψ x i)) =
        η t * ∫ x in torusBox, v x i * v x j * pd j ψ x i := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  simp_rw [hlin, hquad]
  rw [← Finset.mul_sum]
  simp_rw [← Finset.mul_sum]
  rw [← quad_sum_integral hconst v t]
  change deriv η t * eulerSpatialPairing ψ v + η t * eulerSpatialFlux ψ v = _
  ring

/-- Every weak Euler solution satisfies the initial-value evolution
formula for every fixed smooth periodic divergence-free spatial test. -/
theorem IsWeakEulerSolution.spatial_test_evolution {T : ℝ} (hT : 0 < T)
    {u₀ : L2T} {U : ℝ → L2T} (hU : IsWeakEulerSolution T u₀ U)
    {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ) (hp : IsTorusPeriodic ψ)
    (hd : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) :
    ∀ t ∈ Icc 0 T, eulerSpatialPairing ψ (U t) =
      eulerSpatialPairing ψ u₀ + ∫ s in (0 : ℝ)..t, eulerSpatialFlux ψ (U s) := by
  let V := extendPath hT.le U
  have hVc : Continuous V := extendPath_continuous hT.le hU.continuous
  have hVeq (t : ℝ) (ht : t ∈ Icc 0 T) : V t = U t := extendPath_eq hT.le U ht
  have hV0 : V 0 = u₀ := (hVeq 0 ⟨le_rfl, hT.le⟩).trans hU.initial
  have hweak : ∀ η : ℝ → ℝ, IsTimeTest T η →
      (∫ t in (0 : ℝ)..T, eulerSpatialPairing ψ (V t) * deriv η t +
        eulerSpatialFlux ψ (V t) * η t) + eulerSpatialPairing ψ (V 0) * η 0 = 0 := by
    intro η hη
    have hw := hU.weak _ (isEulerTest_separable hη hψ hp hd)
    simp_rw [integral_separableEulerField_integrand hη.1 hψ,
      integral_separableEulerField_pairing η hψ] at hw
    rw [hV0]
    rw [show (∫ t in (0 : ℝ)..T, eulerSpatialPairing ψ (V t) * deriv η t +
        eulerSpatialFlux ψ (V t) * η t) =
        ∫ t in (0 : ℝ)..T, eulerSpatialPairing ψ (U t) * deriv η t +
          eulerSpatialFlux ψ (U t) * η t from by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [hVeq t (by simpa only [uIcc_of_le hT.le] using ht)]]
    simpa only [mul_comm] using hw
  have hformula := eq_integral_of_weak_time_identity hT
    ((continuous_eulerSpatialPairing hψ.continuous).comp hVc)
    ((continuous_eulerSpatialFlux hψ).comp hVc) hweak
  intro t ht
  have hft := hformula t ht
  simp only [Function.comp_def] at hft
  rw [hVeq t ht, hV0] at hft
  rw [hft]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [hVeq s]
  exact Icc_subset_Icc le_rfl ht.2 (by simpa only [uIcc_of_le ht.1] using hs)

lemma abs_eulerSpatialFlux_le {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ)
    {C : ℝ} (hC : ∀ i j x, x ∈ torusBox → |pd j ψ x i| ≤ C) (v : L2T) :
    |eulerSpatialFlux ψ v| ≤ 4 * C * ‖v‖ ^ 2 := by
  have hc : ContDiff ℝ 1 (Function.uncurry fun _t : ℝ => ψ) :=
    (hψ.of_le (by exact_mod_cast le_top)).comp contDiff_snd
  unfold eulerSpatialFlux
  rw [quad_sum_integral hc v 0]
  calc
    _ ≤ ∑ i : Fin 2, |∑ j : Fin 2, ∫ x in torusBox, v x i * v x j * pd j ψ x i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, |∫ x in torusBox, v x i * v x j * pd j ψ x i| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, C * (‖v‖ * ‖v‖) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        abs_integral_bilin_le v v i j (hC i j)
    _ = _ := by simp; ring

/-- The spatial mean is conserved by the original weak Euler definition. -/
theorem IsWeakEulerSolution.integral_eq_initial {T : ℝ} (hT : 0 < T)
    {u₀ : L2T} {U : ℝ → L2T} (hU : IsWeakEulerSolution T u₀ U)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ x in torusBox, U t x) = ∫ x in torusBox, u₀ x := by
  have hcoord (v : L2T) (i : Fin 2) :
      (∫ x in torusBox, v x) i = ∫ x in torusBox, v x i :=
    ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).integral_comp_comm
      ((Lp.memLp v).integrable (by norm_num))).symm
  ext i
  rw [hcoord, hcoord]
  let ψ : R2 → R2 := fun _ => EuclideanSpace.single i 1
  have hψ : ContDiff ℝ ∞ ψ := contDiff_const
  have hp : IsTorusPeriodic ψ := fun _ _ => rfl
  have hd : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0 := by simp [ψ, pd]
  have hflux (v : L2T) : eulerSpatialFlux ψ v = 0 := by
    simp [eulerSpatialFlux, ψ, pd]
  have hpair (v : L2T) : eulerSpatialPairing ψ v = ∫ x in torusBox, v x i := by
    fin_cases i <;> simp [eulerSpatialPairing, ψ, EuclideanSpace.single_apply, Fin.sum_univ_two]
  have he := hU.spatial_test_evolution hT hψ hp hd t ht
  simpa only [hpair, hflux, intervalIntegral.integral_zero, add_zero] using he

theorem IsWeakEulerSolution.spatial_test_difference {T : ℝ} (hT : 0 < T)
    {u₀ : L2T} {U : ℝ → L2T} (hU : IsWeakEulerSolution T u₀ U)
    {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ) (hp : IsTorusPeriodic ψ)
    (hd : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    eulerSpatialPairing ψ (U t) - eulerSpatialPairing ψ (U s) =
      ∫ r in s..t, eulerSpatialFlux ψ (U r) := by
  have hB : ContinuousOn (fun r => eulerSpatialFlux ψ (U r)) (Icc 0 T) :=
    (continuous_eulerSpatialFlux hψ).comp_continuousOn hU.continuous
  calc
    _ = (eulerSpatialPairing ψ u₀ + ∫ r in (0 : ℝ)..t, eulerSpatialFlux ψ (U r)) -
        (eulerSpatialPairing ψ u₀ + ∫ r in (0 : ℝ)..s, eulerSpatialFlux ψ (U r)) := by
      rw [hU.spatial_test_evolution hT hψ hp hd t ht,
        hU.spatial_test_evolution hT hψ hp hd s hs]
    _ = (∫ r in (0 : ℝ)..t, eulerSpatialFlux ψ (U r)) -
        ∫ r in (0 : ℝ)..s, eulerSpatialFlux ψ (U r) := by ring
    _ = _ := intervalIntegral.integral_interval_sub_left
      ((hB.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
      ((hB.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1)

lemma exists_spatial_derivative_bound {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j x, x ∈ torusBox → |pd j ψ x i| ≤ C := by
  have hex (i j : Fin 2) : ∃ C : ℝ, ∀ x ∈ torusBox, |pd j ψ x i| ≤ C :=
    bound_on_box ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const))
  choose C hC using hex
  let B := ∑ i : Fin 2, ∑ j : Fin 2, max (C i j) 0
  have hnon (i : Fin 2) : 0 ≤ ∑ j : Fin 2, max (C i j) 0 :=
    Finset.sum_nonneg fun j _ => le_max_right _ _
  refine ⟨B, Finset.sum_nonneg (fun i _ => hnon i), fun i j x hx => ?_⟩
  exact (hC i j x hx).trans ((le_max_left _ _).trans
    ((Finset.single_le_sum (fun k _ => le_max_right (C i k) 0) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => hnon k) (Finset.mem_univ i))))

/-- A common energy bound gives a common Lipschitz constant for each
fixed solenoidal test pairing, directly from the weak equation. The
constant may depend on the test and is independent of the solution index. -/
theorem uniform_lipschitz_spatial_test_pairings {T : ℝ} (hT : 0 < T)
    {U : ℕ → ℝ → L2T} {u₀ : ℕ → L2T}
    (hU : ∀ n, IsWeakEulerSolution T (u₀ n) (U n))
    {M : ℝ} (hbound : ∀ n t, t ∈ Icc 0 T → ‖U n t‖ ≤ M)
    {ψ : R2 → R2} (hψ : ContDiff ℝ ∞ ψ) (hp : IsTorusPeriodic ψ)
    (hd : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) :
    ∃ L : ℝ≥0, ∀ n, LipschitzWith L
      (fun t : Icc (0 : ℝ) T => eulerSpatialPairing ψ (U n t)) := by
  obtain ⟨C, hC0, hC⟩ := exists_spatial_derivative_bound hψ
  refine ⟨NNReal.mk (4 * C * M ^ 2) (by positivity),
    fun n => LipschitzWith.of_dist_le_mul fun t s => ?_⟩
  rw [dist_eq_norm, (hU n).spatial_test_difference hT hψ hp hd s.property t.property]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := (s : ℝ)) (b := (t : ℝ))
    (C := 4 * C * M ^ 2) (f := fun r => eulerSpatialFlux ψ (U n r)) (fun r hr => by
      have hmem : r ∈ Icc 0 T :=
        ⟨(le_min s.property.1 t.property.1).trans (uIoc_subset_uIcc hr).1,
          (uIoc_subset_uIcc hr).2.trans (max_le s.property.2 t.property.2)⟩
      rw [Real.norm_eq_abs]
      apply (abs_eulerSpatialFlux_le hψ hC (U n r)).trans
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hC0)
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound n r hmem) 2)
  simpa only [Subtype.dist_eq, Real.dist_eq, NNReal.coe_mk] using hn

end Euler2D

end
