module

public import RequestProject.Euler.TorusL2

/-!
# Spatial compactness in the actual Euler torus model

Coordinate complexification and the normalized torus isometry transfer the
actual distributional div--curl equations to Fourier coefficients. Finite
Fourier projections therefore approximate a bounded-curl family uniformly.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

/-- Complexification of one actual velocity coordinate. -/
def boxComplexCoord (j : Fin 2) : L2T →L[ℝ] BoxFourierL2 :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj j)).compLpL 2 μT

lemma coeFn_boxComplexCoord (j : Fin 2) (u : L2T) :
    boxComplexCoord j u =ᵐ[μT] fun x => (u x j : ℂ) :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj j)).coeFn_compLpL u

lemma integrable_velocity_coord (u : L2T) (j : Fin 2) :
    Integrable (fun x => u x j) μT :=
  ((EuclideanSpace.proj j : R2 →L[ℝ] ℝ).comp_memLp u).integrable (by norm_num)

/-- A real vorticity function viewed as a scalar complex `L²` element. -/
def boxVorticity (ω : R2 → ℝ) (hω : MemLp ω 2 μT) : BoxFourierL2 :=
  (hω.ofReal : MemLp (fun x => (ω x : ℂ)) 2 μT).toLp _

lemma coeFn_boxVorticity (ω : R2 → ℝ) (hω : MemLp ω 2 μT) :
    boxVorticity ω hω =ᵐ[μT] fun x => (ω x : ℂ) :=
  (hω.ofReal : MemLp (fun x => (ω x : ℂ)) 2 μT).coeFn_toLp

lemma norm_boxVorticity (ω : R2 → ℝ) (hω : MemLp ω 2 μT) :
    ‖boxVorticity ω hω‖ = (eLpNorm ω 2 μT).toReal := by
  rw [boxVorticity, Lp.norm_toLp]
  congr 1
  exact eLpNorm_congr_norm_ae
    (hω.ofReal : MemLp (fun x => (ω x : ℂ)) 2 μT).aestronglyMeasurable
    hω.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by simp)

lemma mFourierCoeff_const_mul (c : ℂ) (f : UnitAddTorus (Fin 2) → ℂ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun t => c * f t) k =
      c * UnitAddTorus.mFourierCoeff f k := by
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

/-- The isometric lift has coefficient `(2π)⁻¹` times the actual box coefficient. -/
lemma mFourierCoeff_torusL2Equiv_real {f : R2 → ℝ} {v : BoxFourierL2}
    (hv : v =ᵐ[μT] fun x => (f x : ℂ)) (hf : Integrable f μT) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (torusL2Equiv v) k =
      (2 * π : ℂ)⁻¹ * boxFourierCoeff f k := by
  have hae : torusL2Equiv v =ᵐ[volume] fun t => (2 * π : ℂ) * (f (torusRep t) : ℂ) := by
    filter_upwards [coeFn_torusLiftFn v, ae_eq_comp_torusRep hv] with t ht hf
    change torusLiftFn v t = _
    simp only [Function.comp_def] at hf
    rw [ht, hf]
  calc
    UnitAddTorus.mFourierCoeff (torusL2Equiv v) k =
        UnitAddTorus.mFourierCoeff (fun t => (2 * π : ℂ) * (f (torusRep t) : ℂ)) k := by
      apply integral_congr_ae
      filter_upwards [hae] with t ht
      simp only [ht]
    _ = (2 * π : ℂ) * UnitAddTorus.mFourierCoeff (fun t => (f (torusRep t) : ℂ)) k :=
      mFourierCoeff_const_mul _ _ _
    _ = (2 * π : ℂ)⁻¹ * boxFourierCoeff f k := by
      rw [mFourierCoeff_torusRep hf]
      simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow,
        Complex.ofReal_mul, Complex.ofReal_ofNat]
      field_simp

lemma mFourierCoeff_velocity_coord (u : L2T) (j : Fin 2) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord j u)) k =
      (2 * π : ℂ)⁻¹ * boxFourierCoeff (fun x => u x j) k :=
  mFourierCoeff_torusL2Equiv_real (coeFn_boxComplexCoord j u)
    (integrable_velocity_coord u j) k

lemma mFourierCoeff_vorticity (ω : R2 → ℝ) (hω : MemLp ω 2 μT) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (torusL2Equiv (boxVorticity ω hω)) k =
      (2 * π : ℂ)⁻¹ * boxFourierCoeff ω k :=
  mFourierCoeff_torusL2Equiv_real (coeFn_boxVorticity ω hω)
    (hω.integrable (by norm_num)) k

/-- The original distributional divergence identity survives the normalized lift. -/
lemma lifted_div_identity (u : L2T) (hu : DivFree u) (k : Fin 2 → ℤ) :
    (k 0 : ℂ) * UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 0 u)) k +
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 1 u)) k = 0 := by
  rw [mFourierCoeff_velocity_coord, mFourierCoeff_velocity_coord]
  calc
    _ = (2 * π : ℂ)⁻¹ * ((k 0 : ℂ) * boxFourierCoeff (fun x => u x 0) k +
        (k 1 : ℂ) * boxFourierCoeff (fun x => u x 1) k) := by ring
    _ = 0 := by rw [boxFourier_div_identity u hu k, mul_zero]

/-- The physical curl identity has no additional coordinate factor when all
three fields use the same normalized isometric lift. -/
lemma lifted_curl_identity (u : L2T) (ω : R2 → ℝ) (hω : MemLp ω 2 μT)
    (hc : IsCurl u ω) (k : Fin 2 → ℤ) :
    Complex.I * ((k 0 : ℂ) * UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 1 u)) k -
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 0 u)) k) =
        UnitAddTorus.mFourierCoeff (torusL2Equiv (boxVorticity ω hω)) k := by
  rw [mFourierCoeff_velocity_coord, mFourierCoeff_velocity_coord, mFourierCoeff_vorticity]
  calc
    _ = (2 * π : ℂ)⁻¹ * (Complex.I * ((k 0 : ℂ) * boxFourierCoeff (fun x => u x 1) k -
        (k 1 : ℂ) * boxFourierCoeff (fun x => u x 0) k)) := by ring
    _ = _ := by rw [boxFourier_curl_identity u ω hc k]

/-- The actual curl bounds the finite weighted Fourier coefficient sums. -/
lemma lifted_velocity_weighted_bound (u : L2T) (hu : DivFree u)
    (ω : R2 → ℝ) (hω : MemLp ω 2 μT) (hc : IsCurl u ω)
    (s : Finset (Fin 2 → ℤ)) :
    ∑ k ∈ s, frequencySq k *
      (‖UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 0 u)) k‖ ^ 2 +
       ‖UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 1 u)) k‖ ^ 2) ≤
        (eLpNorm ω 2 μT).toReal ^ 2 := by
  have hp (k : Fin 2 → ℤ) : frequencySq k *
      (‖UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 0 u)) k‖ ^ 2 +
       ‖UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 1 u)) k‖ ^ 2) =
        ‖UnitAddTorus.mFourierCoeff (torusL2Equiv (boxVorticity ω hω)) k‖ ^ 2 := by
    rw [fourier_div_curl_identity, lifted_div_identity u hu, norm_zero,
      zero_pow (by decide : 2 ≠ 0), zero_add]
    rw [← lifted_curl_identity u ω hω hc k, norm_mul, Complex.norm_I, one_mul]
  simp_rw [hp]
  have hb := UnitAddTorus.mFourierBasis.orthonormal.sum_inner_products_le
    (torusL2Equiv (boxVorticity ω hω)) (s := s)
  simpa only [← UnitAddTorus.mFourierBasis_repr, HilbertBasis.repr_apply_apply,
    torusL2Equiv.norm_map, norm_boxVorticity] using hb

/-- Each actual coordinate has truncation error at most `‖curl u‖₂/N`. -/
lemma norm_sub_scalarTrunc_velocity (N : ℕ) (hN : 0 < N) (u : L2T) (hu : DivFree u)
    (ω : R2 → ℝ) (hω : MemLp ω 2 μT) (hc : IsCurl u ω) (j : Fin 2) :
    ‖boxComplexCoord j u - boxScalarFourierTrunc N (boxComplexCoord j u)‖ ≤
      (eLpNorm ω 2 μT).toReal / N := by
  rw [norm_sub_boxScalarFourierTrunc]
  apply norm_sub_fourierTrunc_le N hN _ ENNReal.toReal_nonneg
  intro s
  apply le_trans _ (lifted_velocity_weighted_bound u hu ω hω hc s)
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (frequencySq_nonneg k)
  fin_cases j
  · exact le_add_of_nonneg_right (sq_nonneg _)
  · exact le_add_of_nonneg_left (sq_nonneg _)


/-- The real part of a scalar field, inserted into one velocity coordinate. -/
def realCoordInjection (j : Fin 2) : ℂ →L[ℝ] R2 :=
  Complex.reCLM.smulRight (EuclideanSpace.single j 1)

def boxRealCoordInjection (j : Fin 2) : BoxFourierL2 →L[ℝ] L2T :=
  (realCoordInjection j).compLpL 2 μT

lemma coeFn_boxRealCoordInjection (j : Fin 2) (f : BoxFourierL2) :
    boxRealCoordInjection j f =ᵐ[μT]
      fun x => (f x).re • EuclideanSpace.single j 1 :=
  (realCoordInjection j).coeFn_compLpL f

lemma norm_boxRealCoordInjection_le (j : Fin 2) (f : BoxFourierL2) :
    ‖boxRealCoordInjection j f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_boxRealCoordInjection j f] with x hx
  rw [hx, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

lemma boxRealCoordInjection_coords (u : L2T) :
    boxRealCoordInjection 0 (boxComplexCoord 0 u) +
      boxRealCoordInjection 1 (boxComplexCoord 1 u) = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (boxRealCoordInjection 0 (boxComplexCoord 0 u))
      (boxRealCoordInjection 1 (boxComplexCoord 1 u)),
    coeFn_boxRealCoordInjection 0 (boxComplexCoord 0 u),
    coeFn_boxRealCoordInjection 1 (boxComplexCoord 1 u),
    coeFn_boxComplexCoord 0 u, coeFn_boxComplexCoord 1 u] with x hadd hi₀ hi₁ hc₀ hc₁
  rw [hadd]
  change boxRealCoordInjection 0 (boxComplexCoord 0 u) x +
    boxRealCoordInjection 1 (boxComplexCoord 1 u) x = u x
  rw [hi₀, hi₁, hc₀, hc₁]
  ext i
  fin_cases i <;> simp [EuclideanSpace.single_apply]

/-- One coordinate of a genuine finite Fourier approximation. -/
def boxVectorFourierTerm (N : ℕ) (j : Fin 2) : L2T →L[ℝ] L2T :=
  (boxRealCoordInjection j).comp
    (((boxScalarFourierTrunc N).restrictScalars ℝ).comp (boxComplexCoord j))

/-- An actual real finite-rank Fourier approximation of the velocity field. -/
def boxVectorFourierTrunc (N : ℕ) : L2T →L[ℝ] L2T :=
  boxVectorFourierTerm N 0 + boxVectorFourierTerm N 1

lemma boxScalarFourierTrunc_real_finiteDimensional_range (N : ℕ) :
    FiniteDimensional ℝ
      (LinearMap.range ((boxScalarFourierTrunc N).restrictScalars ℝ).toLinearMap) := by
  letI := boxScalarFourierTrunc_finiteDimensional_range N
  change FiniteDimensional ℝ
    (LinearMap.range ((boxScalarFourierTrunc N).toLinearMap.restrictScalars ℝ))
  rw [LinearMap.range_restrictScalars]
  change FiniteDimensional ℝ (LinearMap.range (boxScalarFourierTrunc N).toLinearMap)
  exact Module.Finite.trans ℂ _

lemma boxVectorFourierTerm_finiteDimensional_range (N : ℕ) (j : Fin 2) :
    FiniteDimensional ℝ (LinearMap.range (boxVectorFourierTerm N j).toLinearMap) := by
  let P := LinearMap.range ((boxScalarFourierTrunc N).restrictScalars ℝ).toLinearMap
  letI : FiniteDimensional ℝ P := boxScalarFourierTrunc_real_finiteDimensional_range N
  letI : FiniteDimensional ℝ (P.map (boxRealCoordInjection j).toLinearMap) := inferInstance
  apply Submodule.finiteDimensional_of_le (S₂ := P.map (boxRealCoordInjection j).toLinearMap)
  rintro y ⟨u, rfl⟩
  exact ⟨boxScalarFourierTrunc N (boxComplexCoord j u),
    ⟨boxComplexCoord j u, rfl⟩, rfl⟩

lemma boxVectorFourierTrunc_finiteDimensional_range (N : ℕ) :
    FiniteDimensional ℝ (LinearMap.range (boxVectorFourierTrunc N).toLinearMap) := by
  letI := boxVectorFourierTerm_finiteDimensional_range N 0
  letI := boxVectorFourierTerm_finiteDimensional_range N 1
  change FiniteDimensional ℝ (LinearMap.range
    ((boxVectorFourierTerm N 0).toLinearMap + (boxVectorFourierTerm N 1).toLinearMap))
  exact Submodule.finiteDimensional_of_le (LinearMap.range_add_le _ _)

/-- A quantitative actual-vector Fourier tail controlled by the actual curl. -/
lemma norm_sub_boxVectorFourierTrunc_le (N : ℕ) (hN : 0 < N)
    (u : L2T) (hu : DivFree u) (ω : R2 → ℝ) (hω : MemLp ω 2 μT) (hc : IsCurl u ω) :
    ‖u - boxVectorFourierTrunc N u‖ ≤ 2 * (eLpNorm ω 2 μT).toReal / N := by
  have heq : u - boxVectorFourierTrunc N u =
      boxRealCoordInjection 0 (boxComplexCoord 0 u - boxScalarFourierTrunc N (boxComplexCoord 0 u)) +
      boxRealCoordInjection 1 (boxComplexCoord 1 u - boxScalarFourierTrunc N (boxComplexCoord 1 u)) := by
    calc
      _ = (boxRealCoordInjection 0 (boxComplexCoord 0 u) +
          boxRealCoordInjection 1 (boxComplexCoord 1 u)) - boxVectorFourierTrunc N u := by
        rw [boxRealCoordInjection_coords]
      _ = _ := by
        simp only [boxVectorFourierTrunc, boxVectorFourierTerm, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.comp_apply, map_sub]
        abel
  rw [heq]
  calc
    _ ≤ ‖boxRealCoordInjection 0 (boxComplexCoord 0 u - boxScalarFourierTrunc N (boxComplexCoord 0 u))‖ +
        ‖boxRealCoordInjection 1 (boxComplexCoord 1 u - boxScalarFourierTrunc N (boxComplexCoord 1 u))‖ :=
      norm_add_le _ _
    _ ≤ ‖boxComplexCoord 0 u - boxScalarFourierTrunc N (boxComplexCoord 0 u)‖ +
        ‖boxComplexCoord 1 u - boxScalarFourierTrunc N (boxComplexCoord 1 u)‖ :=
      add_le_add (norm_boxRealCoordInjection_le 0 _) (norm_boxRealCoordInjection_le 1 _)
    _ ≤ (eLpNorm ω 2 μT).toReal / N + (eLpNorm ω 2 μT).toReal / N :=
      add_le_add (norm_sub_scalarTrunc_velocity N hN u hu ω hω hc 0)
        (norm_sub_scalarTrunc_velocity N hN u hu ω hω hc 1)
    _ = _ := by ring

/-- Bounded velocity families with a common actual `L²` curl bound are totally
bounded in the original fundamental-square `L²` model. -/
theorem totallyBounded_of_curl_L2_bound {s : Set L2T}
    (hs : Bornology.IsBounded s) {M : ℝ} (_hM : 0 ≤ M)
    (hcurl : ∀ u ∈ s, DivFree u ∧ ∃ ω : R2 → ℝ,
      MemLp ω 2 μT ∧ IsCurl u ω ∧ (eLpNorm ω 2 μT).toReal ≤ M) :
    TotallyBounded s := by
  apply totallyBounded_of_finiteRank_approx hs boxVectorFourierTrunc
    boxVectorFourierTrunc_finiteDimensional_range
  intro ε hε
  have hlim := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (2 * M)
  obtain ⟨N, hnear, hN⟩ := ((hlim.eventually (gt_mem_nhds hε)).and
    (eventually_gt_atTop (0 : ℕ))).exists
  refine ⟨N, ?_⟩
  intro u hu
  obtain ⟨hdiv, ω, hω, hc, hbound⟩ := hcurl u hu
  calc
    ‖u - boxVectorFourierTrunc N u‖ ≤ 2 * (eLpNorm ω 2 μT).toReal / N :=
      norm_sub_boxVectorFourierTrunc_le N hN u hdiv ω hω hc
    _ ≤ 2 * M / N := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbound (by norm_num)) (by positivity)
    _ < ε := hnear



/-- The same spatial compactness follows directly from a common `L^q` curl
bound for any `q ≥ 2`, including `q = ∞`. -/
theorem totallyBounded_of_curl_Lq_bound {s : Set L2T}
    (hs : Bornology.IsBounded s) {q : ENNReal} (hq : 2 ≤ q) {M : ℝ}
    (hcurl : ∀ u ∈ s, DivFree u ∧ ∃ ω : R2 → ℝ,
      MemLp ω q μT ∧ IsCurl u ω ∧ (eLpNorm ω q μT).toReal ≤ M) :
    TotallyBounded s := by
  have hexp : 0 ≤ 1 / (2 : ℝ) - 1 / q.toReal := by
    by_cases ht : q = ∞
    · simp [ht]
    have hqr : (2 : ℝ) ≤ q.toReal := by
      simpa using ENNReal.toReal_mono ht hq
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hqr)
  let C : ENNReal := ENNReal.ofReal M * μT univ ^ (1 / (2 : ℝ) - 1 / q.toReal)
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μT univ))
  apply totallyBounded_of_curl_L2_bound hs (M := C.toReal) ENNReal.toReal_nonneg
  intro u hu
  obtain ⟨hdiv, ω, hω, hc, hbound⟩ := hcurl u hu
  refine ⟨hdiv, ω, hω.mono_exponent hq, hc, ?_⟩
  have hqnorm : eLpNorm ω q μT ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_toReal hω.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hbound
  apply ENNReal.toReal_mono hC
  calc
    eLpNorm ω 2 μT ≤ eLpNorm ω q μT * μT univ ^ (1 / (2 : ℝ) - 1 / q.toReal) := by
      simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq hω.aestronglyMeasurable
    _ ≤ C := mul_le_mul_left hqnorm _



/-- Uniform spatial curl bounds and uniform time Lipschitz estimates give
strong uniform compactness for actual Euler velocity paths. -/
theorem compactness_of_uniform_curl_bounds
    {A : Type*} [PseudoMetricSpace A] [CompactSpace A]
    (U : ℕ → A → L2T) (L : ℝ≥0) (hlip : ∀ n, LipschitzWith L (U n))
    {M : ℝ} (hbound : ∀ n t, ‖U n t‖ ≤ M)
    {q : ENNReal} (hq : 2 ≤ q) {C : ℝ}
    (hcurl : ∀ n t, DivFree (U n t) ∧ ∃ ω : R2 → ℝ,
      MemLp ω q μT ∧ IsCurl (U n t) ω ∧ (eLpNorm ω q μT).toReal ≤ C) :
    ∃ u : A → L2T, Continuous u ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformly (fun n => U (φ n)) u atTop := by
  let s : Set L2T := Set.range (fun p : ℕ × A => U p.1 p.2)
  have hs : Bornology.IsBounded s := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro u ⟨⟨n, t⟩, rfl⟩
    exact hbound n t
  have hst : TotallyBounded s := by
    apply totallyBounded_of_curl_Lq_bound hs hq
    rintro u ⟨⟨n, t⟩, rfl⟩
    exact hcurl n t
  exact uniform_subseq_of_totallyBounded U L hlip hst
    (fun n t => Set.mem_range_self (n, t))


end Euler2D

end





