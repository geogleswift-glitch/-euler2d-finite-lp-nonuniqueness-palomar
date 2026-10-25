module

public import RequestProject.Euler.Compactness
public import RequestProject.Euler.WeakAux
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Finite Fourier projections and quantitative tails on the two-dimensional torus

The measure on the unit quotient torus in this file is normalized Haar measure.
The operators below are actual finite sums of Fourier modes, rather than an
assumed family of compact approximations.  The weighted estimate is the
spectral estimate needed after the distributional div--curl identities have
been transferred from the fundamental square to the quotient torus.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

namespace FourierProjection

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 E)

/-- The orthogonal projection retaining precisely a finite set of basis modes. -/
def trunc (s : Finset ι) : E →L[𝕜] E :=
  ∑ i ∈ s, (innerSL 𝕜 (b i)).smulRight (b i)

theorem trunc_apply (s : Finset ι) (x : E) :
    trunc b s x = ∑ i ∈ s, b.repr x i • b i := by
  simp [trunc, HilbertBasis.repr_apply_apply]

theorem trunc_mem_span (s : Finset ι) (x : E) :
    trunc b s x ∈ Submodule.span 𝕜 (b '' (s : Set ι)) := by
  rw [trunc_apply]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem finiteDimensional_range (s : Finset ι) :
    FiniteDimensional 𝕜 (LinearMap.range (trunc b s).toLinearMap) := by
  let P := Submodule.span 𝕜 (b '' (s : Set ι))
  letI : FiniteDimensional 𝕜 P :=
    FiniteDimensional.span_of_finite 𝕜 ((Finset.finite_toSet s).image b)
  apply FiniteDimensional.of_injective
    (Submodule.inclusion (show LinearMap.range (trunc b s).toLinearMap ≤ P from by
      rintro y ⟨x, rfl⟩
      exact trunc_mem_span b s x))
  exact Submodule.inclusion_injective _

theorem repr_trunc [DecidableEq ι] (s : Finset ι) (x : E) (i : ι) :
    b.repr (trunc b s x) i = if i ∈ s then b.repr x i else 0 := by
  rw [trunc_apply, map_sum]
  simp only [map_smul, HilbertBasis.repr_self, lp.coeFn_sum, lp.coeFn_smul,
    Finset.sum_apply, Pi.smul_apply, lp.single_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

theorem repr_sub_trunc [DecidableEq ι] (s : Finset ι) (x : E) (i : ι) :
    b.repr (x - trunc b s x) i = if i ∈ s then 0 else b.repr x i := by
  rw [map_sub]
  change b.repr x i - b.repr (trunc b s x) i = _
  rw [repr_trunc]
  split_ifs <;> simp

theorem norm_sq_eq_tsum (x : E) :
    ‖x‖ ^ 2 = ∑' i, ‖b.repr x i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    (b.repr x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] using h

/-- Exact Parseval tail identity for finite orthogonal projection. -/
theorem norm_sub_trunc_sq [DecidableEq ι] (s : Finset ι) (x : E) :
    ‖x - trunc b s x‖ ^ 2 =
      ∑' i, if i ∈ s then 0 else ‖b.repr x i‖ ^ 2 := by
  rw [norm_sq_eq_tsum b]
  congr 1
  funext i
  rw [repr_sub_trunc]
  split_ifs <;> simp

/-- A lower frequency bound and a weighted coefficient bound give a uniform
projection error.  A bound on all finite weighted sums suffices, so no
summability assumption on derivatives is hidden in the statement. -/
theorem norm_sub_trunc_le_of_weighted [DecidableEq ι]
    (s : Finset ι) (x : E) (w : ι → ℝ) {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hw : ∀ i, 0 ≤ w i)
    (hout : ∀ i ∉ s, r ^ 2 ≤ w i)
    (hbound : ∀ t : Finset ι, ∑ i ∈ t, w i * ‖b.repr x i‖ ^ 2 ≤ M ^ 2) :
    ‖x - trunc b s x‖ ≤ M / r := by
  have hsq : ‖x - trunc b s x‖ ^ 2 ≤ (M / r) ^ 2 := by
    rw [norm_sub_trunc_sq]
    apply Real.tsum_le_of_sum_le
    · intro i
      change 0 ≤ (if i ∈ s then 0 else ‖b.repr x i‖ ^ 2)
      split_ifs <;> positivity
    · intro t
      have hterm : ∀ i, r ^ 2 * (if i ∈ s then 0 else ‖b.repr x i‖ ^ 2) ≤
          w i * ‖b.repr x i‖ ^ 2 := by
        intro i
        split_ifs with hi
        · simpa using mul_nonneg (hw i) (sq_nonneg ‖b.repr x i‖)
        · exact mul_le_mul_of_nonneg_right (hout i hi) (sq_nonneg _)
      have hsum : r ^ 2 * (∑ i ∈ t, if i ∈ s then 0 else ‖b.repr x i‖ ^ 2) ≤ M ^ 2 := by
        calc
          _ = ∑ i ∈ t, r ^ 2 * (if i ∈ s then 0 else ‖b.repr x i‖ ^ 2) := by rw [Finset.mul_sum]
          _ ≤ ∑ i ∈ t, w i * ‖b.repr x i‖ ^ 2 := Finset.sum_le_sum fun i _ => hterm i
          _ ≤ M ^ 2 := hbound t
      rw [div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
      simpa [div_pow, mul_comm] using hsum
  exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg hM hr.le)).mp hsq

end FourierProjection

attribute [local instance] instMeasureSpaceUnitAddCircle

/-- Scalar complex `L²` on the normalized two-dimensional quotient torus. -/
abbrev FourierL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))

/-- Fourier frequencies retained in the square `[-N,N]²`. -/
def fourierModes (N : ℕ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem mem_fourierModes (N : ℕ) (k : Fin 2 → ℤ) :
    k ∈ fourierModes N ↔ ∀ i, -(N : ℤ) ≤ k i ∧ k i ≤ N := by
  simp [fourierModes, Fintype.mem_piFinset]

/-- The continuous linear square Fourier truncation. -/
def fourierTrunc (N : ℕ) : FourierL2 →L[ℂ] FourierL2 :=
  FourierProjection.trunc UnitAddTorus.mFourierBasis (fourierModes N)

theorem fourierTrunc_apply (N : ℕ) (f : FourierL2) :
    fourierTrunc N f = ∑ k ∈ fourierModes N,
      UnitAddTorus.mFourierCoeff f k • UnitAddTorus.mFourierLp 2 k := by
  simp [fourierTrunc, FourierProjection.trunc_apply, UnitAddTorus.mFourierBasis_repr]

theorem fourierTrunc_finiteDimensional_range (N : ℕ) :
    FiniteDimensional ℂ (LinearMap.range (fourierTrunc N).toLinearMap) :=
  FourierProjection.finiteDimensional_range _ _

/-- Parseval's exact tail identity for the square Fourier truncation. -/
theorem norm_sub_fourierTrunc_sq (N : ℕ) (f : FourierL2) :
    ‖f - fourierTrunc N f‖ ^ 2 =
      ∑' k, if k ∈ fourierModes N then 0 else ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
  simpa only [fourierTrunc, UnitAddTorus.mFourierBasis_repr] using
    FourierProjection.norm_sub_trunc_sq UnitAddTorus.mFourierBasis (fourierModes N) f

/-- Squared Euclidean Fourier frequency, with the `2π` normalization separated
from this arithmetic quantity. -/
def frequencySq (k : Fin 2 → ℤ) : ℝ := (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2

theorem frequencySq_nonneg (k : Fin 2 → ℤ) : 0 ≤ frequencySq k := by
  unfold frequencySq
  positivity

theorem frequencySq_ge_of_not_mem (N : ℕ) {k : Fin 2 → ℤ}
    (hk : k ∉ fourierModes N) : (N : ℝ) ^ 2 ≤ frequencySq k := by
  rw [mem_fourierModes, not_forall] at hk
  obtain ⟨i, hi⟩ := hk
  have hi' : (N : ℝ) ^ 2 ≤ (k i : ℝ) ^ 2 := by
    push_neg at hi
    by_cases h : -(N : ℤ) ≤ k i
    · have ht := hi h
      have ht' : (N : ℝ) < (k i : ℝ) := by exact_mod_cast ht
      nlinarith [sq_nonneg ((k i : ℝ) - N)]
    · have ht : k i < -(N : ℤ) := by omega
      have ht' : (k i : ℝ) < -(N : ℝ) := by exact_mod_cast ht
      nlinarith [sq_nonneg ((k i : ℝ) + N)]
  fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one] at hi' <;>
    simp only [frequencySq] <;> nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]

/-- A uniform spectral `H¹` bound gives the `M/N` Fourier tail estimate.
For a divergence-free velocity, the div--curl coefficient identities turn
the vorticity's `L²` bound into precisely the finite-sum hypothesis below. -/
theorem norm_sub_fourierTrunc_le (N : ℕ) (hN : 0 < N) (f : FourierL2)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s : Finset (Fin 2 → ℤ),
      ∑ k ∈ s, frequencySq k * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 ≤ M ^ 2) :
    ‖f - fourierTrunc N f‖ ≤ M / N := by
  apply FourierProjection.norm_sub_trunc_le_of_weighted _ _ f frequencySq
    (by exact_mod_cast hN) hM frequencySq_nonneg
    (fun k hk => frequencySq_ge_of_not_mem N hk)
  simpa only [UnitAddTorus.mFourierBasis_repr] using hbound

/-- A bounded family with a common Fourier `H¹` bound is totally bounded
in `L²`.  This is the spatial compactness needed for Euler approximation. -/
theorem totallyBounded_of_fourier_bound {s : Set FourierL2}
    (hs : Bornology.IsBounded s) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ f ∈ s, ∀ t : Finset (Fin 2 → ℤ),
      ∑ k ∈ t, frequencySq k * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 ≤ M ^ 2) :
    TotallyBounded s := by
  apply totallyBounded_of_finiteRank_approx hs fourierTrunc
    fourierTrunc_finiteDimensional_range
  intro ε hε
  have hlim := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) M
  obtain ⟨N, herr, hN⟩ := ((hlim.eventually (gt_mem_nhds hε)).and
    (eventually_gt_atTop (0 : ℕ))).exists
  exact ⟨N, fun f hf => (norm_sub_fourierTrunc_le N hN f hM (hbound f hf)).trans_lt herr⟩

/-- The frequency-by-frequency div--curl identity; it applies to the two
complex Fourier coefficients of a real velocity field as well. -/
theorem fourier_div_curl_identity (k : Fin 2 → ℤ) (a b : ℂ) :
    frequencySq k * (‖a‖ ^ 2 + ‖b‖ ^ 2) =
      ‖(k 0 : ℂ) * a + (k 1 : ℂ) * b‖ ^ 2 +
      ‖(k 0 : ℂ) * b - (k 1 : ℂ) * a‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    sub_zero, add_zero, frequencySq]
  ring

/-- The finite weighted velocity sum is bounded by the vorticity `L²` norm
once the Fourier div--curl identities have been established.  The factor
`2π` from a unit-period spatial derivative is included explicitly. -/
theorem fourier_velocity_weighted_bound (u₀ u₁ ω : FourierL2)
    (hdiv : ∀ k, (k 0 : ℂ) * UnitAddTorus.mFourierCoeff u₀ k +
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff u₁ k = 0)
    (hcurl : ∀ k, (2 * Real.pi : ℂ) * Complex.I *
      ((k 0 : ℂ) * UnitAddTorus.mFourierCoeff u₁ k -
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff u₀ k) = UnitAddTorus.mFourierCoeff ω k)
    (s : Finset (Fin 2 → ℤ)) :
    ∑ k ∈ s, frequencySq k *
      (‖UnitAddTorus.mFourierCoeff u₀ k‖ ^ 2 +
       ‖UnitAddTorus.mFourierCoeff u₁ k‖ ^ 2) ≤ (‖ω‖ / (2 * Real.pi)) ^ 2 := by
  have hpoint : ∀ k, (2 * Real.pi) ^ 2 * (frequencySq k *
      (‖UnitAddTorus.mFourierCoeff u₀ k‖ ^ 2 +
       ‖UnitAddTorus.mFourierCoeff u₁ k‖ ^ 2)) =
      ‖UnitAddTorus.mFourierCoeff ω k‖ ^ 2 := by
    intro k
    rw [fourier_div_curl_identity, hdiv k, norm_zero, zero_pow (by decide : 2 ≠ 0),
      zero_add, ← hcurl k, norm_mul, norm_mul, mul_pow, mul_pow]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos, mul_pow]
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < 2 * Real.pi))).mpr
  calc
    _ = ∑ k ∈ s, ‖UnitAddTorus.mFourierCoeff ω k‖ ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]; exact hpoint k
    _ ≤ ‖ω‖ ^ 2 := by
      simpa only [← UnitAddTorus.mFourierBasis_repr, HilbertBasis.repr_apply_apply] using
        UnitAddTorus.mFourierBasis.orthonormal.sum_inner_products_le ω (s := s)

/-- Each velocity component has the Fourier tail controlled by the
vorticity, with the correct normalization on the unit torus. -/
theorem fourier_velocity_tail_le (N : ℕ) (hN : 0 < N) (u₀ u₁ ω : FourierL2)
    (hdiv : ∀ k, (k 0 : ℂ) * UnitAddTorus.mFourierCoeff u₀ k +
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff u₁ k = 0)
    (hcurl : ∀ k, (2 * Real.pi : ℂ) * Complex.I *
      ((k 0 : ℂ) * UnitAddTorus.mFourierCoeff u₁ k -
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff u₀ k) = UnitAddTorus.mFourierCoeff ω k) :
    ‖u₀ - fourierTrunc N u₀‖ ≤ (‖ω‖ / (2 * Real.pi)) / N ∧
    ‖u₁ - fourierTrunc N u₁‖ ≤ (‖ω‖ / (2 * Real.pi)) / N := by
  have hbound := fourier_velocity_weighted_bound u₀ u₁ ω hdiv hcurl
  constructor
  · apply norm_sub_fourierTrunc_le N hN u₀ (by positivity)
    intro s
    apply le_trans _ (hbound s)
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (sq_nonneg _)) (frequencySq_nonneg k)
  · apply norm_sub_fourierTrunc_le N hN u₁ (by positivity)
    intro s
    apply le_trans _ (hbound s)
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (sq_nonneg _)) (frequencySq_nonneg k)

/-! ## Fourier test functions in the original fundamental-square model -/

/-- The phase `k · x` in the original torus of period `2π`. -/
def boxFourierPhase (k : Fin 2 → ℤ) : R2 →L[ℝ] ℝ :=
  ∑ i : Fin 2, (k i : ℝ) • PiLp.proj 2 (fun _ : Fin 2 => ℝ) i

theorem boxFourierPhase_apply (k : Fin 2 → ℤ) (x : R2) :
    boxFourierPhase k x = ∑ i : Fin 2, (k i : ℝ) * x i := by
  simp [boxFourierPhase, PiLp.proj_apply]

theorem boxFourierPhase_single (k : Fin 2 → ℤ) (i : Fin 2) (a : ℝ) :
    boxFourierPhase k (EuclideanSpace.single i a) = (k i : ℝ) * a := by
  simp [boxFourierPhase_apply, EuclideanSpace.single_apply, eq_comm]

/-- Both trigonometric modes are valid tests for the distributional equations. -/
theorem isScalarTest_boxFourier_cos (k : Fin 2 → ℤ) :
    IsScalarTest (fun x => Real.cos (boxFourierPhase k x)) := by
  constructor
  · exact Real.contDiff_cos.comp (boxFourierPhase k).contDiff
  · intro x i
    dsimp only
    rw [map_add, boxFourierPhase_single]
    exact Real.cos_add_int_mul_two_pi _ _

theorem isScalarTest_boxFourier_sin (k : Fin 2 → ℤ) :
    IsScalarTest (fun x => Real.sin (boxFourierPhase k x)) := by
  constructor
  · exact Real.contDiff_sin.comp (boxFourierPhase k).contDiff
  · intro x i
    dsimp only
    rw [map_add, boxFourierPhase_single]
    exact Real.sin_add_int_mul_two_pi _ _

theorem pd_boxFourier_cos (k : Fin 2 → ℤ) (i : Fin 2) (x : R2) :
    pd i (fun y => Real.cos (boxFourierPhase k y)) x =
      -(k i : ℝ) * Real.sin (boxFourierPhase k x) := by
  rw [pd, ((boxFourierPhase k).hasFDerivAt.cos).fderiv]
  simp [boxFourierPhase_single]
  ring

theorem pd_boxFourier_sin (k : Fin 2 → ℤ) (i : Fin 2) (x : R2) :
    pd i (fun y => Real.sin (boxFourierPhase k y)) x =
      (k i : ℝ) * Real.cos (boxFourierPhase k x) := by
  rw [pd, ((boxFourierPhase k).hasFDerivAt.sin).fderiv]
  simp [boxFourierPhase_single]
  ring

/-- The unnormalized Fourier coefficient on `[0,2π)²`.  The real and
imaginary parts are written as real integrals, matching `DivFree` and
`IsCurl` without any additional regularity of representatives. -/
def boxFourierCoeff (f : R2 → ℝ) (k : Fin 2 → ℤ) : ℂ :=
  ⟨∫ x in torusBox, f x * Real.cos (boxFourierPhase k x),
   -(∫ x in torusBox, f x * Real.sin (boxFourierPhase k x))⟩

private theorem integrable_coord_boxFourier_cos (u : L2T) (j : Fin 2) (k : Fin 2 → ℤ) :
    Integrable (fun x => u x j * Real.cos (boxFourierPhase k x)) μT := by
  have hc : Integrable (fun x => u x j) μT := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) j).integrable_comp
      ((Lp.memLp u).integrable (by norm_num))
  apply hc.mul_bdd
  · exact (Real.continuous_cos.comp (boxFourierPhase k).continuous).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by simpa using Real.abs_cos_le_one (boxFourierPhase k x)

private theorem integrable_coord_boxFourier_sin (u : L2T) (j : Fin 2) (k : Fin 2 → ℤ) :
    Integrable (fun x => u x j * Real.sin (boxFourierPhase k x)) μT := by
  have hc : Integrable (fun x => u x j) μT := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) j).integrable_comp
      ((Lp.memLp u).integrable (by norm_num))
  apply hc.mul_bdd
  · exact (Real.continuous_sin.comp (boxFourierPhase k).continuous).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by simpa using Real.abs_sin_le_one (boxFourierPhase k x)

private theorem integrable_coord_pd_boxFourier_cos
    (u : L2T) (i j : Fin 2) (k : Fin 2 → ℤ) :
    Integrable (fun x => u x j * pd i (fun y => Real.cos (boxFourierPhase k y)) x) μT := by
  convert (integrable_coord_boxFourier_sin u j k).const_mul (-(k i : ℝ)) using 1
  funext x
  rw [pd_boxFourier_cos]
  ring

private theorem integrable_coord_pd_boxFourier_sin
    (u : L2T) (i j : Fin 2) (k : Fin 2 → ℤ) :
    Integrable (fun x => u x j * pd i (fun y => Real.sin (boxFourierPhase k y)) x) μT := by
  convert (integrable_coord_boxFourier_cos u j k).const_mul (k i : ℝ) using 1
  funext x
  rw [pd_boxFourier_sin]
  ring

private theorem integral_coord_pd_boxFourier_cos
    (u : L2T) (i j : Fin 2) (k : Fin 2 → ℤ) :
    (∫ x in torusBox, u x j * pd i (fun y => Real.cos (boxFourierPhase k y)) x) =
      -(k i : ℝ) * ∫ x in torusBox, u x j * Real.sin (boxFourierPhase k x) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by dsimp only; rw [pd_boxFourier_cos]; ring

private theorem integral_coord_pd_boxFourier_sin
    (u : L2T) (i j : Fin 2) (k : Fin 2 → ℤ) :
    (∫ x in torusBox, u x j * pd i (fun y => Real.sin (boxFourierPhase k y)) x) =
      (k i : ℝ) * ∫ x in torusBox, u x j * Real.cos (boxFourierPhase k x) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by dsimp only; rw [pd_boxFourier_sin]; ring

/-- Distributional divergence-freeness in the original model gives the
exact algebraic Fourier divergence identity at every lattice frequency. -/
theorem boxFourier_div_identity (u : L2T) (hu : DivFree u) (k : Fin 2 → ℤ) :
    (k 0 : ℂ) * boxFourierCoeff (fun x => u x 0) k +
      (k 1 : ℂ) * boxFourierCoeff (fun x => u x 1) k = 0 := by
  have hcos := hu _ (isScalarTest_boxFourier_cos k)
  have hsin := hu _ (isScalarTest_boxFourier_sin k)
  simp only [Fin.sum_univ_two] at hcos hsin
  rw [integral_add (integrable_coord_pd_boxFourier_cos u 0 0 k)
    (integrable_coord_pd_boxFourier_cos u 1 1 k),
    integral_coord_pd_boxFourier_cos, integral_coord_pd_boxFourier_cos] at hcos
  rw [integral_add (integrable_coord_pd_boxFourier_sin u 0 0 k)
    (integrable_coord_pd_boxFourier_sin u 1 1 k),
    integral_coord_pd_boxFourier_sin, integral_coord_pd_boxFourier_sin] at hsin
  apply Complex.ext <;>
    simp only [boxFourierCoeff, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      sub_zero, add_zero, Complex.zero_re, Complex.zero_im]
  · exact hsin
  · linarith

/-- The distributional curl in the original model gives the exact Fourier
curl identity.  On the period-`2π` torus, spatial differentiation multiplies
the coefficient by `i k`, with no further normalization factor. -/
theorem boxFourier_curl_identity (u : L2T) (ω : R2 → ℝ)
    (hω : IsCurl u ω) (k : Fin 2 → ℤ) :
    Complex.I * ((k 0 : ℂ) * boxFourierCoeff (fun x => u x 1) k -
      (k 1 : ℂ) * boxFourierCoeff (fun x => u x 0) k) = boxFourierCoeff ω k := by
  have hcos := hω _ (isScalarTest_boxFourier_cos k)
  have hsin := hω _ (isScalarTest_boxFourier_sin k)
  rw [integral_sub (integrable_coord_pd_boxFourier_cos u 1 0 k)
    (integrable_coord_pd_boxFourier_cos u 0 1 k),
    integral_coord_pd_boxFourier_cos, integral_coord_pd_boxFourier_cos] at hcos
  rw [integral_sub (integrable_coord_pd_boxFourier_sin u 1 0 k)
    (integrable_coord_pd_boxFourier_sin u 0 1 k),
    integral_coord_pd_boxFourier_sin, integral_coord_pd_boxFourier_sin] at hsin
  apply Complex.ext <;>
    simp only [boxFourierCoeff, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, sub_zero, add_zero]
  · linarith
  · linarith

/-- A real sine or cosine Fourier vector mode, in one velocity coordinate. -/
def boxFourierModeFn (k : Fin 2 → ℤ) (j : Fin 2) (sine : Bool) (x : R2) : R2 :=
  EuclideanSpace.single j (if sine then Real.sin (boxFourierPhase k x)
    else Real.cos (boxFourierPhase k x))

theorem memLp_boxFourierModeFn (k : Fin 2 → ℤ) (j : Fin 2) (sine : Bool) :
    MemLp (boxFourierModeFn k j sine) 2 μT := by
  apply MemLp.of_bound (C := 1)
  · have hcont : Continuous (boxFourierModeFn k j sine) := by
      have hsingle : Continuous (EuclideanSpace.single j : ℝ → R2) := by
        unfold EuclideanSpace.single
        apply (PiLp.continuous_toLp 2 _).comp
        apply continuous_pi
        intro i
        by_cases hi : i = j <;> simp only [Pi.single_apply, hi, ↓reduceIte] <;> fun_prop
      cases sine
      · change Continuous (fun x : R2 => EuclideanSpace.single j (Real.cos (boxFourierPhase k x)))
        exact hsingle.comp (Real.continuous_cos.comp (boxFourierPhase k).continuous)
      · change Continuous (fun x : R2 => EuclideanSpace.single j (Real.sin (boxFourierPhase k x)))
        exact hsingle.comp (Real.continuous_sin.comp (boxFourierPhase k).continuous)
    exact hcont.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    rw [boxFourierModeFn, EuclideanSpace.norm_single]
    cases sine
    · simpa using Real.abs_cos_le_one (boxFourierPhase k x)
    · simpa using Real.abs_sin_le_one (boxFourierPhase k x)

/-- A real Fourier vector mode as an element of the original `L²(𝕋²;ℝ²)`. -/
def boxFourierMode (k : Fin 2 → ℤ) (j : Fin 2) (sine : Bool) : L2T :=
  (memLp_boxFourierModeFn k j sine).toLp (boxFourierModeFn k j sine)

def boxFourierGenerators (N : ℕ) : Finset L2T := by
  classical
  exact (((fourierModes N).product (Finset.univ : Finset (Fin 2))).product
    (Finset.univ : Finset Bool)).image fun p => boxFourierMode p.1.1 p.1.2 p.2

/-- The finite-dimensional real space of all vector trigonometric
polynomials with frequencies in `[-N,N]²`, on the original torus box. -/
def boxFourierSpace (N : ℕ) : Submodule ℝ L2T :=
  Submodule.span ℝ (boxFourierGenerators N : Set L2T)

instance (N : ℕ) : FiniteDimensional ℝ (boxFourierSpace N) :=
  FiniteDimensional.span_finset ℝ _

theorem boxFourierMode_mem (N : ℕ) {k : Fin 2 → ℤ} (hk : k ∈ fourierModes N)
    (j : Fin 2) (sine : Bool) : boxFourierMode k j sine ∈ boxFourierSpace N := by
  classical
  apply Submodule.subset_span
  exact Finset.mem_image.mpr ⟨((k, j), sine), by simp [hk], rfl⟩

/-- The genuine finite-rank orthogonal Fourier projection on the original
non-normalized `L2T`. -/
def boxFourierTrunc (N : ℕ) : L2T →L[ℝ] L2T :=
  (boxFourierSpace N).starProjection

theorem boxFourierTrunc_range (N : ℕ) :
    LinearMap.range (boxFourierTrunc N).toLinearMap = boxFourierSpace N :=
  Submodule.range_starProjection _

theorem boxFourierTrunc_finiteDimensional_range (N : ℕ) :
    FiniteDimensional ℝ (LinearMap.range (boxFourierTrunc N).toLinearMap) := by
  rw [boxFourierTrunc_range]
  infer_instance

theorem norm_boxFourierTrunc_le (N : ℕ) (u : L2T) : ‖boxFourierTrunc N u‖ ≤ ‖u‖ :=
  Submodule.norm_starProjection_apply_le _ _

theorem boxFourierTrunc_eq_self (N : ℕ) {u : L2T} (hu : u ∈ boxFourierSpace N) :
    boxFourierTrunc N u = u := Submodule.starProjection_eq_self_iff.mpr hu

/-- Any trigonometric polynomial approximation bounds the error of the
orthogonal Fourier truncation on the original torus. -/
theorem norm_sub_boxFourierTrunc_le (N : ℕ) (u v : L2T)
    (hv : v ∈ boxFourierSpace N) : ‖u - boxFourierTrunc N u‖ ≤ ‖u - v‖ := by
  rw [boxFourierTrunc, Submodule.starProjection_minimal]
  exact ciInf_le (show BddBelow (Set.range fun x : boxFourierSpace N => ‖u - x‖) from
    ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩) ⟨v, hv⟩

end Euler2D

end
