module

public import RequestProject.Euler.BoxFourierCompactness
public import RequestProject.Euler.Stationary

/-!
# Smooth representatives of the actual square Fourier truncations

The real trigonometric polynomial below represents the finite Fourier
operator transported from the normalized quotient.  Its coefficients
carry the physical square normalization, and distributional div--curl
identities become classical identities of the smooth representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

/-- The real part of a complex coefficient times a physical character. -/
def realFourierMode (a : ℂ) (k : Fin 2 → ℤ) (x : R2) : ℝ :=
  a.re * cos (boxFourierPhase k x) - a.im * sin (boxFourierPhase k x)

lemma realFourierMode_add (a b : ℂ) (k : Fin 2 → ℤ) (x : R2) :
    realFourierMode (a + b) k x = realFourierMode a k x + realFourierMode b k x := by
  simp only [realFourierMode, Complex.add_re, Complex.add_im]
  ring

lemma realFourierMode_sub (a b : ℂ) (k : Fin 2 → ℤ) (x : R2) :
    realFourierMode (a - b) k x = realFourierMode a k x - realFourierMode b k x := by
  simp only [realFourierMode, Complex.sub_re, Complex.sub_im]
  ring

@[simp] lemma realFourierMode_zero (k : Fin 2 → ℤ) (x : R2) :
    realFourierMode 0 k x = 0 := by simp [realFourierMode]

lemma isScalarTest_realFourierMode (a : ℂ) (k : Fin 2 → ℤ) :
    IsScalarTest (realFourierMode a k) := by
  have hc := isScalarTest_boxFourier_cos k
  have hs := isScalarTest_boxFourier_sin k
  refine ⟨(contDiff_const.mul hc.1).sub (contDiff_const.mul hs.1), ?_⟩
  intro x i
  simp only [realFourierMode, hc.2 x i, hs.2 x i]

lemma pd_realFourierMode (a : ℂ) (k : Fin 2 → ℤ) (i : Fin 2) (x : R2) :
    pd i (realFourierMode a k) x =
      realFourierMode (Complex.I * (k i : ℂ) * a) k x := by
  unfold pd realFourierMode
  have hd := (((boxFourierPhase k).hasFDerivAt (x := x)).cos.const_mul a.re).sub
    (((boxFourierPhase k).hasFDerivAt (x := x)).sin.const_mul a.im)
  change HasFDerivAt (fun y => a.re * cos (boxFourierPhase k y) -
    a.im * sin (boxFourierPhase k y)) _ x at hd
  rw [hd.fderiv]
  simp [boxFourierPhase_single, Complex.mul_re, Complex.mul_im]
  ring

/-- A finite real Fourier polynomial with arbitrary complex coefficients. -/
def realFourierPolynomial (N : ℕ) (a : (Fin 2 → ℤ) → ℂ) (x : R2) : ℝ :=
  ∑ k ∈ fourierModes N, realFourierMode (a k) k x

lemma isScalarTest_realFourierPolynomial (N : ℕ) (a : (Fin 2 → ℤ) → ℂ) :
    IsScalarTest (realFourierPolynomial N a) := by
  refine ⟨ContDiff.sum fun k _ => (isScalarTest_realFourierMode (a k) k).1, ?_⟩
  intro x i
  exact Finset.sum_congr rfl fun k _ => (isScalarTest_realFourierMode (a k) k).2 x i

lemma pd_realFourierPolynomial (N : ℕ) (a : (Fin 2 → ℤ) → ℂ)
    (i : Fin 2) (x : R2) :
    pd i (realFourierPolynomial N a) x =
      realFourierPolynomial N (fun k => Complex.I * (k i : ℂ) * a k) x := by
  unfold pd realFourierPolynomial
  rw [fderiv_fun_sum fun k _ =>
    ((isScalarTest_realFourierMode (a k) k).1.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun k _ => pd_realFourierMode (a k) k i x

/-- Normalized coefficients of an actual box scalar field. -/
def boxNormalizedFourierCoeff (v : BoxFourierL2) (k : Fin 2 → ℤ) : ℂ :=
  (2 * π : ℂ)⁻¹ * UnitAddTorus.mFourierCoeff (torusL2Equiv v) k

/-- A smooth real representative of the real part of the box scalar truncation. -/
def boxScalarFourierPolynomial (N : ℕ) (v : BoxFourierL2) : R2 → ℝ :=
  realFourierPolynomial N (boxNormalizedFourierCoeff v)

lemma boxNormalizedFourierCoeff_real {f : R2 → ℝ} {v : BoxFourierL2}
    (hv : v =ᵐ[μT] fun x => (f x : ℂ)) (hf : Integrable f μT) (k : Fin 2 → ℤ) :
    boxNormalizedFourierCoeff v k = ((2 * π : ℂ) ^ 2)⁻¹ * boxFourierCoeff f k := by
  rw [boxNormalizedFourierCoeff, mFourierCoeff_torusL2Equiv_real hv hf]
  ring

lemma isScalarTest_boxScalarFourierPolynomial (N : ℕ) (v : BoxFourierL2) :
    IsScalarTest (boxScalarFourierPolynomial N v) :=
  isScalarTest_realFourierPolynomial N _

lemma torusL2Equiv_symm_eq_descend (g : FourierL2) :
    torusL2Equiv.symm g = torusDescendFn g := by
  apply torusL2Equiv.injective
  rw [torusL2Equiv.apply_symm_apply]
  symm
  apply Lp.ext
  filter_upwards [coeFn_torusLiftFn (torusDescendFn g),
    ae_eq_comp_torusRep (coeFn_torusDescendFn g)] with t hlift hdesc
  change torusLiftFn (torusDescendFn g) t = g t
  simp only [Function.comp_def] at hdesc
  rw [hlift, hdesc, torusProj_torusRep, ← mul_assoc, mul_inv_cancel₀, one_mul]
  exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)

lemma coeFn_fourier_sum (s : Finset (Fin 2 → ℤ)) (a : (Fin 2 → ℤ) → ℂ) :
    (∑ k ∈ s, a k • UnitAddTorus.mFourierLp 2 k : FourierL2) =ᵐ[volume]
      fun t => ∑ k ∈ s, a k * UnitAddTorus.mFourier k t := by
  induction s using Finset.induction_on with
  | empty => simpa [Pi.zero_def] using Lp.coeFn_zero ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    filter_upwards [Lp.coeFn_add (a k • UnitAddTorus.mFourierLp 2 k)
      (∑ j ∈ s, a j • UnitAddTorus.mFourierLp 2 j),
      Lp.coeFn_smul (a k) (UnitAddTorus.mFourierLp 2 k),
      UnitAddTorus.coeFn_mFourierLp 2 k, ih] with t hadd hsmul hmode hsum
    rw [hadd]
    change (a k • UnitAddTorus.mFourierLp 2 k) t + _ = _
    rw [hsmul]
    change a k * UnitAddTorus.mFourierLp 2 k t + _ = _
    rw [hmode, hsum]

lemma coeFn_boxScalarFourierTrunc_re (N : ℕ) (v : BoxFourierL2) :
    (fun x => (boxScalarFourierTrunc N v x).re) =ᵐ[μT]
      boxScalarFourierPolynomial N v := by
  have hs : fourierTrunc N (torusL2Equiv v) =ᵐ[volume] fun t =>
      ∑ k ∈ fourierModes N, UnitAddTorus.mFourierCoeff (torusL2Equiv v) k *
        UnitAddTorus.mFourier k t := by
    rw [fourierTrunc_apply]
    exact coeFn_fourier_sum _ _
  have hp := measurePreserving_torusProj.quasiMeasurePreserving.ae_eq_comp
    (Measure.ae_smul_measure hs (ENNReal.ofReal ((2 * π) ^ 2)))
  change (fun x => ((torusL2Equiv.symm (fourierTrunc N (torusL2Equiv v))) x).re) =ᵐ[μT] _
  rw [torusL2Equiv_symm_eq_descend]
  filter_upwards [coeFn_torusDescendFn (fourierTrunc N (torusL2Equiv v)), hp]
    with x hdesc hpoly
  simp only [Function.comp_def] at hpoly
  rw [hdesc, hpoly, Finset.mul_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [← mul_assoc]
    simp only [realFourierMode, boxNormalizedFourierCoeff, Complex.mul_re,
      mFourier_torusProj_re, mFourier_torusProj_im]

/-- The actual velocity Fourier truncation has this explicit smooth representative. -/
def boxVectorFourierPolynomial (N : ℕ) (u : L2T) (x : R2) : R2 :=
  boxScalarFourierPolynomial N (boxComplexCoord 0 u) x • EuclideanSpace.single 0 1 +
    boxScalarFourierPolynomial N (boxComplexCoord 1 u) x • EuclideanSpace.single 1 1

lemma boxVectorFourierPolynomial_apply (N : ℕ) (u : L2T) (x : R2) (j : Fin 2) :
    boxVectorFourierPolynomial N u x j =
      boxScalarFourierPolynomial N (boxComplexCoord j u) x := by
  fin_cases j <;> simp [boxVectorFourierPolynomial, EuclideanSpace.single_apply]

lemma smooth_periodic_boxVectorFourierPolynomial (N : ℕ) (u : L2T) :
    ContDiff ℝ ∞ (boxVectorFourierPolynomial N u) ∧
      IsTorusPeriodic (boxVectorFourierPolynomial N u) := by
  have h₀ := isScalarTest_boxScalarFourierPolynomial N (boxComplexCoord 0 u)
  have h₁ := isScalarTest_boxScalarFourierPolynomial N (boxComplexCoord 1 u)
  refine ⟨(h₀.1.smul contDiff_const).add (h₁.1.smul contDiff_const), ?_⟩
  intro x i
  simp only [boxVectorFourierPolynomial, h₀.2 x i, h₁.2 x i]

lemma coeFn_boxVectorFourierTrunc (N : ℕ) (u : L2T) :
    boxVectorFourierTrunc N u =ᵐ[μT] boxVectorFourierPolynomial N u := by
  filter_upwards [Lp.coeFn_add (boxVectorFourierTerm N 0 u) (boxVectorFourierTerm N 1 u),
    coeFn_boxRealCoordInjection 0 (boxScalarFourierTrunc N (boxComplexCoord 0 u)),
    coeFn_boxRealCoordInjection 1 (boxScalarFourierTrunc N (boxComplexCoord 1 u)),
    coeFn_boxScalarFourierTrunc_re N (boxComplexCoord 0 u),
    coeFn_boxScalarFourierTrunc_re N (boxComplexCoord 1 u)] with x hadd h₀ h₁ hp₀ hp₁
  change (boxVectorFourierTerm N 0 u + boxVectorFourierTerm N 1 u) x = _
  rw [hadd]
  change boxRealCoordInjection 0 (boxScalarFourierTrunc N (boxComplexCoord 0 u)) x +
    boxRealCoordInjection 1 (boxScalarFourierTrunc N (boxComplexCoord 1 u)) x = _
  rw [h₀, h₁, hp₀, hp₁]
  rfl

lemma pd_boxVectorFourierPolynomial (N : ℕ) (u : L2T) (x : R2) (i j : Fin 2) :
    pd i (boxVectorFourierPolynomial N u) x j = realFourierPolynomial N
      (fun k => Complex.I * (k i : ℂ) * boxNormalizedFourierCoeff (boxComplexCoord j u) k) x := by
  rw [← torus_pd_component _ x
    ((smooth_periodic_boxVectorFourierPolynomial N u).1.differentiable (by simp) x) i j]
  have he : (fun y => boxVectorFourierPolynomial N u y j) =
      boxScalarFourierPolynomial N (boxComplexCoord j u) :=
    funext fun y => boxVectorFourierPolynomial_apply N u y j
  rw [he]
  exact pd_realFourierPolynomial N _ i x

lemma boxNormalizedFourierCoeff_div (u : L2T) (hu : DivFree u) (k : Fin 2 → ℤ) :
    Complex.I * (k 0 : ℂ) * boxNormalizedFourierCoeff (boxComplexCoord 0 u) k +
      Complex.I * (k 1 : ℂ) * boxNormalizedFourierCoeff (boxComplexCoord 1 u) k = 0 := by
  unfold boxNormalizedFourierCoeff
  calc
    _ = (2 * π : ℂ)⁻¹ * Complex.I *
        ((k 0 : ℂ) * UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 0 u)) k +
         (k 1 : ℂ) * UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 1 u)) k) := by ring
    _ = 0 := by rw [lifted_div_identity u hu k, mul_zero]

/-- Distributional divergence-freeness gives classical divergence-freeness
of each actual smooth velocity approximation. -/
lemma divFree_boxVectorFourierPolynomial (N : ℕ) (u : L2T) (hu : DivFree u) (x : R2) :
    pd 0 (boxVectorFourierPolynomial N u) x 0 +
      pd 1 (boxVectorFourierPolynomial N u) x 1 = 0 := by
  rw [pd_boxVectorFourierPolynomial, pd_boxVectorFourierPolynomial]
  unfold realFourierPolynomial
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k hk
  rw [← realFourierMode_add, boxNormalizedFourierCoeff_div u hu k, realFourierMode_zero]

lemma boxNormalizedFourierCoeff_curl (u : L2T) (w : R2 → ℝ)
    (hw : MemLp w 2 μT) (hc : IsCurl u w) (k : Fin 2 → ℤ) :
    Complex.I * (k 0 : ℂ) * boxNormalizedFourierCoeff (boxComplexCoord 1 u) k -
      Complex.I * (k 1 : ℂ) * boxNormalizedFourierCoeff (boxComplexCoord 0 u) k =
        boxNormalizedFourierCoeff (boxVorticity w hw) k := by
  unfold boxNormalizedFourierCoeff
  calc
    _ = (2 * π : ℂ)⁻¹ * (Complex.I *
        ((k 0 : ℂ) * UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 1 u)) k -
         (k 1 : ℂ) * UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 0 u)) k)) := by ring
    _ = _ := by rw [lifted_curl_identity u w hw hc k]

/-- The classical curl of the explicit velocity polynomial is the real
scalar Fourier approximation of the original distributional curl. -/
lemma curl_boxVectorFourierPolynomial (N : ℕ) (u : L2T) (w : R2 → ℝ)
    (hw : MemLp w 2 μT) (hc : IsCurl u w) (x : R2) :
    pd 0 (boxVectorFourierPolynomial N u) x 1 -
      pd 1 (boxVectorFourierPolynomial N u) x 0 =
        boxScalarFourierPolynomial N (boxVorticity w hw) x := by
  rw [pd_boxVectorFourierPolynomial, pd_boxVectorFourierPolynomial]
  unfold boxScalarFourierPolynomial realFourierPolynomial
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← realFourierMode_sub, boxNormalizedFourierCoeff_curl u w hw hc k]

/-! ## Strong convergence, including the actual classical curls -/

lemma tendsto_fourierModes_atTop : Tendsto fourierModes atTop atTop := by
  let bound (k : Fin 2 → ℤ) := max (k 0).natAbs (k 1).natAbs
  apply tendsto_atTop.mpr
  intro s
  refine eventually_atTop.mpr ⟨s.sup bound, fun N hN => ?_⟩
  intro k hk
  rw [mem_fourierModes]
  intro i
  have hb : bound k ≤ N := (Finset.le_sup (f := bound) hk).trans hN
  have hi : (k i).natAbs ≤ N := by
    fin_cases i
    · exact (le_max_left _ _).trans hb
    · exact (le_max_right _ _).trans hb
  have habs : |k i| ≤ (N : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hi
  exact ⟨(neg_le_neg habs).trans (neg_abs_le _), (le_abs_self _).trans habs⟩

lemma tendsto_fourierTrunc (f : FourierL2) :
    Tendsto (fun N => fourierTrunc N f) atTop (𝓝 f) := by
  have hsum : Tendsto (fun s : Finset (Fin 2 → ℤ) =>
      ∑ k ∈ s, UnitAddTorus.mFourierCoeff f k • UnitAddTorus.mFourierLp 2 k)
      atTop (𝓝 f) := UnitAddTorus.hasSum_mFourier_series_L2 f
  simpa only [Function.comp_def, ← fourierTrunc_apply] using
    hsum.comp tendsto_fourierModes_atTop

lemma tendsto_boxScalarFourierTrunc (v : BoxFourierL2) :
    Tendsto (fun N => boxScalarFourierTrunc N v) atTop (𝓝 v) := by
  have h := (torusL2Equiv.symm.continuous.tendsto (torusL2Equiv v)).comp
    (tendsto_fourierTrunc (torusL2Equiv v))
  simpa only [Function.comp_def, boxScalarFourierTrunc, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    torusL2Equiv.symm_apply_apply] using h

/-- Real-part projection on actual scalar `L²` spaces. -/
def boxRealPart : BoxFourierL2 →L[ℝ] Lp ℝ 2 μT :=
  Complex.reCLM.compLpL 2 μT

lemma coeFn_boxRealPart (v : BoxFourierL2) :
    boxRealPart v =ᵐ[μT] fun x => (v x).re :=
  Complex.reCLM.coeFn_compLpL v

lemma boxRealPart_boxVorticity (w : R2 → ℝ) (hw : MemLp w 2 μT) :
    boxRealPart (boxVorticity w hw) = hw.toLp w := by
  apply Lp.ext
  filter_upwards [coeFn_boxRealPart (boxVorticity w hw),
    coeFn_boxVorticity w hw, hw.coeFn_toLp] with x hre hwv hwx
  rw [hre, hwv, hwx, Complex.ofReal_re]

lemma tendsto_boxRealPart_scalarTrunc (w : R2 → ℝ) (hw : MemLp w 2 μT) :
    Tendsto (fun N => boxRealPart (boxScalarFourierTrunc N (boxVorticity w hw)))
      atTop (𝓝 (hw.toLp w)) := by
  simpa only [Function.comp_def, boxRealPart_boxVorticity] using
    (boxRealPart.continuous.tendsto (boxVorticity w hw)).comp
      (tendsto_boxScalarFourierTrunc (boxVorticity w hw))

lemma memLp_boxScalarFourierPolynomial (N : ℕ) (v : BoxFourierL2) :
    MemLp (boxScalarFourierPolynomial N v) 2 μT := by
  have hrep : boxRealPart (boxScalarFourierTrunc N v) =ᵐ[μT]
      boxScalarFourierPolynomial N v :=
    (coeFn_boxRealPart _).trans (coeFn_boxScalarFourierTrunc_re N v)
  exact (memLp_congr_ae hrep).mp (Lp.memLp _)

lemma boxScalarFourierPolynomial_toLp (N : ℕ) (v : BoxFourierL2) :
    (memLp_boxScalarFourierPolynomial N v).toLp (boxScalarFourierPolynomial N v) =
      boxRealPart (boxScalarFourierTrunc N v) := by
  apply Lp.ext
  exact (memLp_boxScalarFourierPolynomial N v).coeFn_toLp.trans
    ((coeFn_boxRealPart _).trans (coeFn_boxScalarFourierTrunc_re N v)).symm

lemma memLp_boxVectorFourierPolynomial (N : ℕ) (u : L2T) :
    MemLp (boxVectorFourierPolynomial N u) 2 μT :=
  (memLp_congr_ae (coeFn_boxVectorFourierTrunc N u)).mp
    (Lp.memLp (boxVectorFourierTrunc N u))

lemma boxVectorFourierPolynomial_toLp (N : ℕ) (u : L2T) :
    (memLp_boxVectorFourierPolynomial N u).toLp (boxVectorFourierPolynomial N u) =
      boxVectorFourierTrunc N u := by
  apply Lp.ext
  exact (memLp_boxVectorFourierPolynomial N u).coeFn_toLp.trans
    (coeFn_boxVectorFourierTrunc N u).symm

lemma tendsto_boxVectorFourierTrunc (u : L2T) :
    Tendsto (fun N => boxVectorFourierTrunc N u) atTop (𝓝 u) := by
  have h₀ := (boxRealCoordInjection 0).continuous.tendsto (boxComplexCoord 0 u) |>.comp
    (tendsto_boxScalarFourierTrunc (boxComplexCoord 0 u))
  have h₁ := (boxRealCoordInjection 1).continuous.tendsto (boxComplexCoord 1 u) |>.comp
    (tendsto_boxScalarFourierTrunc (boxComplexCoord 1 u))
  simpa only [Function.comp_def, boxVectorFourierTrunc, boxVectorFourierTerm, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    boxRealCoordInjection_coords] using h₀.add h₁

/-- The explicit smooth velocity representatives converge in the actual `L²` norm. -/
lemma tendsto_boxVectorFourierPolynomial_toLp (u : L2T) :
    Tendsto (fun N => (memLp_boxVectorFourierPolynomial N u).toLp
      (boxVectorFourierPolynomial N u)) atTop (𝓝 u) := by
  simpa only [boxVectorFourierPolynomial_toLp] using tendsto_boxVectorFourierTrunc u

lemma memLp_curl_boxVectorFourierPolynomial (N : ℕ) (u : L2T) (w : R2 → ℝ)
    (hw : MemLp w 2 μT) (hc : IsCurl u w) :
    MemLp (fun x => pd 0 (boxVectorFourierPolynomial N u) x 1 -
      pd 1 (boxVectorFourierPolynomial N u) x 0) 2 μT := by
  simpa only [curl_boxVectorFourierPolynomial N u w hw hc] using
    memLp_boxScalarFourierPolynomial N (boxVorticity w hw)

/-- The classical curls of the same smooth velocity approximations converge
strongly to the actual distributional `L²` curl. -/
lemma tendsto_curl_boxVectorFourierPolynomial_toLp (u : L2T) (w : R2 → ℝ)
    (hw : MemLp w 2 μT) (hc : IsCurl u w) :
    Tendsto (fun N => (memLp_curl_boxVectorFourierPolynomial N u w hw hc).toLp
      (fun x => pd 0 (boxVectorFourierPolynomial N u) x 1 -
        pd 1 (boxVectorFourierPolynomial N u) x 0)) atTop (𝓝 (hw.toLp w)) := by
  have heq (N : ℕ) : (memLp_curl_boxVectorFourierPolynomial N u w hw hc).toLp
      (fun x => pd 0 (boxVectorFourierPolynomial N u) x 1 -
        pd 1 (boxVectorFourierPolynomial N u) x 0) =
      boxRealPart (boxScalarFourierTrunc N (boxVorticity w hw)) := by
    apply Lp.ext
    refine (memLp_curl_boxVectorFourierPolynomial N u w hw hc).coeFn_toLp.trans ?_
    have hcurl : (fun x => pd 0 (boxVectorFourierPolynomial N u) x 1 -
        pd 1 (boxVectorFourierPolynomial N u) x 0) =ᵐ[μT]
        boxScalarFourierPolynomial N (boxVorticity w hw) :=
      Filter.Eventually.of_forall (curl_boxVectorFourierPolynomial N u w hw hc)
    refine hcurl.trans ?_
    exact ((coeFn_boxRealPart _).trans
      (coeFn_boxScalarFourierTrunc_re N (boxVorticity w hw))).symm
  simpa only [heq] using tendsto_boxRealPart_scalarTrunc w hw

end Euler2D

end
