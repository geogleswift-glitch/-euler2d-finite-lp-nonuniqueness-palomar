module

public import RequestProject.Euler.BiotSavartL2

/-!
# Actual first weak derivatives of the torus inverse curl

The four derivatives are explicitly constructed by bounded Fourier
symbols.  Their distributional identities follow from classical periodic
integration by parts on the genuine finite Fourier polynomials and
strong convergence in the physical `L²` spaces.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

namespace BiotSavartConstruction

lemma coordinate_square_le_frequencySq (k : Fin 2 → ℤ) (i : Fin 2) :
    (k i : ℝ) ^ 2 ≤ frequencySq k := by
  fin_cases i
  · exact le_add_of_nonneg_right (sq_nonneg (k 1 : ℝ))
  · exact le_add_of_nonneg_left (sq_nonneg (k 0 : ℝ))

lemma abs_frequency_mul_le (k : Fin 2 → ℤ) (i j : Fin 2) :
    |(k i : ℝ)| * |(k j : ℝ)| ≤ frequencySq k := by
  have hi := coordinate_square_le_frequencySq k i
  have hj := coordinate_square_le_frequencySq k j
  nlinarith [sq_nonneg (|(k i : ℝ)| - |(k j : ℝ)|),
    sq_abs (k i : ℝ), sq_abs (k j : ℝ)]

/-- The symbol of the physical derivative `∂ᵢ` of inverse-curl coordinate `j`. -/
def derivativeSymbol (i j : Fin 2) (k : Fin 2 → ℤ) : ℂ :=
  Complex.I * (k i : ℂ) * symbol j k

lemma derivativeSymbol_norm_le (i j : Fin 2) (k : Fin 2 → ℤ) :
    ‖derivativeSymbol i j k‖ ≤ 1 := by
  by_cases hz : frequencySq k = 0
  · simp [derivativeSymbol, symbol, hz]
  have hp : 0 < frequencySq k := lt_of_le_of_ne (frequencySq_nonneg k) (Ne.symm hz)
  fin_cases j
  · change ‖Complex.I * (k i : ℂ) *
      (Complex.I * (k 1 : ℂ) / (frequencySq k : ℂ))‖ ≤ 1
    simpa only [norm_mul, norm_div, Complex.norm_I, one_mul, Complex.norm_intCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (frequencySq_nonneg k),
      mul_div_assoc] using (div_le_one hp).mpr (abs_frequency_mul_le k i 1)
  · change ‖Complex.I * (k i : ℂ) *
      (Complex.I * -(k 0 : ℂ) / (frequencySq k : ℂ))‖ ≤ 1
    simpa only [norm_mul, norm_div, Complex.norm_I, one_mul, norm_neg, Complex.norm_intCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (frequencySq_nonneg k),
      mul_div_assoc] using (div_le_one hp).mpr (abs_frequency_mul_le k i 0)

def derivativeComponent (i j : Fin 2) : BoxFourierL2 →L[ℂ] BoxFourierL2 :=
  boxMultiplier (derivativeSymbol i j) (derivativeSymbol_norm_le i j)

lemma normalized_derivativeComponent_coeff (i j : Fin 2) (f : BoxFourierL2)
    (k : Fin 2 → ℤ) :
    boxNormalizedFourierCoeff (derivativeComponent i j f) k =
      Complex.I * (k i : ℂ) * boxNormalizedFourierCoeff (component j f) k := by
  unfold boxNormalizedFourierCoeff derivativeComponent
  rw [boxMultiplier_coeff, component_coeff]
  unfold derivativeSymbol
  ring

lemma pairedPolynomial_derivative (N : ℕ) (f : BoxFourierL2) (x : R2) (i j : Fin 2) :
    pd i (pairedPolynomial N (fun j => component j f)) x j =
      boxScalarFourierPolynomial N (derivativeComponent i j f) x := by
  rw [pd_pairedPolynomial]
  unfold boxScalarFourierPolynomial
  congr 1
  funext k
  exact (normalized_derivativeComponent_coeff i j f k).symm

lemma norm_boxRealPart_le (v : BoxFourierL2) : ‖boxRealPart v‖ ≤ ‖v‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_boxRealPart v] with x hx
  rw [hx, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

end BiotSavartConstruction

open BiotSavartConstruction

/-- Four actual scalar `L²` fields, constructed as continuous linear
functions of the input vorticity. -/
def biotSavartDerivativeL2 (i j : Fin 2) : Lp ℝ 2 μT →L[ℝ] Lp ℝ 2 μT :=
  boxRealPart.comp (((derivativeComponent i j).restrictScalars ℝ).comp complexify)

lemma norm_biotSavartDerivativeL2_le (i j : Fin 2) (f : Lp ℝ 2 μT) :
    ‖biotSavartDerivativeL2 i j f‖ ≤ ‖f‖ := by
  change ‖boxRealPart (derivativeComponent i j (complexify f))‖ ≤ _
  exact (norm_boxRealPart_le _).trans
    ((boxMultiplier_norm_le _ _ _).trans (complexify_norm_le f))

namespace BiotSavartConstruction

def derivativeApprox (N : ℕ) (i j : Fin 2) (f : Lp ℝ 2 μT) : Lp ℝ 2 μT :=
  boxRealPart (boxScalarFourierTrunc N (derivativeComponent i j (complexify f)))

lemma tendsto_derivativeApprox (i j : Fin 2) (f : Lp ℝ 2 μT) :
    Tendsto (fun N => derivativeApprox N i j f) atTop (𝓝 (biotSavartDerivativeL2 i j f)) :=
  (boxRealPart.continuous.tendsto _).comp (tendsto_boxScalarFourierTrunc _)

lemma derivativeApprox_ae (N : ℕ) (i j : Fin 2) (f : Lp ℝ 2 μT) :
    derivativeApprox N i j f =ᵐ[μT] fun x =>
      pd i (pairedPolynomial N (fun j => component j (complexify f))) x j := by
  refine ((coeFn_boxRealPart _).trans (coeFn_boxScalarFourierTrunc_re N _)).trans ?_
  exact Eventually.of_forall fun x => (pairedPolynomial_derivative N (complexify f) x i j).symm

lemma pairedTrunc_weakDerivative (N : ℕ) (i j : Fin 2) (f : Lp ℝ 2 μT)
    (ψ : R2 → ℝ) (hψ : IsScalarTest ψ) :
    (∫ x in torusBox, pairedTrunc N (fun j => component j (complexify f)) x j * pd i ψ x) =
      -∫ x in torusBox, derivativeApprox N i j f x * ψ x := by
  let P := pairedPolynomial N (fun j => component j (complexify f))
  have hs := pairedPolynomial_smooth_periodic N (fun j => component j (complexify f))
  have hP : ContDiff ℝ 1 P := hs.1.of_le (by exact_mod_cast le_top)
  have hPc : ContDiff ℝ 1 (fun x => P x j) :=
    (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).contDiff.comp hP
  have hp : IsTorusPeriodic (fun x => P x j) := fun x ℓ =>
    congrArg (fun y : R2 => y j) (hs.2 x ℓ)
  calc
    _ = ∫ x in torusBox, P x j * pd i ψ x := by
      apply integral_congr_ae
      filter_upwards [pairedTrunc_ae N (fun j => component j (complexify f))] with x hx
      rw [hx]
    _ = -∫ x in torusBox, pd i (fun y => P y j) x * ψ x :=
      integral_mul_pd_periodic _ _ hPc (hψ.1.of_le (by exact_mod_cast le_top)) hp hψ.2 i
    _ = -∫ x in torusBox, derivativeApprox N i j f x * ψ x := by
      congr 1
      apply integral_congr_ae
      filter_upwards [derivativeApprox_ae N i j f] with x hx
      rw [torus_pd_component P x (hP.differentiable one_ne_zero x) i j]
      rw [hx]

end BiotSavartConstruction

/-- The explicitly constructed four scalar fields are the actual weak
partial derivatives required by the project's Sobolev definition. -/
theorem biotSavartL2_weakDerivative (f : Lp ℝ 2 μT) (i j : Fin 2)
    (ψ : R2 → ℝ) (hψ : IsScalarTest ψ) :
    (∫ x in torusBox, biotSavartL2 f x j * pd i ψ x) =
      -∫ x in torusBox, biotSavartDerivativeL2 i j f x * ψ x := by
  have hv : Tendsto (fun N => pairedTrunc N (fun j => component j (complexify f)))
      atTop (𝓝 (biotSavartL2 f)) := tendsto_pairedTrunc _
  have hpd : Continuous (pd i ψ) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hl := tendsto_integral_lin hv hpd j
  have hr : Tendsto (fun N => -∫ x in torusBox, derivativeApprox N i j f x * ψ x)
      atTop (𝓝 (-∫ x in torusBox, biotSavartDerivativeL2 i j f x * ψ x)) := by
    simp_rw [scalar_test_pairing_eq_inner _ hψ.1.continuous]
    exact ((tendsto_derivativeApprox i j f).inner tendsto_const_nhds).neg
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall fun N =>
    (pairedTrunc_weakDerivative N i j f ψ hψ).symm))

/-- The actual torus Biot--Savart operator maps scalar `L²` into the
project's concrete distributional `W¹,²` space. -/
theorem memW1p_two_biotSavartL2 (f : Lp ℝ 2 μT) :
    MemW1p 2 (biotSavartL2 f) := by
  refine ⟨Lp.memLp _, (fun i j x => biotSavartDerivativeL2 i j f x), ?_, ?_⟩
  · intro i j
    exact Lp.memLp _
  · intro i j ψ hψ
    exact biotSavartL2_weakDerivative f i j ψ hψ

end Euler2D

end
