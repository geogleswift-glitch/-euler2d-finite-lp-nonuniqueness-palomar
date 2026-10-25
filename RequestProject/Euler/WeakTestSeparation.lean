module

public import RequestProject.Euler.WeakTimeEvolution
public import RequestProject.Euler.BoxFourierCompactness
public import RequestProject.Euler.Stationary
public import RequestProject.Euler.LimitPassage

/-!
# Smooth solenoidal tests separate actual divergence-free velocities

The proof uses the real sine and cosine tests in the original box and
the complete Fourier basis on the isometric quotient model.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

def SmoothDivFreeTest := {ψ : R2 → R2 // ContDiff ℝ ∞ ψ ∧ IsTorusPeriodic ψ ∧
  ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0}

def weakTestMap (u : L2T) (ψ : SmoothDivFreeTest) : ℝ := eulerSpatialPairing ψ.1 u

lemma continuous_weakTestMap : Continuous weakTestMap :=
  continuous_pi fun ψ => continuous_eulerSpatialPairing ψ.2.1.continuous

lemma isClosed_setOf_divFree : IsClosed {u : L2T | DivFree u} :=
  IsSeqClosed.isClosed fun _ _ hmem hlim =>
    divFree_of_tendsto hlim (Eventually.of_forall hmem)

def solenoidalFourierTest (k : Fin 2 → ℤ) (sine : Bool) (x : R2) : R2 :=
  (if sine then Real.sin (boxFourierPhase k x) else Real.cos (boxFourierPhase k x)) •
    torusVec (-(k 1 : ℝ)) (k 0 : ℝ)

lemma pd_smul_const_vector {f : R2 → ℝ} (hf : Differentiable ℝ f)
    (a : R2) (i : Fin 2) (x : R2) :
    pd i (fun y => f y • a) x = pd i f x • a := by
  unfold pd
  rw [((hf x).hasFDerivAt.smul_const a).fderiv]
  rfl

lemma solenoidalFourierTest_valid (k : Fin 2 → ℤ) (sine : Bool) :
    ContDiff ℝ ∞ (solenoidalFourierTest k sine) ∧
      IsTorusPeriodic (solenoidalFourierTest k sine) ∧
        ∀ x, pd 0 (solenoidalFourierTest k sine) x 0 +
          pd 1 (solenoidalFourierTest k sine) x 1 = 0 := by
  cases sine
  · have hc := isScalarTest_boxFourier_cos k
    refine ⟨hc.1.smul contDiff_const, fun x i => ?_, fun x => ?_⟩
    · exact congrArg (fun r : ℝ => r • torusVec (-(k 1 : ℝ)) (k 0 : ℝ)) (hc.2 x i)
    · change pd 0 (fun y => Real.cos (boxFourierPhase k y) •
        torusVec (-(k 1 : ℝ)) (k 0 : ℝ)) x 0 + pd 1 (fun y =>
          Real.cos (boxFourierPhase k y) • torusVec (-(k 1 : ℝ)) (k 0 : ℝ)) x 1 = 0
      rw [pd_smul_const_vector (hc.1.differentiable (by simp)),
        pd_smul_const_vector (hc.1.differentiable (by simp)), pd_boxFourier_cos, pd_boxFourier_cos]
      simp only [PiLp.smul_apply, smul_eq_mul, torusVec_apply_zero, torusVec_apply_one]
      ring
  · have hs := isScalarTest_boxFourier_sin k
    refine ⟨hs.1.smul contDiff_const, fun x i => ?_, fun x => ?_⟩
    · exact congrArg (fun r : ℝ => r • torusVec (-(k 1 : ℝ)) (k 0 : ℝ)) (hs.2 x i)
    · change pd 0 (fun y => Real.sin (boxFourierPhase k y) •
        torusVec (-(k 1 : ℝ)) (k 0 : ℝ)) x 0 + pd 1 (fun y =>
          Real.sin (boxFourierPhase k y) • torusVec (-(k 1 : ℝ)) (k 0 : ℝ)) x 1 = 0
      rw [pd_smul_const_vector (hs.1.differentiable (by simp)),
        pd_smul_const_vector (hs.1.differentiable (by simp)), pd_boxFourier_sin, pd_boxFourier_sin]
      simp only [PiLp.smul_apply, smul_eq_mul, torusVec_apply_zero, torusVec_apply_one]
      ring

lemma pairing_smul_torusVec (f : R2 → ℝ) (a b : ℝ) (u : L2T) :
    eulerSpatialPairing (fun x => f x • torusVec a b) u =
      a * (∫ x in torusBox, u x 0 * f x) + b * (∫ x in torusBox, u x 1 * f x) := by
  simp only [eulerSpatialPairing, Fin.sum_univ_two, PiLp.smul_apply, smul_eq_mul,
    torusVec_apply_zero, torusVec_apply_one]
  have h₀ (x : R2) : u x 0 * (f x * a) = a * (u x 0 * f x) := by ring
  have h₁ (x : R2) : u x 1 * (f x * b) = b * (u x 1 * f x) := by ring
  simp_rw [h₀, h₁]
  rw [integral_const_mul, integral_const_mul]

lemma curl_coeff_eq_of_weakTestMap_eq {u v : L2T} (h : weakTestMap u = weakTestMap v)
    (k : Fin 2 → ℤ) :
    (k 0 : ℂ) * boxFourierCoeff (fun x => u x 1) k -
      (k 1 : ℂ) * boxFourierCoeff (fun x => u x 0) k =
    (k 0 : ℂ) * boxFourierCoeff (fun x => v x 1) k -
      (k 1 : ℂ) * boxFourierCoeff (fun x => v x 0) k := by
  have hp (sine : Bool) := congrFun h ⟨solenoidalFourierTest k sine,
    solenoidalFourierTest_valid k sine⟩
  have hc := hp false
  have hs := hp true
  change eulerSpatialPairing (fun x => Real.cos (boxFourierPhase k x) •
    torusVec (-(k 1 : ℝ)) (k 0 : ℝ)) u = eulerSpatialPairing (fun x =>
      Real.cos (boxFourierPhase k x) • torusVec (-(k 1 : ℝ)) (k 0 : ℝ)) v at hc
  change eulerSpatialPairing (fun x => Real.sin (boxFourierPhase k x) •
    torusVec (-(k 1 : ℝ)) (k 0 : ℝ)) u = eulerSpatialPairing (fun x =>
      Real.sin (boxFourierPhase k x) • torusVec (-(k 1 : ℝ)) (k 0 : ℝ)) v at hs
  rw [pairing_smul_torusVec, pairing_smul_torusVec] at hc hs
  apply Complex.ext <;>
    simp only [boxFourierCoeff, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero, add_zero]
  · linarith
  · linarith

lemma coord_integral_eq_of_weakTestMap_eq {u v : L2T} (h : weakTestMap u = weakTestMap v)
    (i : Fin 2) : (∫ x in torusBox, u x i) = ∫ x in torusBox, v x i := by
  let ψ : R2 → R2 := fun _ => EuclideanSpace.single i 1
  have hψ : ContDiff ℝ ∞ ψ ∧ IsTorusPeriodic ψ ∧
      ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0 := by
    exact ⟨contDiff_const, fun _ _ => rfl, by simp [ψ, pd]⟩
  have hp := congrFun h ⟨ψ, hψ⟩
  change eulerSpatialPairing ψ u = eulerSpatialPairing ψ v at hp
  fin_cases i <;> simpa [eulerSpatialPairing, ψ, EuclideanSpace.single_apply,
    Fin.sum_univ_two] using hp

lemma frequencySq_pos {k : Fin 2 → ℤ} (hk : k ≠ 0) : 0 < frequencySq k := by
  have h : k 0 ≠ 0 ∨ k 1 ≠ 0 := by
    by_contra! hz
    apply hk
    ext i
    fin_cases i <;> simp [hz]
  rcases h with h | h
  · have h₀ : (k 0 : ℝ) ≠ 0 := by exact_mod_cast h
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h₀) (sq_nonneg _)
  · have h₁ : (k 1 : ℝ) ≠ 0 := by exact_mod_cast h
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h₁)

lemma boxFourierCoeff_eq_of_weakTestMap_eq {u v : L2T}
    (hu : DivFree u) (hv : DivFree v) (h : weakTestMap u = weakTestMap v)
    (k : Fin 2 → ℤ) (i : Fin 2) :
    boxFourierCoeff (fun x => u x i) k = boxFourierCoeff (fun x => v x i) k := by
  by_cases hk : k = 0
  · subst k
    simp only [boxFourierCoeff, boxFourierPhase_apply, Pi.zero_apply, Int.cast_zero,
      zero_mul, Finset.sum_const_zero, Real.cos_zero, mul_one, Real.sin_zero, mul_zero,
      integral_zero, neg_zero]
    exact Complex.ext (coord_integral_eq_of_weakTestMap_eq h i) rfl
  let a := boxFourierCoeff (fun x => u x 0) k - boxFourierCoeff (fun x => v x 0) k
  let b := boxFourierCoeff (fun x => u x 1) k - boxFourierCoeff (fun x => v x 1) k
  have hd : (k 0 : ℂ) * a + (k 1 : ℂ) * b = 0 := by
    dsimp only [a, b]
    linear_combination boxFourier_div_identity u hu k - boxFourier_div_identity v hv k
  have hc : (k 0 : ℂ) * b - (k 1 : ℂ) * a = 0 := by
    dsimp only [a, b]
    linear_combination curl_coeff_eq_of_weakTestMap_eq h k
  have hid := fourier_div_curl_identity k a b
  rw [hd, hc, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hid
  have hpos := frequencySq_pos hk
  have hz : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 0 := (mul_eq_zero.mp hid).resolve_left hpos.ne'
  have ha : a = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg a, sq_nonneg ‖b‖])
  have hb : b = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg b, sq_nonneg ‖a‖])
  fin_cases i
  · exact sub_eq_zero.mp ha
  · exact sub_eq_zero.mp hb

/-- Smooth divergence-free tests determine a divergence-free `L²`
velocity in the actual fundamental-square model. -/
theorem eq_of_smooth_divFree_pairings {u v : L2T}
    (hu : DivFree u) (hv : DivFree v) (h : weakTestMap u = weakTestMap v) : u = v := by
  have hcoord (j : Fin 2) : boxComplexCoord j u = boxComplexCoord j v := by
    apply torusL2Equiv.injective
    apply UnitAddTorus.mFourierBasis.repr.injective
    ext k
    simp only [UnitAddTorus.mFourierBasis_repr]
    rw [mFourierCoeff_torusL2Equiv_real (coeFn_boxComplexCoord j u) (integrable_velocity_coord u j),
      mFourierCoeff_torusL2Equiv_real (coeFn_boxComplexCoord j v) (integrable_velocity_coord v j),
      boxFourierCoeff_eq_of_weakTestMap_eq hu hv h]
  apply Lp.ext
  have h₀ := coeFn_boxComplexCoord 0 u
  have h₁ := coeFn_boxComplexCoord 1 u
  rw [hcoord] at h₀ h₁
  filter_upwards [h₀, h₁, coeFn_boxComplexCoord 0 v, coeFn_boxComplexCoord 1 v]
    with x hu₀ hu₁ hv₀ hv₁
  ext i
  fin_cases i
  · exact Complex.ofReal_injective (hu₀.symm.trans hv₀)
  · exact Complex.ofReal_injective (hu₁.symm.trans hv₁)

end Euler2D

end
