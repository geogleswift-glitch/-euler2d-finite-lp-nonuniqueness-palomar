module

public import RequestProject.Euler.TorusGreenCorrection

/-!
# Quarter-turn symmetry of the constructed torus Green correction

The symmetry is derived from the actual radial planar error, a rotation
of the integer lattice, and Fourier uniqueness for periodic harmonic
functions.  It is not an assumption on the correction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal
open Laplacian

namespace Euler2D

open SmoothPoissonConstruction

/-- A globally smooth periodic harmonic function on the square torus is
constant, by its actual Fourier reconstruction. -/
theorem eq_const_of_smooth_periodic_laplacian_zero {f : R2 → ℝ}
    (hf : IsScalarTest f) (hΔ : ∀ x, Δ f x = 0) (x y : R2) : f x = f y := by
  have hreg : regularizer f = f := by
    funext z
    have hz := hΔ z
    rw [laplacian_eq_pd_sum (hf.1.of_le (by decide))] at hz
    simp only [regularizer]
    linarith
  have hcoeff (k : Fin 2 → ℤ) (hk : k ≠ 0) : boxFourierCoeff f k = 0 := by
    have h := boxFourierCoeff_regularizer hf k
    rw [hreg] at h
    have hq : (frequencySq k : ℂ) ≠ 0 := by
      have hpos : 0 < frequencySq k := lt_of_lt_of_le zero_lt_one (one_le_frequencySq hk)
      exact_mod_cast ne_of_gt hpos
    have he : (frequencySq k : ℂ) * boxFourierCoeff f k = 0 := by
      push_cast at h
      linear_combination -h
    exact (mul_eq_zero.mp he).resolve_left hq
  have heval (z : R2) : f z = (physicalCoeff f 0).re := by
    calc f z = modeSeries (physicalCoeff f) z := congrFun (modeSeries_physicalCoeff hf).symm z
         _ = _ := ?_
    change (∑' k, realFourierMode (physicalCoeff f k) k z) = _
    rw [tsum_eq_single (0 : Fin 2 → ℤ) (fun k hk => by
      simp [physicalCoeff, hcoeff k hk])]
    simp [realFourierMode, boxFourierPhase_apply]
  exact (heval x).trans (heval y).symm

/-- The physical quarter-turn about the pole at the square's center. -/
def torusQuarterTurn (x : R2) : R2 := torusCenter + perpJ (x - torusCenter)

@[simp] lemma torusQuarterTurn_center : torusQuarterTurn torusCenter = torusCenter := by
  simp [torusQuarterTurn, perpJ]

lemma torusQuarterTurn_smooth : ContDiff ℝ ∞ torusQuarterTurn :=
  contDiff_const.add (perpJL.contDiff.comp (contDiff_id.sub contDiff_const))

lemma hasFDerivAt_torusQuarterTurn (x : R2) : HasFDerivAt torusQuarterTurn perpJL x := by
  convert (perpJL.hasFDerivAt (x := x - torusCenter)).comp x
    ((hasFDerivAt_id x).sub_const torusCenter) |>.const_add torusCenter using 1

/-- Rotation of the actual two-dimensional integer lattice. -/
def torusLatticeQuarterTurn : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun k := ![-k 1, k 0]
  invFun k := ![k 1, -k 0]
  left_inv k := by ext i; fin_cases i <;> simp
  right_inv k := by ext i; fin_cases i <;> simp

lemma torusLatticeShift_quarterTurn (k : Fin 2 → ℤ) :
    torusLatticeShift (torusLatticeQuarterTurn k) = perpJ (torusLatticeShift k) := by
  ext i
  fin_cases i <;> simp [torusLatticeQuarterTurn, perpJ, torusLatticeShift_apply]

lemma localPlanarKernelError_perpJ (x : R2) :
    localPlanarKernelError (perpJ x) = localPlanarKernelError x := by
  simp only [localPlanarKernelError, radialKernelError, norm_perpJ]

/-- Rotation of the lattice preserves the actual periodized radial error. -/
theorem periodicCenteredSource_localPlanarKernelError_quarterTurn (x : R2) :
    periodicCenteredSource localPlanarKernelError (torusQuarterTurn x) =
      periodicCenteredSource localPlanarKernelError x := by
  change (∑' k, localPlanarKernelError
    (torusQuarterTurn x + torusLatticeShift k - torusCenter)) = _
  rw [← torusLatticeQuarterTurn.tsum_eq]
  change (∑' k, localPlanarKernelError
    (torusQuarterTurn x + torusLatticeShift (torusLatticeQuarterTurn k) - torusCenter)) = _
  apply tsum_congr
  intro k
  rw [torusLatticeShift_quarterTurn]
  have he : torusQuarterTurn x + perpJ (torusLatticeShift k) - torusCenter =
      perpJ (x + torusLatticeShift k - torusCenter) := by
    ext i
    fin_cases i <;> simp [torusQuarterTurn, perpJ, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]
  rw [he, localPlanarKernelError_perpJ]

theorem canonicalTorusCorrectionSource_quarterTurn (x : R2) :
    canonicalTorusCorrectionSource (torusQuarterTurn x) = canonicalTorusCorrectionSource x := by
  exact congrArg (fun z : ℝ => -z - ((2 * π) ^ 2)⁻¹)
    (periodicCenteredSource_localPlanarKernelError_quarterTurn x)

lemma torusQuarterTurn_add_single_zero (x : R2) :
    torusQuarterTurn (x + EuclideanSpace.single 0 (2 * π)) =
      torusQuarterTurn x + EuclideanSpace.single 1 (2 * π) := by
  ext i
  fin_cases i <;> simp [torusQuarterTurn, perpJ, EuclideanSpace.single_apply,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma torusQuarterTurn_add_single_one (x : R2) :
    torusQuarterTurn (x + EuclideanSpace.single 1 (2 * π)) =
      torusQuarterTurn x - EuclideanSpace.single 0 (2 * π) := by
  ext i
  fin_cases i <;> simp [torusQuarterTurn, perpJ, EuclideanSpace.single_apply,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma IsTorusPeriodic.comp_torusQuarterTurn {F : Type*} {f : R2 → F}
    (hf : IsTorusPeriodic f) : IsTorusPeriodic (f ∘ torusQuarterTurn) := by
  intro x i
  fin_cases i
  · change f (torusQuarterTurn (x + EuclideanSpace.single 0 (2 * π))) = _
    rw [torusQuarterTurn_add_single_zero, hf]
    rfl
  · change f (torusQuarterTurn (x + EuclideanSpace.single 1 (2 * π))) = _
    rw [torusQuarterTurn_add_single_one]
    have h := hf (torusQuarterTurn x - EuclideanSpace.single 0 (2 * π)) 0
    simpa only [sub_add_cancel] using h.symm

@[simp] lemma perpJL_single_zero :
    perpJL (EuclideanSpace.single 0 1) = EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp [perpJ, EuclideanSpace.single_apply]

@[simp] lemma perpJL_single_one :
    perpJL (EuclideanSpace.single 1 1) = -EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i <;> simp [perpJ, EuclideanSpace.single_apply]

lemma pd_zero_comp_torusQuarterTurn {f : R2 → ℝ} (hf : Differentiable ℝ f) (x : R2) :
    pd 0 (f ∘ torusQuarterTurn) x = pd 1 f (torusQuarterTurn x) := by
  have hd := (hf (torusQuarterTurn x)).hasFDerivAt.comp x (hasFDerivAt_torusQuarterTurn x)
  unfold pd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, perpJL_single_zero]

lemma pd_one_comp_torusQuarterTurn {f : R2 → ℝ} (hf : Differentiable ℝ f) (x : R2) :
    pd 1 (f ∘ torusQuarterTurn) x = -pd 0 f (torusQuarterTurn x) := by
  have hd := (hf (torusQuarterTurn x)).hasFDerivAt.comp x (hasFDerivAt_torusQuarterTurn x)
  unfold pd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, perpJL_single_one, map_neg]

/-- The intrinsic Laplacian is invariant under the actual affine rotation. -/
theorem laplacian_comp_torusQuarterTurn {f : R2 → ℝ} (hf : ContDiff ℝ ∞ f) (x : R2) :
    Δ (f ∘ torusQuarterTurn) x = Δ f (torusQuarterTurn x) := by
  have hd := hf.differentiable (by simp)
  have hp (i : Fin 2) : ContDiff ℝ ∞ (pd i f) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have h₀ : pd 0 (f ∘ torusQuarterTurn) = pd 1 f ∘ torusQuarterTurn :=
    funext (pd_zero_comp_torusQuarterTurn hd)
  have h₁ : pd 1 (f ∘ torusQuarterTurn) = -(pd 0 f ∘ torusQuarterTurn) :=
    funext (pd_one_comp_torusQuarterTurn hd)
  rw [laplacian_eq_pd_sum ((hf.comp torusQuarterTurn_smooth).of_le (by decide)),
    laplacian_eq_pd_sum (hf.of_le (by decide)), h₀, h₁]
  rw [pd_zero_comp_torusQuarterTurn ((hp 1).differentiable (by simp))]
  have hn : pd 1 (-(pd 0 f ∘ torusQuarterTurn)) x =
      -pd 1 (pd 0 f ∘ torusQuarterTurn) x := by
    simp only [pd, fderiv_neg, ContinuousLinearMap.neg_apply]
  rw [hn, pd_one_comp_torusQuarterTurn ((hp 0).differentiable (by simp)), neg_neg]
  exact add_comm _ _

/-- The actual Fourier-constructed correction inherits the radial source's
quarter-turn symmetry.  The additive constant is fixed at the center. -/
theorem torusGreenCorrection_quarterTurn (x : R2) :
    torusGreenCorrection (torusQuarterTurn x) = torusGreenCorrection x := by
  let D : R2 → ℝ := torusGreenCorrection ∘ torusQuarterTurn + (-1 : ℝ) • torusGreenCorrection
  have hrot : ContDiff ℝ ∞ (torusGreenCorrection ∘ torusQuarterTurn) :=
    torusGreenCorrection_smooth.comp torusQuarterTurn_smooth
  have hD : IsScalarTest D := by
    refine ⟨hrot.add (torusGreenCorrection_smooth.const_smul (-1 : ℝ)), ?_⟩
    intro y i
    change (torusGreenCorrection ∘ torusQuarterTurn) (y + EuclideanSpace.single i (2 * π)) +
      (-1) * torusGreenCorrection (y + EuclideanSpace.single i (2 * π)) = _
    rw [torusGreenCorrection_periodic.comp_torusQuarterTurn y i,
      torusGreenCorrection_periodic y i]
    rfl
  have hΔD (y : R2) : Δ D y = 0 := by
    change Δ (torusGreenCorrection ∘ torusQuarterTurn +
      fun z => (-1 : ℝ) • torusGreenCorrection z) y = 0
    rw [(hrot.of_le (by decide)).contDiffAt.laplacian_add
      ((torusGreenCorrection_smooth.const_smul (-1 : ℝ)).of_le (by decide)).contDiffAt]
    change Δ (torusGreenCorrection ∘ torusQuarterTurn) y +
      Δ ((-1 : ℝ) • torusGreenCorrection) y = 0
    rw [InnerProductSpace.laplacian_smul (-1 : ℝ)
        (torusGreenCorrection_smooth.of_le (by decide)).contDiffAt,
      laplacian_comp_torusQuarterTurn torusGreenCorrection_smooth,
      torusGreenCorrection_laplacian, torusGreenCorrection_laplacian,
      canonicalTorusCorrectionSource_quarterTurn]
    simp
  have he := eq_const_of_smooth_periodic_laplacian_zero hD hΔD x torusCenter
  change torusGreenCorrection (torusQuarterTurn x) + (-1) * torusGreenCorrection x =
    torusGreenCorrection (torusQuarterTurn torusCenter) + (-1) * torusGreenCorrection torusCenter at he
  rw [torusQuarterTurn_center] at he
  linarith

theorem torusGreenQuadratic_quarterTurn (x : R2) :
    torusGreenQuadratic (torusQuarterTurn x) = torusGreenQuadratic x := by
  simp only [torusGreenQuadratic, torusQuarterTurn, add_sub_cancel_left, norm_perpJ]

/-- The constructed local harmonic remainder has the fourfold symmetry
needed for the cancellation of the Green kernel's higher derivatives. -/
theorem torusGreenHarmonicRemainder_quarterTurn (x : R2) :
    torusGreenHarmonicRemainder (torusQuarterTurn x) = torusGreenHarmonicRemainder x := by
  change torusGreenCorrection (torusQuarterTurn x) + torusGreenQuadratic (torusQuarterTurn x) = _
  rw [torusGreenCorrection_quarterTurn, torusGreenQuadratic_quarterTurn]
  rfl

/-- The directional derivatives of an invariant scalar obey the actual
rotation chain rule. -/
lemma fderiv_quarterTurn_of_invariant {f : R2 → ℝ} (hf : Differentiable ℝ f)
    (hrot : ∀ x, f (torusQuarterTurn x) = f x) (x v : R2) :
    fderiv ℝ f (torusQuarterTurn x) (perpJ v) = fderiv ℝ f x v := by
  have he : f ∘ torusQuarterTurn = f := funext hrot
  have hd := (hf (torusQuarterTurn x)).hasFDerivAt.comp x (hasFDerivAt_torusQuarterTurn x)
  rw [he] at hd
  have hv := congrArg (fun L : R2 →L[ℝ] ℝ => L v) hd.fderiv
  exact hv.symm

theorem fderiv_torusGreenCorrection_quarterTurn (x v : R2) :
    fderiv ℝ torusGreenCorrection (torusQuarterTurn x) (perpJ v) =
      fderiv ℝ torusGreenCorrection x v :=
  fderiv_quarterTurn_of_invariant (torusGreenCorrection_smooth.differentiable (by simp))
    torusGreenCorrection_quarterTurn x v

theorem fderiv_torusGreenHarmonicRemainder_quarterTurn (x v : R2) :
    fderiv ℝ torusGreenHarmonicRemainder (torusQuarterTurn x) (perpJ v) =
      fderiv ℝ torusGreenHarmonicRemainder x v :=
  fderiv_quarterTurn_of_invariant (torusGreenHarmonicRemainder_smooth.differentiable (by simp))
    torusGreenHarmonicRemainder_quarterTurn x v

end Euler2D

end
