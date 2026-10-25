module

public import RequestProject.Euler.ContourHilbertHolderBound
public import RequestProject.Euler.ContourHolderNorm

/-! # The genuine bounded Hilbert increment on the actual Hölder space -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped NNReal Interval

namespace Euler2D

theorem periodic_hilbertIncrement {f : ℝ → ℂ} {P : ℝ} (hf : Function.Periodic f P) :
    Function.Periodic (hilbertIncrement f) P := by
  intro θ
  have he : hilbertIncrementIntegrand f (θ + P) = hilbertIncrementIntegrand f θ := by
    funext τ
    unfold hilbertIncrementIntegrand
    rw [show θ + P + τ = (θ + τ) + P by ring, hf (θ + τ), hf θ]
  exact congrArg (fun F : ℝ → ℂ => ∫ τ in Icc (-Real.pi) Real.pi, F τ) he

theorem periodic_contourHilbertIncrement {γ : ℝ≥0} (f : ContourHolderSpace γ) :
    Function.Periodic (contourHilbertIncrement f) (2 * Real.pi) :=
  periodic_hilbertIncrement (fun θ => congrArg f (AddCircle.coe_add_period (2 * Real.pi) θ))

def contourHilbertOnCircle {γ : ℝ≥0} (f : ContourHolderSpace γ) : ContourCircle → ℂ :=
  (periodic_contourHilbertIncrement f).lift

@[simp] theorem contourHilbertOnCircle_coe {γ : ℝ≥0} (f : ContourHolderSpace γ) (θ : ℝ) :
    contourHilbertOnCircle f (θ : ContourCircle) = contourHilbertIncrement f θ := rfl

theorem holderWith_contourHilbertOnCircle {γ : ℝ≥0} (f : ContourHolderSpace γ)
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    HolderWith (⟨hilbertHolderConstant (γ : ℝ) * ‖f‖,
      mul_nonneg (hilbertHolderConstant_nonneg hγ hγ1) (norm_nonneg f)⟩ : ℝ≥0) γ
      (contourHilbertOnCircle f) := by
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hb : dist (contourHilbertOnCircle f x) (contourHilbertOnCircle f y) ≤
      (hilbertHolderConstant (γ : ℝ) * ‖f‖) * dist x y ^ (γ : ℝ) := by
    obtain ⟨θ, φ, hθ, hφ, _, hdist⟩ := exists_short_contour_representatives x y
    have h := norm_contourHilbertIncrement_sub_le f hγ hγ1 θ φ
    rw [← contourHilbertOnCircle_coe, ← contourHilbertOnCircle_coe, hθ, hφ, ← hdist] at h
    simpa only [_root_.dist_eq_norm] using h
  exact_mod_cast hb

def contourHilbertHolder {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (f : ContourHolderSpace γ) : ContourHolderSpace γ :=
  contourHolderOfMemHolder (by exact_mod_cast hγ) (contourHilbertOnCircle f)
    (holderWith_contourHilbertOnCircle f hγ hγ1).memHolder

@[simp] theorem contourHilbertHolder_apply {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (f : ContourHolderSpace γ) (x : ContourCircle) :
    contourHilbertHolder hγ hγ1 f x = contourHilbertOnCircle f x := rfl

def hilbertOperatorConstant (γ : ℝ) : ℝ := 2 * Real.pi ^ γ / γ + hilbertHolderConstant γ

theorem hilbertOperatorConstant_nonneg {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    0 ≤ hilbertOperatorConstant γ := by
  unfold hilbertOperatorConstant
  exact add_nonneg (by positivity) (hilbertHolderConstant_nonneg hγ hγ1)

theorem norm_contourHilbertHolder_le {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (f : ContourHolderSpace γ) :
    ‖contourHilbertHolder hγ hγ1 f‖ ≤ hilbertOperatorConstant (γ : ℝ) * ‖f‖ := by
  have hU : 0 ≤ 2 * Real.pi ^ (γ : ℝ) / (γ : ℝ) := by positivity
  have hC := hilbertHolderConstant_nonneg hγ hγ1
  rw [HolderFunctionSpace.norm_eq_max_uniform_holder]
  apply max_le
  · apply (BoundedContinuousFunction.norm_le
      (mul_nonneg (hilbertOperatorConstant_nonneg hγ hγ1) (norm_nonneg f))).mpr
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change ‖contourHilbertIncrement f θ‖ ≤ _
    have hb := norm_contourHilbertIncrement_le f hγ θ
    rw [mul_comm ‖f‖] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC) (norm_nonneg f))
  · have hh := (holderWith_contourHilbertOnCircle f hγ hγ1).nnholderNorm_le
    have hn : (nnHolderNorm γ (contourHilbertOnCircle f) : ℝ) ≤
        hilbertHolderConstant (γ : ℝ) * ‖f‖ := by exact_mod_cast hh
    exact hn.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hU) (norm_nonneg f))

theorem hilbertIncrement_add {f g : ℝ → ℂ} {θ : ℝ}
    (hf : IntegrableOn (hilbertIncrementIntegrand f θ) (Icc (-Real.pi) Real.pi))
    (hg : IntegrableOn (hilbertIncrementIntegrand g θ) (Icc (-Real.pi) Real.pi)) :
    hilbertIncrement (f + g) θ = hilbertIncrement f θ + hilbertIncrement g θ := by
  have he : hilbertIncrementIntegrand (f + g) θ = fun τ =>
      hilbertIncrementIntegrand f θ τ + hilbertIncrementIntegrand g θ τ := by
    funext τ
    dsimp only [hilbertIncrementIntegrand, Pi.add_apply]
    ring
  unfold hilbertIncrement
  rw [he, integral_add hf hg]

theorem hilbertIncrement_smul (f : ℝ → ℂ) (θ a : ℝ) :
    hilbertIncrement (a • f) θ = a • hilbertIncrement f θ := by
  have he : hilbertIncrementIntegrand (a • f) θ =
      fun τ => a • hilbertIncrementIntegrand f θ τ := by
    funext τ
    dsimp only [hilbertIncrementIntegrand, Pi.smul_apply]
    simp only [Complex.real_smul]
    ring
  unfold hilbertIncrement
  rw [he, integral_smul]

theorem integrableOn_contourHilbertIncrementIntegrand {γ : ℝ≥0}
    (f : ContourHolderSpace γ) (hγ : 0 < (γ : ℝ)) (θ : ℝ) :
    IntegrableOn (hilbertIncrementIntegrand (fun t : ℝ => f (t : ContourCircle)) θ)
      (Icc (-Real.pi) Real.pi) :=
  integrableOn_hilbertIncrementIntegrand
    (((HolderFunctionSpace.toBCF γ f).continuous.comp
      (AddCircle.continuous_mk' (2 * Real.pi))).measurable)
    hγ (norm_nonneg f) Real.pi_pos.le (fun τ _ => norm_contourHolder_lift_sub_le f θ τ)

def contourHilbertLinearMap {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    ContourHolderSpace γ →ₗ[ℝ] ContourHolderSpace γ where
  toFun := contourHilbertHolder hγ hγ1
  map_add' f g := by
    apply HolderFunctionSpace.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change hilbertIncrement ((fun t : ℝ => f (t : ContourCircle)) +
      (fun t : ℝ => g (t : ContourCircle))) θ = _
    exact hilbertIncrement_add (integrableOn_contourHilbertIncrementIntegrand f hγ θ)
      (integrableOn_contourHilbertIncrementIntegrand g hγ θ)
  map_smul' a f := by
    apply HolderFunctionSpace.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change hilbertIncrement (a • (fun t : ℝ => f (t : ContourCircle))) θ = _
    exact hilbertIncrement_smul _ _ _

/-- A genuine bounded operator, proved by the complete real near/far argument. -/
def contourHilbertOperator {γ : ℝ≥0} (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    ContourHolderSpace γ →L[ℝ] ContourHolderSpace γ :=
  (contourHilbertLinearMap hγ hγ1).mkContinuous (hilbertOperatorConstant (γ : ℝ))
    (norm_contourHilbertHolder_le hγ hγ1)

@[simp] theorem contourHilbertOperator_apply {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (f : ContourHolderSpace γ) (θ : ℝ) :
    contourHilbertOperator hγ hγ1 f (θ : ContourCircle) = contourHilbertIncrement f θ := rfl

theorem norm_contourHilbertOperator_le {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    ‖contourHilbertOperator hγ hγ1‖ ≤ hilbertOperatorConstant (γ : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact hilbertOperatorConstant_nonneg hγ hγ1
  · exact norm_contourHilbertHolder_le hγ hγ1

end Euler2D

end
