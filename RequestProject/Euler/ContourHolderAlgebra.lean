module

public import RequestProject.Euler.ContourHolderNorm

/-!
# Actual conjugation, multiplication and reciprocals of Hölder functions

All operations are the literal pointwise complex operations.  In the inherited
max norm multiplication is bounded by 2, while conjugation is an isometry.
The reciprocal of a function with a genuine positive pointwise lower bound
has the genuine Hölder modulus obtained from the inverse-difference identity.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction ComplexConjugate

namespace Euler2D

variable {X : Type*} [MetricSpace X]

-- Canonical inherited structures, named to short-circuit higher operator-space inference.
instance (priority := 2000) complexHolderSpace_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (HolderFunctionSpace X ℂ γ) :=
  Submodule.normedAddCommGroup (holderGraphSubmodule X ℂ γ)

instance (priority := 2000) complexHolderSpace_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (HolderFunctionSpace X ℂ γ) :=
  Submodule.normedSpace (holderGraphSubmodule X ℂ γ)

private lemma holderWith_of_norm_sub_bound {γ C : ℝ≥0} {f : X → ℂ}
    (h : ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ (γ : ℝ)) : HolderWith C γ f := by
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hb : dist (f x) (f y) ≤ C * dist x y ^ (γ : ℝ) := by
    simpa only [dist_eq_norm] using h x y
  exact_mod_cast hb

namespace HolderFunctionSpace

variable {γ : ℝ≥0}

lemma norm_le_of_pointwise_holder_bounds (f : HolderFunctionSpace X ℂ γ) {C : ℝ≥0}
    (hsup : ∀ x, ‖f x‖ ≤ C) (hholder : HolderWith C γ (fun x => f x)) : ‖f‖ ≤ C := by
  rw [norm_eq_max_uniform_holder]
  apply max_le
  · exact (BoundedContinuousFunction.norm_le C.coe_nonneg).mpr hsup
  · exact_mod_cast hholder.nnholderNorm_le

lemma holderWith_conjugate (f : HolderFunctionSpace X ℂ γ) :
    HolderWith ‖f.val.2‖₊ γ (fun x => conj (f x)) := by
  apply holderWith_of_norm_sub_bound
  intro x y
  rw [← map_sub, Complex.norm_conj]
  exact norm_sub_le_quotient f x y

/-- The literal pointwise complex conjugate. -/
def conjugate (f : HolderFunctionSpace X ℂ γ) : HolderFunctionSpace X ℂ γ :=
  ofMemHolder
    (Complex.conjCLE.toContinuousLinearMap.compLeftContinuousBounded X (toBCF γ f))
    (holderWith_conjugate f).memHolder

@[simp] theorem conjugate_apply (f : HolderFunctionSpace X ℂ γ) (x : X) :
    conjugate f x = conj (f x) := rfl

lemma norm_conjugate_le (f : HolderFunctionSpace X ℂ γ) : ‖conjugate f‖ ≤ ‖f‖ := by
  apply norm_le_of_pointwise_holder_bounds (C := ‖f‖₊)
  · intro x
    rw [conjugate_apply, Complex.norm_conj]
    exact norm_eval_le f x
  · have hm : ‖f.val.2‖₊ ≤ ‖f‖₊ := by exact_mod_cast norm_quotient_le f
    exact (holderWith_conjugate f).mono hm

@[simp] theorem conjugate_conjugate (f : HolderFunctionSpace X ℂ γ) :
    conjugate (conjugate f) = f := by
  apply HolderFunctionSpace.ext
  intro x
  change conj (conj (f x)) = f x
  exact Complex.conj_conj _

@[simp] theorem norm_conjugate (f : HolderFunctionSpace X ℂ γ) : ‖conjugate f‖ = ‖f‖ := by
  apply le_antisymm (norm_conjugate_le f)
  simpa only [conjugate_conjugate] using norm_conjugate_le (conjugate f)

/-- Genuine conjugation as a bounded real linear operator. -/
def conjugateCLM (γ : ℝ≥0) : HolderFunctionSpace X ℂ γ →L[ℝ] HolderFunctionSpace X ℂ γ :=
  LinearMap.mkContinuous
    { toFun := conjugate
      map_add' := fun f g => by
        apply HolderFunctionSpace.ext
        intro x
        change conj (f x + g x) = conj (f x) + conj (g x)
        exact map_add (starRingEnd ℂ) _ _
      map_smul' := fun c f => by
        apply HolderFunctionSpace.ext
        intro x
        change conj (c • f x) = c • conj (f x)
        exact map_smul Complex.conjCLE.toContinuousLinearMap c (f x) }
    1 (fun f => by
      change ‖conjugate f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_conjugate_le f)

theorem norm_conjugateCLM_le_one (γ : ℝ≥0) : ‖conjugateCLM (X := X) γ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖conjugate f‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using norm_conjugate_le f

lemma holderWith_pointwiseMul (f g : HolderFunctionSpace X ℂ γ) :
    HolderWith (2 * ‖f‖₊ * ‖g‖₊) γ (fun x => f x * g x) := by
  apply holderWith_of_norm_sub_bound
  intro x y
  change ‖f x * g x - f y * g y‖ ≤ (2 * ‖f‖ * ‖g‖) * dist x y ^ (γ : ℝ)
  have heq : f x * g x - f y * g y = f x * (g x - g y) + (f x - f y) * g y := by ring
  calc
    _ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by
      rw [heq]
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
    _ ≤ ‖f‖ * (‖g‖ * dist x y ^ (γ : ℝ)) +
        (‖f‖ * dist x y ^ (γ : ℝ)) * ‖g‖ :=
      add_le_add
        (mul_le_mul (norm_eval_le f x) (norm_sub_le_holder g x y) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (norm_sub_le_holder f x y) (norm_eval_le g y) (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _)))
    _ = _ := by ring

/-- The literal pointwise product in the actual Hölder space. -/
def pointwiseMul (f g : HolderFunctionSpace X ℂ γ) : HolderFunctionSpace X ℂ γ :=
  ofMemHolder (toBCF γ f * toBCF γ g) (holderWith_pointwiseMul f g).memHolder

@[simp] theorem pointwiseMul_apply (f g : HolderFunctionSpace X ℂ γ) (x : X) :
    pointwiseMul f g x = f x * g x := rfl

theorem norm_pointwiseMul_le (f g : HolderFunctionSpace X ℂ γ) :
    ‖pointwiseMul f g‖ ≤ 2 * ‖f‖ * ‖g‖ := by
  apply norm_le_of_pointwise_holder_bounds (C := 2 * ‖f‖₊ * ‖g‖₊)
  · intro x
    rw [pointwiseMul_apply, norm_mul]
    have hm := mul_le_mul (norm_eval_le f x) (norm_eval_le g x) (norm_nonneg _) (norm_nonneg _)
    change ‖f x‖ * ‖g x‖ ≤ 2 * ‖f‖ * ‖g‖
    nlinarith [mul_nonneg (norm_nonneg f) (norm_nonneg g)]
  · exact holderWith_pointwiseMul f g

def pointwiseMulLM (γ : ℝ≥0) :
    HolderFunctionSpace X ℂ γ →ₗ[ℝ] HolderFunctionSpace X ℂ γ →ₗ[ℝ] HolderFunctionSpace X ℂ γ where
  toFun f :=
    { toFun := pointwiseMul f
      map_add' := fun g h => by
        apply HolderFunctionSpace.ext
        intro x
        change f x * (g x + h x) = f x * g x + f x * h x
        exact mul_add _ _ _
      map_smul' := fun c g => by
        apply HolderFunctionSpace.ext
        intro x
        change f x * (c • g x) = c • (f x * g x)
        exact mul_smul_comm _ _ _ }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply HolderFunctionSpace.ext
    intro x
    change (f x + g x) * h x = f x * h x + g x * h x
    exact add_mul _ _ _
  map_smul' c f := by
    apply LinearMap.ext
    intro g
    apply HolderFunctionSpace.ext
    intro x
    change (c • f x) * g x = c • (f x * g x)
    exact smul_mul_assoc _ _ _

/-- The actual pointwise product as a bounded real bilinear map. -/
def pointwiseMulCLM (γ : ℝ≥0) :
    HolderFunctionSpace X ℂ γ →L[ℝ] HolderFunctionSpace X ℂ γ →L[ℝ] HolderFunctionSpace X ℂ γ :=
  (pointwiseMulLM γ).mkContinuous₂ 2 norm_pointwiseMul_le

@[simp] theorem pointwiseMulCLM_apply (f g : HolderFunctionSpace X ℂ γ) :
    pointwiseMulCLM γ f g = pointwiseMul f g := rfl

theorem norm_pointwiseMulCLM_le_two (γ : ℝ≥0) : ‖pointwiseMulCLM (X := X) γ‖ ≤ 2 :=
  LinearMap.mkContinuous₂_norm_le (pointwiseMulLM (X := X) γ) (C := 2) (by norm_num)
    norm_pointwiseMul_le

lemma norm_inv_le_of_norm_lower (f : HolderFunctionSpace X ℂ γ)
    {c : ℝ≥0} (hc : 0 < c) (hlower : ∀ x, (c : ℝ) ≤ ‖f x‖) (x : X) :
    ‖(f x)⁻¹‖ ≤ (c : ℝ)⁻¹ := by
  rw [norm_inv]
  have hcr : (0 : ℝ) < c := hc
  simpa only [one_div] using one_div_le_one_div_of_le hcr (hlower x)

lemma holderWith_inv_of_norm_lower (f : HolderFunctionSpace X ℂ γ)
    {c : ℝ≥0} (hc : 0 < c) (hlower : ∀ x, (c : ℝ) ≤ ‖f x‖) :
    HolderWith (‖f.val.2‖₊ / c ^ 2) γ (fun x => (f x)⁻¹) := by
  apply holderWith_of_norm_sub_bound
  intro x y
  have hcr : (0 : ℝ) < c := hc
  have hnx : f x ≠ 0 := norm_pos_iff.mp (hcr.trans_le (hlower x))
  have hny : f y ≠ 0 := norm_pos_iff.mp (hcr.trans_le (hlower y))
  have hden : (c : ℝ) * c ≤ ‖f x‖ * ‖f y‖ :=
    mul_le_mul (hlower x) (hlower y) hcr.le (norm_nonneg _)
  change ‖(f x)⁻¹ - (f y)⁻¹‖ ≤
    (‖f.val.2‖ / (c : ℝ) ^ 2) * dist x y ^ (γ : ℝ)
  calc
    _ = ‖f x - f y‖ / (‖f x‖ * ‖f y‖) := by
      simpa only [dist_eq_norm] using dist_inv_inv₀ hnx hny
    _ ≤ ‖f x - f y‖ / ((c : ℝ) * c) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hcr hcr) hden
    _ ≤ (‖f.val.2‖ * dist x y ^ (γ : ℝ)) / ((c : ℝ) * c) :=
      div_le_div_of_nonneg_right (norm_sub_le_quotient f x y) (mul_nonneg hcr.le hcr.le)
    _ = _ := by rw [pow_two]; ring

def inverseBCFOfNormLower (f : HolderFunctionSpace X ℂ γ)
    {c : ℝ≥0} (hc : 0 < c) (hlower : ∀ x, (c : ℝ) ≤ ‖f x‖) : X →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => (f x)⁻¹, (toBCF γ f).continuous.inv₀ (fun x =>
      norm_pos_iff.mp ((show (0 : ℝ) < c from hc).trans_le (hlower x)))⟩
    (2 * (c : ℝ)⁻¹)
    (BoundedContinuousFunction.dist_le_two_norm' (norm_inv_le_of_norm_lower f hc hlower))

/-- The genuine reciprocal of a Hölder function bounded away from zero. -/
def inverseOfNormLowerNN (f : HolderFunctionSpace X ℂ γ)
    {c : ℝ≥0} (hc : 0 < c) (hlower : ∀ x, (c : ℝ) ≤ ‖f x‖) : HolderFunctionSpace X ℂ γ :=
  ofMemHolder (inverseBCFOfNormLower f hc hlower) (holderWith_inv_of_norm_lower f hc hlower).memHolder

@[simp] theorem inverseOfNormLowerNN_apply (f : HolderFunctionSpace X ℂ γ)
    {c : ℝ≥0} (hc : 0 < c) (hlower : ∀ x, (c : ℝ) ≤ ‖f x‖) (x : X) :
    inverseOfNormLowerNN f hc hlower x = (f x)⁻¹ := rfl

theorem norm_inverseOfNormLowerNN_le (f : HolderFunctionSpace X ℂ γ)
    {c : ℝ≥0} (hc : 0 < c) (hlower : ∀ x, (c : ℝ) ≤ ‖f x‖) :
    ‖inverseOfNormLowerNN f hc hlower‖ ≤ max (c : ℝ)⁻¹ (‖f.val.2‖ / (c : ℝ) ^ 2) := by
  rw [norm_eq_max_uniform_holder]
  apply max_le_max
  · exact (BoundedContinuousFunction.norm_le (inv_nonneg.mpr c.coe_nonneg)).mpr
      (norm_inv_le_of_norm_lower f hc hlower)
  · exact_mod_cast (holderWith_inv_of_norm_lower f hc hlower).nnholderNorm_le

/-- Real-constant interface for the actual reciprocal. -/
def inverseOfNormLower (f : HolderFunctionSpace X ℂ γ)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c ≤ ‖f x‖) : HolderFunctionSpace X ℂ γ :=
  inverseOfNormLowerNN f (c := ⟨c, hc.le⟩) hc hlower

@[simp] theorem inverseOfNormLower_apply (f : HolderFunctionSpace X ℂ γ)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c ≤ ‖f x‖) (x : X) :
    inverseOfNormLower f hc hlower x = (f x)⁻¹ := rfl

theorem norm_inverseOfNormLower_le (f : HolderFunctionSpace X ℂ γ)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c ≤ ‖f x‖) :
    ‖inverseOfNormLower f hc hlower‖ ≤ max c⁻¹ (‖f‖ / c ^ 2) := by
  apply (norm_inverseOfNormLowerNN_le f (c := ⟨c, hc.le⟩) hc hlower).trans
  exact max_le_max_left _ (div_le_div_of_nonneg_right (norm_quotient_le f) (sq_nonneg c))

/-- The literal quotient, for the actual boundary densities used in Cauchy integrals. -/
def divideOfNormLower (f g : HolderFunctionSpace X ℂ γ)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c ≤ ‖g x‖) : HolderFunctionSpace X ℂ γ :=
  pointwiseMul f (inverseOfNormLower g hc hlower)

@[simp] theorem divideOfNormLower_apply (f g : HolderFunctionSpace X ℂ γ)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c ≤ ‖g x‖) (x : X) :
    divideOfNormLower f g hc hlower x = f x / g x := by
  rw [div_eq_mul_inv]
  rfl

theorem norm_divideOfNormLower_le (f g : HolderFunctionSpace X ℂ γ)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c ≤ ‖g x‖) :
    ‖divideOfNormLower f g hc hlower‖ ≤
      2 * ‖f‖ * max c⁻¹ (‖g‖ / c ^ 2) :=
  (norm_pointwiseMul_le f _).trans
    (mul_le_mul_of_nonneg_left (norm_inverseOfNormLower_le g hc hlower)
      (mul_nonneg (by norm_num) (norm_nonneg f)))

end HolderFunctionSpace

end Euler2D

end
