module

public import RequestProject.Euler.ContourHolderSpace

/-!
# Actual Hölder functions and the exact Hölder seminorm

Every bounded continuous Hölder function has its genuine difference
quotient in the constructed closed graph.  Conversely, the norm of that
quotient is exactly Mathlib's Hölder seminorm.  Thus the inherited max
norm is equivalent to the usual supremum norm plus Hölder seminorm.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction

namespace Euler2D

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

def holderDifferenceQuotient (γ : ℝ≥0) (f : X → E) (p : HolderDifferencePair X) : E :=
  (dist p.val.1 p.val.2 ^ (γ : ℝ))⁻¹ • (f p.val.1 - f p.val.2)

lemma continuous_holderDifferenceQuotient (γ : ℝ≥0) {f : X → E} (hf : Continuous f) :
    Continuous (holderDifferenceQuotient γ f) := by
  have h₁ : Continuous (fun p : HolderDifferencePair X => p.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have h₂ : Continuous (fun p : HolderDifferencePair X => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hp : Continuous (fun p : HolderDifferencePair X =>
      dist p.val.1 p.val.2 ^ (γ : ℝ)) :=
    (h₁.dist h₂).rpow_const (fun _ => Or.inr γ.coe_nonneg)
  exact (hp.inv₀ (fun p => (Real.rpow_pos_of_pos (dist_pos.mpr p.property) _).ne')).smul
    ((hf.comp h₁).sub (hf.comp h₂))

lemma norm_holderDifferenceQuotient_le {γ C : ℝ≥0} {f : X → E}
    (hf : HolderWith C γ f) (p : HolderDifferencePair X) :
    ‖holderDifferenceQuotient γ f p‖ ≤ C := by
  have hpow : 0 < dist p.val.1 p.val.2 ^ (γ : ℝ) :=
    Real.rpow_pos_of_pos (dist_pos.mpr p.property) _
  have hb : ‖f p.val.1 - f p.val.2‖ ≤ C * dist p.val.1 p.val.2 ^ (γ : ℝ) := by
    simpa only [dist_eq_norm] using hf.dist_le p.val.1 p.val.2
  rw [holderDifferenceQuotient, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpow]
  simpa only [div_eq_mul_inv, mul_comm] using (div_le_iff₀ hpow).mpr hb

def holderDifferenceBCF (γ : ℝ≥0) (f : X →ᵇ E) (hf : MemHolder γ (f : X → E)) :
    HolderDifferencePair X →ᵇ E :=
  BoundedContinuousFunction.mkOfBound
    ⟨holderDifferenceQuotient γ f, continuous_holderDifferenceQuotient γ f.continuous⟩
    (2 * (nnHolderNorm γ (f : X → E) : ℝ))
    (BoundedContinuousFunction.dist_le_two_norm' (fun p =>
      norm_holderDifferenceQuotient_le hf.holderWith p))

namespace HolderFunctionSpace

variable {γ : ℝ≥0}

/-- Every actual bounded Hölder function is a member of the actual
complete graph space, with its genuine difference quotient. -/
def ofMemHolder (f : X →ᵇ E) (hf : MemHolder γ (f : X → E)) : HolderFunctionSpace X E γ := by
  refine ⟨(f, holderDifferenceBCF γ f hf), ?_⟩
  apply (Submodule.mem_iInf _).mpr
  intro p
  change holderGraphOperator X E γ p (f, holderDifferenceBCF γ f hf) = 0
  change holderDifferenceQuotient γ (f : X → E) p -
    (dist p.val.1 p.val.2 ^ (γ : ℝ))⁻¹ • (f p.val.1 - f p.val.2) = 0
  exact sub_self _

@[simp] theorem ofMemHolder_apply (f : X →ᵇ E) (hf : MemHolder γ (f : X → E)) (x : X) :
    ofMemHolder f hf x = f x := rfl

@[simp] theorem toBCF_ofMemHolder (f : X →ᵇ E) (hf : MemHolder γ (f : X → E)) :
    toBCF γ (ofMemHolder f hf) = f := rfl

lemma norm_quotient_le_of_holderWith (f : HolderFunctionSpace X E γ) {C : ℝ≥0}
    (hf : HolderWith C γ (fun x => f x)) : ‖f.val.2‖ ≤ C := by
  apply (BoundedContinuousFunction.norm_le C.coe_nonneg).mpr
  intro p
  rw [holderFunctionSpace_quotient_eq]
  exact norm_holderDifferenceQuotient_le hf p

lemma norm_sub_le_quotient (f : HolderFunctionSpace X E γ) (x y : X) :
    ‖f x - f y‖ ≤ ‖f.val.2‖ * dist x y ^ (γ : ℝ) := by
  by_cases hxy : x = y
  · simp only [hxy, sub_self, norm_zero]
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _)
  let p : HolderDifferencePair X := ⟨(x, y), hxy⟩
  have hpow : 0 < dist x y ^ (γ : ℝ) := Real.rpow_pos_of_pos (dist_pos.mpr hxy) _
  have hq := f.val.2.norm_coe_le_norm p
  rw [holderFunctionSpace_quotient_eq] at hq
  change ‖(dist x y ^ (γ : ℝ))⁻¹ • (f x - f y)‖ ≤ ‖f.val.2‖ at hq
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpow] at hq
  apply (div_le_iff₀ hpow).mp
  simpa only [div_eq_mul_inv, mul_comm] using hq

lemma holderWith_quotient_norm (f : HolderFunctionSpace X E γ) :
    HolderWith ‖f.val.2‖₊ γ (fun x => f x) := by
  intro x y
  rw [edist_nndist, edist_nndist,
    ← ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hb : dist (f x) (f y) ≤ ‖f.val.2‖ * dist x y ^ (γ : ℝ) := by
    simpa only [dist_eq_norm] using norm_sub_le_quotient f x y
  exact_mod_cast hb

theorem norm_quotient_eq_holderSeminorm (f : HolderFunctionSpace X E γ) :
    ‖f.val.2‖ = (nnHolderNorm γ (fun x => f x) : ℝ) := by
  apply le_antisymm
  · exact norm_quotient_le_of_holderWith f (memHolder f).holderWith
  · exact_mod_cast (holderWith_quotient_norm f).nnholderNorm_le

theorem norm_eq_max_uniform_holder (f : HolderFunctionSpace X E γ) :
    ‖f‖ = max ‖toBCF γ f‖ (nnHolderNorm γ (fun x => f x) : ℝ) := by
  change max ‖f.val.1‖ ‖f.val.2‖ = max ‖f.val.1‖ _
  rw [norm_quotient_eq_holderSeminorm]

theorem norm_le_uniform_add_holder (f : HolderFunctionSpace X E γ) :
    ‖f‖ ≤ ‖toBCF γ f‖ + (nnHolderNorm γ (fun x => f x) : ℝ) := by
  rw [norm_eq_max_uniform_holder]
  exact max_le (le_add_of_nonneg_right (NNReal.coe_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))

theorem uniform_add_holder_le_two_norm (f : HolderFunctionSpace X E γ) :
    ‖toBCF γ f‖ + (nnHolderNorm γ (fun x => f x) : ℝ) ≤ 2 * ‖f‖ := by
  have h₁ := norm_toBCF_le f
  have h₂ := norm_quotient_le f
  rw [norm_quotient_eq_holderSeminorm] at h₂
  linarith

end HolderFunctionSpace

/-- Every genuine positive-exponent Hölder function on the actual compact
parameter circle has a representative in the complete contour Hölder space. -/
def contourHolderOfMemHolder {γ : ℝ≥0} (hγ : 0 < γ) (f : ContourCircle → ℂ)
    (hf : MemHolder γ f) : ContourHolderSpace γ :=
  HolderFunctionSpace.ofMemHolder
    (BoundedContinuousFunction.mkOfCompact ⟨f, hf.holderWith.continuous hγ⟩) hf

@[simp] theorem contourHolderOfMemHolder_apply {γ : ℝ≥0} (hγ : 0 < γ)
    (f : ContourCircle → ℂ) (hf : MemHolder γ f) (x : ContourCircle) :
    contourHolderOfMemHolder hγ f hf x = f x := rfl

end Euler2D

end
