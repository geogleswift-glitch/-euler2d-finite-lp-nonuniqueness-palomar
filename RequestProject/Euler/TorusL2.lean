module

public import RequestProject.Euler.TorusModel

/-!
# The normalized `L²` identification of the two torus models

The map sends a box function `f` to `2π f ∘ torusRep`. Its norm is
unchanged, since the representative map divides area by `(2π)²`.
This is a genuine complex linear isometry equivalence, so Fourier
operators and their quantitative bounds can be transported to the box.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

abbrev BoxFourierL2 := Lp ℂ 2 μT

lemma ae_eq_comp_torusRep {F : Type*} {f g : R2 → F} (h : f =ᵐ[μT] g) :
    f ∘ torusRep =ᵐ[volume] g ∘ torusRep :=
  measurePreserving_torusRep.quasiMeasurePreserving.ae_eq_comp
    (Measure.ae_smul_measure h ((ENNReal.ofReal ((2 * Real.pi) ^ 2))⁻¹))

lemma memLp_normalized_torusLift (f : BoxFourierL2) :
    MemLp ((2 * Real.pi : ℂ) • ((f : R2 → ℂ) ∘ torusRep)) 2 volume := by
  have hf := (Lp.memLp f).smul_measure
    (show (ENNReal.ofReal ((2 * Real.pi) ^ 2))⁻¹ ≠ ∞ from
      ENNReal.inv_ne_top.mpr (by positivity))
  exact (hf.comp_measurePreserving measurePreserving_torusRep).const_smul _

def torusLiftFn (f : BoxFourierL2) : FourierL2 :=
  (memLp_normalized_torusLift f).toLp _

lemma coeFn_torusLiftFn (f : BoxFourierL2) :
    torusLiftFn f =ᵐ[volume] fun t => (2 * Real.pi : ℂ) * f (torusRep t) :=
  (memLp_normalized_torusLift f).coeFn_toLp

/-- The normalized pullback from the actual square is complex linear. -/
def torusLiftLinear : BoxFourierL2 →ₗ[ℂ] FourierL2 where
  toFun := torusLiftFn
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coeFn_torusLiftFn (f + g),
      Lp.coeFn_add (torusLiftFn f) (torusLiftFn g),
      coeFn_torusLiftFn f, coeFn_torusLiftFn g,
      ae_eq_comp_torusRep (Lp.coeFn_add f g)] with t hfg hadd hf hg harg
    simp only [Function.comp_def, Pi.add_apply] at harg
    rw [hfg, hadd]
    change _ = torusLiftFn f t + torusLiftFn g t
    rw [hf, hg, harg, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coeFn_torusLiftFn (c • f), Lp.coeFn_smul c (torusLiftFn f),
      coeFn_torusLiftFn f, ae_eq_comp_torusRep (Lp.coeFn_smul c f)] with t hcf hsmul hf harg
    simp only [Function.comp_def, Pi.smul_apply, smul_eq_mul] at harg
    change torusLiftFn (c • f) t = (c • torusLiftFn f) t
    rw [hcf, hsmul]
    change _ = c * torusLiftFn f t
    rw [hf, harg]
    ring

lemma norm_torusLiftFn (f : BoxFourierL2) : ‖torusLiftFn f‖ = ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_torusLiftFn f)]
  change (eLpNorm ((2 * Real.pi : ℂ) • ((f : R2 → ℂ) ∘ torusRep)) 2 volume).toReal = _
  rw [eLpNorm_const_smul, eLpNorm_torusRep]
  have hc : ‖(2 * Real.pi : ℂ)‖ₑ = ENNReal.ofReal (2 * Real.pi) := by
    rw [← ofReal_norm]
    congr 1
    simp [abs_of_pos Real.pi_pos]
  rw [hc, ← mul_assoc, ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top, one_mul]
  rfl

def torusLift : BoxFourierL2 →ₗᵢ[ℂ] FourierL2 where
  toLinearMap := torusLiftLinear
  norm_map' := norm_torusLiftFn

lemma memLp_torusDescend (g : FourierL2) :
    MemLp ((2 * Real.pi : ℂ)⁻¹ • ((g : UnitAddTorus (Fin 2) → ℂ) ∘ torusProj)) 2 μT := by
  have hg := (Lp.memLp g).smul_measure
    (show ENNReal.ofReal ((2 * Real.pi) ^ 2) ≠ ∞ from ENNReal.ofReal_ne_top)
  exact (hg.comp_measurePreserving measurePreserving_torusProj).const_smul _

def torusDescendFn (g : FourierL2) : BoxFourierL2 :=
  (memLp_torusDescend g).toLp _

lemma coeFn_torusDescendFn (g : FourierL2) :
    torusDescendFn g =ᵐ[μT] fun x => (2 * Real.pi : ℂ)⁻¹ * g (torusProj x) :=
  (memLp_torusDescend g).coeFn_toLp

lemma torusLift_surjective : Function.Surjective torusLift := by
  intro g
  refine ⟨torusDescendFn g, ?_⟩
  apply Lp.ext
  filter_upwards [coeFn_torusLiftFn (torusDescendFn g),
    ae_eq_comp_torusRep (coeFn_torusDescendFn g)] with t hlift hdesc
  change torusLiftFn (torusDescendFn g) t = g t
  simp only [Function.comp_def] at hdesc
  rw [hlift, hdesc, torusProj_torusRep]
  rw [← mul_assoc, mul_inv_cancel₀, one_mul]
  exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)

/-- The original non-normalized box and the normalized quotient torus
have isometric scalar `L²` spaces after multiplication by `2π`. -/
def torusL2Equiv : BoxFourierL2 ≃ₗᵢ[ℂ] FourierL2 :=
  LinearIsometryEquiv.ofSurjective torusLift torusLift_surjective

@[simp] lemma torusL2Equiv_apply (f : BoxFourierL2) : torusL2Equiv f = torusLiftFn f := rfl

/-- Fourier truncation transported to the actual fundamental square. -/
def boxScalarFourierTrunc (N : ℕ) : BoxFourierL2 →L[ℂ] BoxFourierL2 :=
  torusL2Equiv.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((fourierTrunc N).comp torusL2Equiv.toLinearIsometry.toContinuousLinearMap)

lemma boxScalarFourierTrunc_finiteDimensional_range (N : ℕ) :
    FiniteDimensional ℂ (LinearMap.range (boxScalarFourierTrunc N).toLinearMap) := by
  letI := fourierTrunc_finiteDimensional_range N
  change FiniteDimensional ℂ (LinearMap.range
    (torusL2Equiv.symm.toLinearEquiv.toLinearMap.comp
      ((fourierTrunc N).toLinearMap.comp torusL2Equiv.toLinearEquiv.toLinearMap)))
  rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _
    torusL2Equiv.toLinearEquiv.range]
  infer_instance

lemma norm_sub_boxScalarFourierTrunc (N : ℕ) (f : BoxFourierL2) :
    ‖f - boxScalarFourierTrunc N f‖ = ‖torusL2Equiv f - fourierTrunc N (torusL2Equiv f)‖ := by
  rw [← torusL2Equiv.norm_map (f - boxScalarFourierTrunc N f), map_sub]
  change ‖torusL2Equiv f - torusL2Equiv (torusL2Equiv.symm
    (fourierTrunc N (torusL2Equiv f)))‖ = _
  rw [torusL2Equiv.apply_symm_apply]

end Euler2D

end
