module

public import RequestProject.Euler.FourierTruncation

/-!
# The fundamental square and the normalized quotient torus

The original Euler model integrates on `[0,2π)²`; the Fourier model uses
probability Haar measure on `(ℝ/ℤ)²`. The maps here retain the actual
normalization factor `(2π)²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped ENNReal

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Projection from the original coordinates to the unit quotient torus. -/
def torusProj (x : R2) : UnitAddTorus (Fin 2) :=
  fun i => ((x i / (2 * π) : ℝ) : UnitAddCircle)

/-- The actual representative of the quotient torus in the fundamental square. -/
def torusRep (t : UnitAddTorus (Fin 2)) : R2 :=
  WithLp.toLp 2 (fun i => (2 * π) * ((AddCircle.equivIco 1 0 (t i) : ℝ)))

lemma measurable_torusProj : Measurable torusProj := by
  apply measurable_pi_lambda
  intro i
  exact AddCircle.measurable_mk'.comp
    (((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.measurable).div_const _)

lemma measurable_torusRep : Measurable torusRep := by
  apply (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.comp
  apply measurable_pi_lambda
  intro i
  have hrep : Measurable (fun t : UnitAddCircle => (AddCircle.equivIco 1 0 t : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  exact (hrep.comp (measurable_pi_apply i)).const_mul _

lemma torusRep_mem (t : UnitAddTorus (Fin 2)) : torusRep t ∈ torusBox := by
  intro i
  have hi := (AddCircle.equivIco 1 0 (t i)).property
  change 0 ≤ 2 * π * _ ∧ 2 * π * _ < 2 * π
  constructor
  · exact mul_nonneg (by positivity) hi.1
  · simpa using mul_lt_mul_of_pos_left hi.2 (by positivity : (0 : ℝ) < 2 * π)

lemma torusProj_torusRep (t : UnitAddTorus (Fin 2)) : torusProj (torusRep t) = t := by
  funext i
  change (((2 * π) * ((AddCircle.equivIco 1 0 (t i) : ℝ)) / (2 * π) : ℝ) :
    UnitAddCircle) = t i
  rw [mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0)]
  exact (AddCircle.equivIco 1 0).symm_apply_apply (t i)

lemma torusRep_torusProj {x : R2} (hx : x ∈ torusBox) : torusRep (torusProj x) = x := by
  ext i
  have hi : x i / (2 * π) ∈ Ico (0 : ℝ) (0 + 1) :=
    ⟨div_nonneg (hx i).1 (by positivity), by
      simpa using (div_lt_one (by positivity : (0 : ℝ) < 2 * π)).mpr (hx i).2⟩
  change (2 * π) * ((AddCircle.equivIco 1 0 ((x i / (2 * π) : ℝ) : UnitAddCircle) : ℝ)) = x i
  rw [AddCircle.equivIco_coe_eq hi]
  change (2 * π) * (x i / (2 * π)) = x i
  field_simp

lemma torusRep_torusProj_ae : (fun x => torusRep (torusProj x)) =ᵐ[μT] id := by
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
  exact torusRep_torusProj hx

/-- The unit fundamental square in Euclidean coordinates. -/
def unitBox : Set R2 := {x | ∀ i, x i ∈ Ico (0 : ℝ) 1}

lemma measurableSet_unitBox : MeasurableSet unitBox := by
  simp only [unitBox, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => measurableSet_Ico.preimage
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.measurable

/-- Unit projection before the physical coordinate rescaling. -/
def unitTorusProj (x : R2) : UnitAddTorus (Fin 2) := fun i => ((x i : ℝ) : UnitAddCircle)

lemma measurePreserving_unitTorusProj :
    MeasurePreserving unitTorusProj (volume.restrict unitBox) volume := by
  let B : Set (Fin 2 → ℝ) := Set.univ.pi (fun _ => Ico (0 : ℝ) 1)
  have ho := (PiLp.volume_preserving_ofLp (ι := Fin 2)).restrict_preimage
    (show MeasurableSet B from MeasurableSet.univ_pi fun _ => measurableSet_Ico)
  have hB : (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' B = unitBox := by
    ext x
    simp [B, unitBox]
  rw [hB] at ho
  have hprod : (volume : Measure (Fin 2 → ℝ)).restrict B =
      Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hm : MeasurePreserving ((↑) : ℝ → UnitAddCircle)
      ((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)) volume := by
    have hi : (volume : Measure ℝ).restrict (Ico (0 : ℝ) 1) =
        volume.restrict (Ioc (0 : ℝ) 1) :=
      Measure.restrict_congr_set (Ico_ae_eq_Icc.trans Ioc_ae_eq_Icc.symm)
    rw [hi]
    have hm0 := UnitAddCircle.measurePreserving_mk 0
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul] at hm0
    simpa only [instMeasureSpaceUnitAddCircle, volume, zero_add] using hm0
  have hp := measurePreserving_pi
    (fun _ : Fin 2 => (volume : Measure ℝ).restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 2 => (volume : Measure UnitAddCircle)) (fun _ => hm)
  rw [← hprod] at hp
  exact hp.comp ho


/-- The physical square is exactly the preimage of the unit square under dilation. -/
lemma torusNormalize_preimage :
    (fun x : R2 => (2 * π)⁻¹ • x) ⁻¹' unitBox = torusBox := by
  ext x
  change (∀ i, (2 * π)⁻¹ * x i ∈ Ico (0 : ℝ) 1) ↔
    ∀ i, x i ∈ Ico (0 : ℝ) (2 * π)
  have hL : (0 : ℝ) < 2 * π := by positivity
  constructor
  · intro h i
    have h0 := mul_le_mul_of_nonneg_left (h i).1 hL.le
    have h1 := mul_lt_mul_of_pos_left (h i).2 hL
    simpa only [Set.mem_Ico, mul_zero, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul, mul_one]
      using And.intro h0 h1
  · intro h i
    have h0 := mul_le_mul_of_nonneg_left (h i).1 (inv_pos.mpr hL).le
    have h1 := mul_lt_mul_of_pos_left (h i).2 (inv_pos.mpr hL)
    simpa only [Set.mem_Ico, mul_zero, inv_mul_cancel₀ hL.ne'] using And.intro h0 h1

/-- The actual change-of-variables formula for the fundamental square. -/
lemma map_torusNormalize :
    Measure.map (fun x : R2 => (2 * π)⁻¹ • x) μT =
      ENNReal.ofReal ((2 * π) ^ 2) • (volume.restrict unitBox) := by
  change Measure.map _ (volume.restrict torusBox) = _
  rw [← torusNormalize_preimage,
    ← Measure.restrict_map (by fun_prop : Measurable (fun x : R2 => (2 * π)⁻¹ • x))
      measurableSet_unitBox,
    Measure.map_addHaar_smul volume (inv_ne_zero (by positivity : (2 * π : ℝ) ≠ 0))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, inv_pow, inv_inv,
    abs_of_nonneg (sq_nonneg (2 * π)), Measure.restrict_smul]

/-- The normalization between the two actual torus measures is `(2π)²`. -/
lemma measurePreserving_torusProj : MeasurePreserving torusProj μT
    (ENNReal.ofReal ((2 * π) ^ 2) • (volume : Measure (UnitAddTorus (Fin 2)))) := by
  refine ⟨measurable_torusProj, ?_⟩
  have heq : torusProj = unitTorusProj ∘ (fun x : R2 => (2 * π)⁻¹ • x) := by
    funext x i
    change ((x i / (2 * π) : ℝ) : UnitAddCircle) =
      (((2 * π)⁻¹ * x i : ℝ) : UnitAddCircle)
    congr 1
    ring
  rw [heq, ← Measure.map_map measurePreserving_unitTorusProj.measurable
    (by fun_prop : Measurable (fun x : R2 => (2 * π)⁻¹ • x)),
    map_torusNormalize,
    Measure.map_smul _ measurePreserving_unitTorusProj.aemeasurable,
    measurePreserving_unitTorusProj.map_eq]

/-- Representatives send normalized Haar measure to normalized box measure. -/
lemma map_torusRep :
    Measure.map torusRep (volume : Measure (UnitAddTorus (Fin 2))) =
      (ENNReal.ofReal ((2 * π) ^ 2))⁻¹ • μT := by
  have hc0 : ENNReal.ofReal ((2 * π) ^ 2) ≠ 0 := by positivity
  have hct : ENNReal.ofReal ((2 * π) ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hid : Measure.map (torusRep ∘ torusProj) μT = μT := by
    change Measure.map (fun x => torusRep (torusProj x)) μT = μT
    rw [Measure.map_congr torusRep_torusProj_ae, Measure.map_id]
  have hscalar : ENNReal.ofReal ((2 * π) ^ 2) •
      Measure.map torusRep (volume : Measure (UnitAddTorus (Fin 2))) = μT := by
    rw [← Measure.map_smul _ measurable_torusRep.aemeasurable,
      ← measurePreserving_torusProj.map_eq,
      Measure.map_map measurable_torusRep measurable_torusProj]
    exact hid
  calc
    Measure.map torusRep volume = (ENNReal.ofReal ((2 * π) ^ 2))⁻¹ •
        (ENNReal.ofReal ((2 * π) ^ 2) • Measure.map torusRep volume) := by
      rw [smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]
    _ = (ENNReal.ofReal ((2 * π) ^ 2))⁻¹ • μT := by rw [hscalar]

lemma measurePreserving_torusRep : MeasurePreserving torusRep
    (volume : Measure (UnitAddTorus (Fin 2))) ((ENNReal.ofReal ((2 * π) ^ 2))⁻¹ • μT) :=
  ⟨measurable_torusRep, map_torusRep⟩



lemma range_torusRep : Set.range torusRep = torusBox := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    exact torusRep_mem t
  · intro x hx
    exact ⟨torusProj x, torusRep_torusProj hx⟩

lemma measurableEmbedding_torusRep : MeasurableEmbedding torusRep :=
  MeasurableEmbedding.of_measurable_inverse measurable_torusRep
    (by rw [range_torusRep]; exact measurableSet_torusBox) measurable_torusProj
    torusProj_torusRep

/-- Exact integral normalization, valid for every representative function. -/
lemma integral_torusRep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : R2 → E) :
    ∫ t : UnitAddTorus (Fin 2), f (torusRep t) =
      ((2 * π) ^ 2)⁻¹ • ∫ x, f x ∂μT := by
  rw [measurePreserving_torusRep.integral_comp measurableEmbedding_torusRep,
    integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (sq_nonneg (2 * π))]

/-- Integral normalization in the projection direction. -/
lemma integral_torusProj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddTorus (Fin 2) → E)
    (hf : AEStronglyMeasurable f (volume : Measure (UnitAddTorus (Fin 2)))) :
    ∫ x, f (torusProj x) ∂μT = (2 * π) ^ 2 • ∫ t, f t := by
  have hfm : AEStronglyMeasurable f (Measure.map torusProj μT) := by
    rw [measurePreserving_torusProj.map_eq]
    exact hf.smul_measure _
  rw [← integral_map measurable_torusProj.aemeasurable hfm,
    measurePreserving_torusProj.map_eq, integral_smul_measure,
    ENNReal.toReal_ofReal (sq_nonneg (2 * π))]

private lemma torusMeasure_sqrt :
    (ENNReal.ofReal ((2 * π) ^ 2)) ^ (1 / (2 : ENNReal)).toReal =
      ENNReal.ofReal (2 * π) := by
  have hL : (0 : ℝ) < 2 * π := by positivity
  simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [ENNReal.ofReal_rpow_of_pos (sq_pos_of_pos hL)]
  congr 1
  rw [← Real.rpow_natCast_mul hL.le]
  norm_num

/-- The representative change of variables for every finite `L^p` seminorm. -/
lemma eLpNorm_torusRep_general {E : Type*} [NormedAddCommGroup E]
    (f : R2 → E) (p : ENNReal) (hp : p ≠ ⊤) :
    eLpNorm (f ∘ torusRep) p (volume : Measure (UnitAddTorus (Fin 2))) =
      (ENNReal.ofReal ((2 * π) ^ 2))⁻¹ ^ (1 / p).toReal * eLpNorm f p μT := by
  have hc : (ENNReal.ofReal ((2 * π) ^ 2))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  rw [← measurableEmbedding_torusRep.eLpNorm_map_measure, map_torusRep]
  simpa only [smul_eq_mul] using eLpNorm_smul_measure_of_ne_zero hc f p μT

/-- The factor for `L²` is exactly `(2π)⁻¹`. -/
lemma eLpNorm_torusRep {E : Type*} [NormedAddCommGroup E] (f : R2 → E) :
    eLpNorm (f ∘ torusRep) 2 (volume : Measure (UnitAddTorus (Fin 2))) =
      (ENNReal.ofReal (2 * π))⁻¹ * eLpNorm f 2 μT := by
  rw [eLpNorm_torusRep_general f 2 (by norm_num), ENNReal.inv_rpow, torusMeasure_sqrt]

/-- Projection changes the `L²` norm by the physical side length `2π`. -/
lemma eLpNorm_torusProj {E : Type*} [NormedAddCommGroup E]
    (f : UnitAddTorus (Fin 2) → E)
    (hf : AEStronglyMeasurable f (volume : Measure (UnitAddTorus (Fin 2)))) :
    eLpNorm (f ∘ torusProj) 2 μT =
      ENNReal.ofReal (2 * π) * eLpNorm f 2 (volume : Measure (UnitAddTorus (Fin 2))) := by
  have hfm : AEStronglyMeasurable f (Measure.map torusProj μT) := by
    rw [measurePreserving_torusProj.map_eq]
    exact hf.smul_measure _
  rw [← eLpNorm_map_measure hfm measurable_torusProj.aemeasurable,
    measurePreserving_torusProj.map_eq,
    eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) f _ hf]
  simp only [smul_eq_mul, torusMeasure_sqrt]



/-- Quotient Fourier characters are the actual physical trigonometric modes. -/
lemma mFourier_torusProj (k : Fin 2 → ℤ) (x : R2) :
    UnitAddTorus.mFourier k (torusProj x) =
      Complex.exp (Complex.I * (boxFourierPhase k x : ℂ)) := by
  change (∏ i : Fin 2, fourier (k i) ((x i / (2 * π) : ℝ) : UnitAddCircle)) = _
  simp only [fourier_coe_apply]
  rw [← Complex.exp_sum, boxFourierPhase_apply]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

lemma mFourier_torusProj_re (k : Fin 2 → ℤ) (x : R2) :
    (UnitAddTorus.mFourier k (torusProj x)).re = Real.cos (boxFourierPhase k x) := by
  rw [mFourier_torusProj]
  simp [Complex.exp_re]

lemma mFourier_torusProj_im (k : Fin 2 → ℤ) (x : R2) :
    (UnitAddTorus.mFourier k (torusProj x)).im = Real.sin (boxFourierPhase k x) := by
  rw [mFourier_torusProj]
  simp [Complex.exp_im]



/-- The original real/imaginary coefficients equal the physical character integral. -/
lemma integral_boxFourier_character {f : R2 → ℝ} (hf : Integrable f μT)
    (k : Fin 2 → ℤ) :
    (∫ x, UnitAddTorus.mFourier (-k) (torusProj x) * (f x : ℂ) ∂μT) =
      boxFourierCoeff f k := by
  have hm : AEStronglyMeasurable
      (fun x => UnitAddTorus.mFourier (-k) (torusProj x)) μT :=
    ((UnitAddTorus.mFourier (-k)).continuous.measurable.comp measurable_torusProj).aestronglyMeasurable
  have hI : Integrable
      (fun x => UnitAddTorus.mFourier (-k) (torusProj x) * (f x : ℂ)) μT := by
    apply (hf.ofReal : Integrable (fun x => (f x : ℂ)) μT).bdd_mul hm
    apply Filter.Eventually.of_forall
    intro x
    exact ((UnitAddTorus.mFourier (-k)).norm_coe_le_norm _).trans_eq
      (UnitAddTorus.mFourier_norm (n := -k))
  have hn (x : R2) : boxFourierPhase (-k) x = -boxFourierPhase k x := by
    simp [boxFourierPhase_apply, Finset.sum_neg_distrib]
  apply Complex.ext
  · change RCLike.re (∫ x, UnitAddTorus.mFourier (-k) (torusProj x) * (f x : ℂ) ∂μT) = _
    rw [← integral_re hI]
    change (∫ x, (UnitAddTorus.mFourier (-k) (torusProj x) * (f x : ℂ)).re ∂μT) = _
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (UnitAddTorus.mFourier (-k) (torusProj x) * (f x : ℂ)).re =
        f x * Real.cos (boxFourierPhase k x)
      simp [Complex.mul_re, mFourier_torusProj_re, hn, mul_comm]
  · change RCLike.im (∫ x, UnitAddTorus.mFourier (-k) (torusProj x) * (f x : ℂ) ∂μT) = _
    rw [← integral_im hI]
    change (∫ x, (UnitAddTorus.mFourier (-k) (torusProj x) * (f x : ℂ)).im ∂μT) =
      -(∫ x, f x * Real.sin (boxFourierPhase k x) ∂μT)
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp [Complex.mul_im, mFourier_torusProj_im, hn, mul_comm]

/-- The exact coefficient normalization between the physical box and quotient. -/
lemma mFourierCoeff_torusRep {f : R2 → ℝ} (hf : Integrable f μT)
    (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun t => (f (torusRep t) : ℂ)) k =
      (((2 * π) ^ 2)⁻¹ : ℝ) • boxFourierCoeff f k := by
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  calc
    (∫ t, UnitAddTorus.mFourier (-k) t * (f (torusRep t) : ℂ)) =
        ∫ t, (fun x => UnitAddTorus.mFourier (-k) (torusProj x) * (f x : ℂ)) (torusRep t) := by
      congr 1
      funext t
      change UnitAddTorus.mFourier (-k) t * (f (torusRep t) : ℂ) =
        UnitAddTorus.mFourier (-k) (torusProj (torusRep t)) * (f (torusRep t) : ℂ)
      rw [torusProj_torusRep]
    _ = (((2 * π) ^ 2)⁻¹ : ℝ) •
        ∫ x, UnitAddTorus.mFourier (-k) (torusProj x) * (f x : ℂ) ∂μT := integral_torusRep (E := ℂ)
          (fun x => UnitAddTorus.mFourier (-k) (torusProj x) * (f x : ℂ))
    _ = _ := by rw [integral_boxFourier_character hf k]


end Euler2D

end











