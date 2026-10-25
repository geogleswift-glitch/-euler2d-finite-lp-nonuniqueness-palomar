module

public import RequestProject.Euler.TorusBiotSavartKernel
public import RequestProject.Euler.BiotSavartDatum

/-!
# Physical convolution with the actual periodic velocity kernel

All integrals retain the original area measure on `[0,2π)²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff ENNReal

namespace Euler2D

lemma TorusAreaPreserving.integrable_comp {F : Type*} [NormedAddCommGroup F]
    {X : R2 → R2} (hX : TorusAreaPreserving X) {f : R2 → F}
    (hf : Integrable f μT) (hp : IsTorusPeriodic f) : Integrable (f ∘ X) μT := by
  have he : f ∘ X = f ∘ (torusWrap ∘ X) := by
    funext x
    exact (hp.eq_torusWrap (X x)).symm
  rw [he]
  exact hX.integrable_comp_of_integrable hf

def torusKernelVelocity (w : R2 → ℝ) (x : R2) : R2 :=
  ∫ y in torusBox, w y • torusBiotSavartKernel (x - y + torusCenter)

lemma integrable_torusBiotSavartKernel_sub_left (x : R2) :
    Integrable (fun y => torusBiotSavartKernel (x - y + torusCenter)) μT := by
  have he : (fun y => torusBiotSavartKernel (x - y + torusCenter)) =
      torusBiotSavartKernel ∘ (fun y => (x + torusCenter) - y) := by
    funext y
    congr 1
    abel_nf
  rw [he]
  exact (torusAreaPreserving_sub_left _).integrable_comp integrable_torusBiotSavartKernel
    isTorusPeriodic_torusBiotSavartKernel

lemma integral_norm_torusBiotSavartKernel_sub_left (x : R2) :
    (∫ y in torusBox, ‖torusBiotSavartKernel (x - y + torusCenter)‖) =
      ∫ y in torusBox, ‖torusBiotSavartKernel y‖ := by
  have hp : IsTorusPeriodic (fun y => ‖torusBiotSavartKernel y‖) :=
    fun y i => congrArg norm (isTorusPeriodic_torusBiotSavartKernel y i)
  convert (torusAreaPreserving_sub_left (x + torusCenter)).integral_comp
    integrable_torusBiotSavartKernel.norm.aestronglyMeasurable hp using 1
  congr 1
  funext y
  congr 2
  abel

lemma integrable_torusKernelVelocity_integrand {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) (x : R2) :
    Integrable (fun y => w y • torusBiotSavartKernel (x - y + torusCenter)) μT :=
  (integrable_torusBiotSavartKernel_sub_left x).bdd_smul M hw hM

theorem norm_torusKernelVelocity_le {w : R2 → ℝ} {M : ℝ}
    (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) (x : R2) :
    ‖torusKernelVelocity w x‖ ≤ M * ∫ y in torusBox, ‖torusBiotSavartKernel y‖ := by
  calc
    _ ≤ ∫ y in torusBox, M * ‖torusBiotSavartKernel (x - y + torusCenter)‖ := by
      apply norm_integral_le_of_norm_le
        ((integrable_torusBiotSavartKernel_sub_left x).norm.const_mul M)
      filter_upwards [hM] with y hy
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
    _ = _ := by rw [integral_const_mul, integral_norm_torusBiotSavartKernel_sub_left]

theorem isTorusPeriodic_torusKernelVelocity (w : R2 → ℝ) :
    IsTorusPeriodic (torusKernelVelocity w) := by
  intro x i
  unfold torusKernelVelocity
  congr 1
  funext y
  congr 1
  calc
    _ = torusBiotSavartKernel ((x - y + torusCenter) + EuclideanSpace.single i (2 * π)) := by
      congr 1
      abel
    _ = _ := isTorusPeriodic_torusBiotSavartKernel _ i

lemma measurable_torusBiotSavartKernel_prod :
    Measurable (fun p : R2 × R2 => torusBiotSavartKernel (p.1 - p.2 + torusCenter)) :=
  measurable_torusBiotSavartKernel.comp ((measurable_fst.sub measurable_snd).add measurable_const)

lemma integrable_torusBiotSavartKernel_prod :
    Integrable (fun p : R2 × R2 => torusBiotSavartKernel (p.1 - p.2 + torusCenter)) (μT.prod μT) := by
  apply (integrable_prod_iff measurable_torusBiotSavartKernel_prod.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall integrable_torusBiotSavartKernel_sub_left, ?_⟩
  apply (integrable_const (∫ y in torusBox, ‖torusBiotSavartKernel y‖)).congr
  exact Eventually.of_forall fun x => (integral_norm_torusBiotSavartKernel_sub_left x).symm

lemma integrable_torusKernelVelocity_prod {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) :
    Integrable (fun p : R2 × R2 => w p.2 •
      torusBiotSavartKernel (p.1 - p.2 + torusCenter)) (μT.prod μT) := by
  exact integrable_torusBiotSavartKernel_prod.bdd_smul M
    (hw.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    (Measure.quasiMeasurePreserving_snd.ae hM)

theorem aestronglyMeasurable_torusKernelVelocity {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) : AEStronglyMeasurable (torusKernelVelocity w) μT := by
  exact ((hw.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).smul
    measurable_torusBiotSavartKernel_prod.aestronglyMeasurable).integral_prod_right'

theorem memLp_torusKernelVelocity {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) (q : ENNReal) :
    MemLp (torusKernelVelocity w) q μT :=
  MemLp.of_bound (aestronglyMeasurable_torusKernelVelocity hw)
    (M * ∫ y in torusBox, ‖torusBiotSavartKernel y‖)
    (Eventually.of_forall (norm_torusKernelVelocity_le hM))

lemma isScalarTest_translate {ψ : R2 → ℝ} (hψ : IsScalarTest ψ) (a : R2) :
    IsScalarTest (fun x => ψ (x + a)) := by
  refine ⟨hψ.1.comp (contDiff_id.add contDiff_const), ?_⟩
  intro x i
  change ψ (x + EuclideanSpace.single i (2 * π) + a) = ψ (x + a)
  convert hψ.2 (x + a) i using 2
  abel

lemma torusBiotSavartKernel_shift_weak_curl {ψ : R2 → ℝ} (hψ : IsScalarTest ψ) (y : R2) :
    (∫ x in torusBox, torusBiotSavartKernel (x - y + torusCenter) 0 * pd 1 ψ x -
      torusBiotSavartKernel (x - y + torusCenter) 1 * pd 0 ψ x) =
      ψ y - ((2 * π) ^ 2)⁻¹ * ∫ x in torusBox, ψ x := by
  let φ := fun x => ψ (x + (y - torusCenter))
  have hφ : IsScalarTest φ := isScalarTest_translate hψ _
  let F := fun x => torusBiotSavartKernel x 0 * pd 1 φ x -
    torusBiotSavartKernel x 1 * pd 0 φ x
  have hF : IsTorusPeriodic F := by
    intro x i
    simp only [F, isTorusPeriodic_torusBiotSavartKernel x i,
      isTorusPeriodic_pd hφ.2 1 x i, isTorusPeriodic_pd hφ.2 0 x i]
  have hFm : AEStronglyMeasurable F μT := by
    have hK (j : Fin 2) := (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.measurable.comp
      measurable_torusBiotSavartKernel
    exact (((hK 0).mul (contDiff_pd_infty hφ.1 1).continuous.measurable).sub
      ((hK 1).mul (contDiff_pd_infty hφ.1 0).continuous.measurable)).aestronglyMeasurable
  have hchange := (torusAreaPreserving_add_right (torusCenter - y)).integral_comp hFm hF
  have he : (∫ x in torusBox, torusBiotSavartKernel (x - y + torusCenter) 0 * pd 1 ψ x -
      torusBiotSavartKernel (x - y + torusCenter) 1 * pd 0 ψ x) = ∫ x in torusBox, F x := by
    rw [← hchange]
    congr 1
    funext x
    dsimp only [F, φ]
    rw [pd_comp_add_const, pd_comp_add_const]
    have ha : x + (torusCenter - y) + (y - torusCenter) = x := by abel
    have hb : x - y + torusCenter = x + (torusCenter - y) := by abel
    rw [ha, hb]
  rw [he]
  change (∫ x in torusBox, torusBiotSavartKernel x 0 * pd 1 φ x -
    torusBiotSavartKernel x 1 * pd 0 φ x) = _
  rw [torusBiotSavartKernel_weak_curl hφ]
  have hi := (torusAreaPreserving_add_right (y - torusCenter)).integral_comp
    hψ.1.continuous.aestronglyMeasurable hψ.2
  dsimp only [φ]
  rw [hi]
  congr 1
  congr 1
  abel

lemma torusBiotSavartKernel_shift_weak_divergence {ψ : R2 → ℝ}
    (hψ : IsScalarTest ψ) (y : R2) :
    (∫ x in torusBox, ∑ i : Fin 2,
      torusBiotSavartKernel (x - y + torusCenter) i * pd i ψ x) = 0 := by
  let φ := fun x => ψ (x + (y - torusCenter))
  have hφ : IsScalarTest φ := isScalarTest_translate hψ _
  let F := fun x => ∑ i : Fin 2, torusBiotSavartKernel x i * pd i φ x
  have hF : IsTorusPeriodic F := by
    intro x i
    simp only [F, isTorusPeriodic_torusBiotSavartKernel x i,
      fun j => isTorusPeriodic_pd hφ.2 j x i]
  have hFm : AEStronglyMeasurable F μT := by
    have hm (i : Fin 2) : AEStronglyMeasurable
        (fun x => torusBiotSavartKernel x i * pd i φ x) μT :=
      (((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.measurable.comp
        measurable_torusBiotSavartKernel).mul
          (contDiff_pd_infty hφ.1 i).continuous.measurable).aestronglyMeasurable
    simpa only [F, Fin.sum_univ_two] using (hm 0).add (hm 1)
  have hchange := (torusAreaPreserving_add_right (torusCenter - y)).integral_comp hFm hF
  calc
    _ = ∫ x in torusBox, F (x + (torusCenter - y)) := by
      congr 1
      funext x
      dsimp only [F, φ]
      simp only [pd_comp_add_const]
      have ha : x + (torusCenter - y) + (y - torusCenter) = x := by abel
      have hb : x - y + torusCenter = x + (torusCenter - y) := by abel
      rw [ha, hb]
    _ = ∫ x in torusBox, F x := hchange
    _ = 0 := divFree_torusBiotSavartKernel φ hφ

lemma integral_torusBiotSavartKernel_shift (y : R2) :
    (∫ x in torusBox, torusBiotSavartKernel (x - y + torusCenter)) = 0 := by
  have he := (torusAreaPreserving_add_right (torusCenter - y)).integral_comp
    integrable_torusBiotSavartKernel.aestronglyMeasurable isTorusPeriodic_torusBiotSavartKernel
  calc
    _ = ∫ x in torusBox, torusBiotSavartKernel (x + (torusCenter - y)) := by
      congr 1
      funext x
      congr 1
      abel
    _ = _ := he.trans integral_torusBiotSavartKernel

lemma integrable_torusKernel_pair_prod {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M)
    {f : R2 → ℝ} (hf : Continuous f) (j : Fin 2) :
    Integrable (fun p : R2 × R2 => w p.2 *
      torusBiotSavartKernel (p.1 - p.2 + torusCenter) j * f p.1) (μT.prod μT) := by
  have hv := integrable_torusKernelVelocity_prod hw hM
  have hc : Integrable (fun p : R2 × R2 =>
      (w p.2 • torusBiotSavartKernel (p.1 - p.2 + torusCenter)) j) (μT.prod μT) := by
    apply hv.norm.mono'
      ((EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hv.aestronglyMeasurable)
    exact Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using abs_coord_le
        (w p.2 • torusBiotSavartKernel (p.1 - p.2 + torusCenter)) j
  obtain ⟨C, hC⟩ := bound_on_box hf
  have hb : ∀ᵐ x ∂μT, ‖f x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
    simpa only [Real.norm_eq_abs] using hC x hx
  simpa only [PiLp.smul_apply, smul_eq_mul] using
    hc.mul_bdd (hf.measurable.comp measurable_fst).aestronglyMeasurable
      (Measure.quasiMeasurePreserving_fst.ae hb)

lemma torusKernelVelocity_coord {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M)
    (x : R2) (j : Fin 2) :
    torusKernelVelocity w x j =
      ∫ y in torusBox, w y * torusBiotSavartKernel (x - y + torusCenter) j := by
  have he := (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).integral_comp_comm
    (integrable_torusKernelVelocity_integrand hw hM x)
  exact he.symm

theorem isCurl_torusKernelVelocity {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M)
    (hmean : (∫ y in torusBox, w y) = 0) : IsCurl (torusKernelVelocity w) w := by
  intro ψ hψ
  have hp (i : Fin 2) : Continuous (pd i ψ) := (contDiff_pd_infty hψ.1 i).continuous
  let F := fun x y => w y * torusBiotSavartKernel (x - y + torusCenter) 0 * pd 1 ψ x -
    w y * torusBiotSavartKernel (x - y + torusCenter) 1 * pd 0 ψ x
  have hF : Integrable (Function.uncurry F) (μT.prod μT) :=
    (integrable_torusKernel_pair_prod hw hM (hp 1) 0).sub
      (integrable_torusKernel_pair_prod hw hM (hp 0) 1)
  have hinner (x : R2) :
      torusKernelVelocity w x 0 * pd 1 ψ x - torusKernelVelocity w x 1 * pd 0 ψ x =
        ∫ y in torusBox, F x y := by
    have hi := integrable_torusKernelVelocity_integrand hw hM x
    have hj (j : Fin 2) := integrable_coord_of_integrable hi j
    rw [torusKernelVelocity_coord hw hM x 0, torusKernelVelocity_coord hw hM x 1]
    rw [← integral_mul_const, ← integral_mul_const]
    symm
    exact integral_sub ((hj 0).mul_const _) ((hj 1).mul_const _)
  have hout (y : R2) : (∫ x in torusBox, F x y) =
      w y * (ψ y - ((2 * π) ^ 2)⁻¹ * ∫ x in torusBox, ψ x) := by
    calc
      _ = ∫ x in torusBox, w y * (torusBiotSavartKernel (x - y + torusCenter) 0 * pd 1 ψ x -
          torusBiotSavartKernel (x - y + torusCenter) 1 * pd 0 ψ x) := by
        congr 1
        funext x
        dsimp only [F]
        ring
      _ = _ := by rw [integral_const_mul, torusBiotSavartKernel_shift_weak_curl hψ]
  have hwI : Integrable w μT := Integrable.of_bound hw M hM
  have hψI : Integrable (fun x => w x * ψ x) μT := by
    obtain ⟨C, hC⟩ := bound_on_box hψ.1.continuous
    apply hwI.mul_bdd hψ.1.continuous.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
    simpa only [Real.norm_eq_abs] using hC x hx
  symm
  calc
    _ = ∫ x in torusBox, ∫ y in torusBox, F x y := by simp_rw [hinner]
    _ = ∫ y in torusBox, ∫ x in torusBox, F x y := integral_integral_swap hF
    _ = ∫ y in torusBox, w y * (ψ y - ((2 * π) ^ 2)⁻¹ * ∫ x in torusBox, ψ x) := by
      simp_rw [hout]
    _ = _ := by
      simp_rw [mul_sub]
      rw [integral_sub hψI (hwI.mul_const _), integral_mul_const, hmean, zero_mul, sub_zero]

theorem integral_torusKernelVelocity {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) :
    (∫ x in torusBox, torusKernelVelocity w x) = 0 := by
  change (∫ x in torusBox, ∫ y in torusBox,
    w y • torusBiotSavartKernel (x - y + torusCenter)) = 0
  rw [integral_integral_swap (integrable_torusKernelVelocity_prod hw hM)]
  simp_rw [integral_smul, integral_torusBiotSavartKernel_shift, smul_zero, integral_zero]

theorem divFree_torusKernelVelocity {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) {M : ℝ} (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) :
    DivFree (torusKernelVelocity w) := by
  intro ψ hψ
  have hp (i : Fin 2) : Continuous (pd i ψ) := (contDiff_pd_infty hψ.1 i).continuous
  let F := fun x y => ∑ i : Fin 2,
    w y * torusBiotSavartKernel (x - y + torusCenter) i * pd i ψ x
  have hF : Integrable (Function.uncurry F) (μT.prod μT) :=
    integrable_finset_sum _ (fun i _ => integrable_torusKernel_pair_prod hw hM (hp i) i)
  have hinner (x : R2) : (∑ i : Fin 2, torusKernelVelocity w x i * pd i ψ x) =
      ∫ y in torusBox, F x y := by
    have hi := integrable_torusKernelVelocity_integrand hw hM x
    have hj (j : Fin 2) : Integrable (fun y => w y *
        torusBiotSavartKernel (x - y + torusCenter) j) μT := by
      simpa only [PiLp.smul_apply, smul_eq_mul] using integrable_coord_of_integrable hi j
    dsimp only [F]
    rw [integral_finset_sum _ (fun i _ => (hj i).mul_const (pd i ψ x))]
    apply Finset.sum_congr rfl
    intro i _
    rw [torusKernelVelocity_coord hw hM x i, integral_mul_const]
  calc
    _ = ∫ x in torusBox, ∫ y in torusBox, F x y := by simp_rw [hinner]
    _ = ∫ y in torusBox, ∫ x in torusBox, F x y := integral_integral_swap hF
    _ = 0 := by
      have hout (y : R2) : (∫ x in torusBox, F x y) = 0 := by
        calc
          _ = ∫ x in torusBox, w y * (∑ i : Fin 2,
              torusBiotSavartKernel (x - y + torusCenter) i * pd i ψ x) := by
            congr 1
            funext x
            simp only [F, Finset.mul_sum, mul_assoc]
          _ = 0 := by rw [integral_const_mul, torusBiotSavartKernel_shift_weak_divergence hψ, mul_zero]
      simp_rw [hout, integral_zero]

/-- The physical integral construction agrees with the independently
constructed Fourier inverse curl. -/
theorem torusKernelVelocity_eq_biotSavartL2_ae (w : Lp ℝ 2 μT) {M : ℝ}
    (hM : ∀ᵐ y ∂μT, ‖w y‖ ≤ M) (hmean : (∫ y in torusBox, w y) = 0) :
    torusKernelVelocity w =ᵐ[μT] biotSavartL2 w := by
  have hw := (Lp.memLp w).aestronglyMeasurable
  have hm := memLp_torusKernelVelocity hw hM 2
  let u : L2T := hm.toLp (torusKernelVelocity w)
  have hu : (u : R2 → R2) =ᵐ[μT] torusKernelVelocity w := hm.coeFn_toLp
  have hd : DivFree u := (divFree_torusKernelVelocity hw hM).congr_ae hu.symm
  have hc : IsCurl u w := (isCurl_torusKernelVelocity hw hM hmean).congr_ae
    hu.symm (EventuallyEq.rfl)
  have hzero : (∫ x in torusBox, u x) = 0 :=
    (integral_congr_ae hu).trans (integral_torusKernelVelocity hw hM)
  have he : biotSavartL2 w = u := biotSavartL2_eq_of_div_curl hd hc hzero
  rw [he]
  exact hu.symm

end Euler2D

end

