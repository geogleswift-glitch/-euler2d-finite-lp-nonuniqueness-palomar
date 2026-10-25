module

public import RequestProject.Euler.Delay

/-!
# Periodic integration by parts and smooth stationary Euler fields

The integration domain is the actual Euclidean fundamental square
`[0,2π)²` used by `μT`. Coordinate Fubini and the fundamental theorem of
calculus remove the periodic boundary terms.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Euler2D

/-- A point of the Euclidean plane specified by its two real coordinates. -/
def torusVec (a b : ℝ) : R2 := WithLp.toLp 2 ![a, b]

@[simp] theorem torusVec_apply_zero (a b : ℝ) : torusVec a b 0 = a := rfl
@[simp] theorem torusVec_apply_one (a b : ℝ) : torusVec a b 1 = b := rfl

lemma continuous_torusVec : Continuous (fun p : ℝ × ℝ => torusVec p.1 p.2) := by
  unfold torusVec
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    (show Continuous (fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ)) from
      continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop)

/-- Fubini on the half-open fundamental square, first coordinate outside. -/
lemma integral_torusBox (G : R2 → ℝ) (hG : Continuous G) :
    ∫ x in torusBox, G x =
      ∫ a in (0 : ℝ)..(2 * Real.pi), ∫ b in (0 : ℝ)..(2 * Real.pi), G (torusVec a b) := by
  let e : R2 ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.finTwoArrow (α := ℝ))
  have hmp : MeasurePreserving e volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  have hset : torusBox = e ⁻¹' (Ico (0 : ℝ) (2 * Real.pi) ×ˢ Ico (0 : ℝ) (2 * Real.pi)) := by
    ext x
    simp [torusBox, e, MeasurableEquiv.finTwoArrow_apply, Fin.forall_fin_two]
  have hsymm (p : ℝ × ℝ) : e.symm p = torusVec p.1 p.2 := by
    ext i
    fin_cases i <;> rfl
  have hc : Continuous (fun p : ℝ × ℝ => G (e.symm p)) := by
    simp_rw [hsymm]
    exact hG.comp continuous_torusVec
  have hI : IntegrableOn (fun p : ℝ × ℝ => G (e.symm p))
      (Ico (0 : ℝ) (2 * Real.pi) ×ˢ Ico (0 : ℝ) (2 * Real.pi)) :=
    (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
  have key := hmp.setIntegral_preimage_emb e.measurableEmbedding (fun p => G (e.symm p))
    (Ico (0 : ℝ) (2 * Real.pi) ×ˢ Ico (0 : ℝ) (2 * Real.pi))
  simp only [MeasurableEquiv.symm_apply_apply] at key
  rw [hset, key, Measure.volume_eq_prod, setIntegral_prod _ hI]
  have hτ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [intervalIntegral.integral_of_le hτ]
  rw [setIntegral_congr_set (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 2 * Real.pi))]
  refine setIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
  rw [intervalIntegral.integral_of_le hτ]
  rw [setIntegral_congr_set (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 2 * Real.pi))]
  simp only [hsymm]

/-- Fubini on the fundamental square, second coordinate outside. -/
lemma integral_torusBox_swap (G : R2 → ℝ) (hG : Continuous G) :
    ∫ x in torusBox, G x =
      ∫ b in (0 : ℝ)..(2 * Real.pi), ∫ a in (0 : ℝ)..(2 * Real.pi), G (torusVec a b) := by
  rw [integral_torusBox G hG]
  have hτ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  simp only [intervalIntegral.integral_of_le hτ]
  apply integral_integral_swap
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact ((hG.comp continuous_torusVec).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

lemma continuous_pd_of_contDiff_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : R2 → F) (hh : ContDiff ℝ 1 h) (i : Fin 2) : Continuous (pd i h) :=
  (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The derivative along a coordinate line is the corresponding `pd`. -/
lemma hasDerivAt_coordinate_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : R2 → F) (x : R2) (i : Fin 2) (r : ℝ)
    (hd : DifferentiableAt ℝ h (x + r • EuclideanSpace.single i 1)) :
    HasDerivAt (fun s : ℝ => h (x + s • EuclideanSpace.single i 1))
      (pd i h (x + r • EuclideanSpace.single i 1)) r := by
  have hl : HasDerivAt (fun s : ℝ => x + s • EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) r := by
    simpa using ((hasDerivAt_id r).smul_const (EuclideanSpace.single i 1)).const_add x
  exact hd.hasFDerivAt.comp_hasDerivAt r hl

lemma integral_pd_coordinate_line (h : R2 → ℝ) (hh : ContDiff ℝ 1 h)
    (hp : IsTorusPeriodic h) (i : Fin 2) (x : R2) :
    ∫ r in (0 : ℝ)..(2 * Real.pi), pd i h (x + r • EuclideanSpace.single i 1) = 0 := by
  have hc : Continuous (fun r : ℝ => pd i h (x + r • EuclideanSpace.single i 1)) :=
    (continuous_pd_of_contDiff_one h hh i).comp (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_coordinate_line h x i r (hh.differentiable one_ne_zero _))
    (hc.intervalIntegrable _ _)]
  have hsingle : (2 * Real.pi) • EuclideanSpace.single i (1 : ℝ) =
      EuclideanSpace.single i (2 * Real.pi) := by
    ext j
    simp [EuclideanSpace.single_apply]
  simp only [zero_smul, add_zero]
  rw [hsingle, hp, sub_self]

/-- The integral of each partial derivative of a periodic `C¹` scalar
function over the actual fundamental square is zero. -/
lemma integral_pd_eq_zero (h : R2 → ℝ) (hh : ContDiff ℝ 1 h)
    (hp : IsTorusPeriodic h) (i : Fin 2) :
    ∫ x in torusBox, pd i h x = 0 := by
  have hc := continuous_pd_of_contDiff_one h hh i
  fin_cases i
  · rw [integral_torusBox_swap _ hc]
    have hline (b : ℝ) : ∫ a in (0 : ℝ)..(2 * Real.pi), pd 0 h (torusVec a b) = 0 := by
      have heq (a : ℝ) : torusVec a b = torusVec 0 b + a • EuclideanSpace.single 0 1 := by
        ext j
        fin_cases j <;> simp [torusVec, EuclideanSpace.single_apply]
      rw [show (fun a => pd 0 h (torusVec a b)) =
        (fun a => pd 0 h (torusVec 0 b + a • EuclideanSpace.single 0 1)) from
          funext fun a => congrArg (pd 0 h) (heq a)]
      exact integral_pd_coordinate_line h hh hp 0 _
    simp [hline]
  · rw [integral_torusBox _ hc]
    have hline (a : ℝ) : ∫ b in (0 : ℝ)..(2 * Real.pi), pd 1 h (torusVec a b) = 0 := by
      have heq (b : ℝ) : torusVec a b = torusVec a 0 + b • EuclideanSpace.single 1 1 := by
        ext j
        fin_cases j <;> simp [torusVec, EuclideanSpace.single_apply]
      rw [show (fun b => pd 1 h (torusVec a b)) =
        (fun b => pd 1 h (torusVec a 0 + b • EuclideanSpace.single 1 1)) from
          funext fun b => congrArg (pd 1 h) (heq b)]
      exact integral_pd_coordinate_line h hh hp 1 _
    simp [hline]

lemma torus_pd_mul (f g : R2 → ℝ) (x : R2) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x := by
  unfold pd
  rw [fderiv_fun_mul hf hg]
  simp
  ring

lemma IsTorusPeriodic.mul {f g : R2 → ℝ} (hf : IsTorusPeriodic f) (hg : IsTorusPeriodic g) :
    IsTorusPeriodic (fun x => f x * g x) := fun x i => by
      dsimp only
      rw [hf, hg]

/-- Scalar periodic integration by parts on the fundamental square. -/
lemma integral_mul_pd_periodic (f g : R2 → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : IsTorusPeriodic f) (hgp : IsTorusPeriodic g) (i : Fin 2) :
    ∫ x in torusBox, f x * pd i g x = -∫ x in torusBox, pd i f x * g x := by
  have h0 := integral_pd_eq_zero _ (hf.mul hg) (hfp.mul hgp) i
  have heq (x : R2) : pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x :=
    torus_pd_mul f g x (hf.differentiable one_ne_zero x) (hg.differentiable one_ne_zero x) i
  simp_rw [heq] at h0
  have hI {k : R2 → ℝ} (hk : Continuous k) : Integrable k μT := by
    obtain ⟨C, hC⟩ := bound_on_box hk
    apply Integrable.of_bound hk.aestronglyMeasurable C
    rw [ae_restrict_iff' measurableSet_torusBox]
    exact Eventually.of_forall fun x hx => by simpa only [Real.norm_eq_abs] using hC x hx
  rw [integral_add (f := fun x => pd i f x * g x) (g := fun x => f x * pd i g x)
    (hI ((continuous_pd_of_contDiff_one f hf i).mul hg.continuous))
    (hI (hf.continuous.mul (continuous_pd_of_contDiff_one g hg i)))] at h0
  linarith

lemma integrable_torusBox_of_continuous {k : R2 → ℝ} (hk : Continuous k) :
    Integrable k μT := by
  obtain ⟨C, hC⟩ := bound_on_box hk
  apply Integrable.of_bound hk.aestronglyMeasurable C
  rw [ae_restrict_iff' measurableSet_torusBox]
  exact Eventually.of_forall fun x hx => by simpa only [Real.norm_eq_abs] using hC x hx

lemma torus_pd_component (u : R2 → R2) (x : R2) (hu : DifferentiableAt ℝ u x)
    (j k : Fin 2) : pd j (fun y => u y k) x = pd j u x k := by
  unfold pd
  have heq : (fun y => u y k) = (EuclideanSpace.proj k : R2 →L[ℝ] ℝ) ∘ u := rfl
  rw [heq, fderiv_comp x (EuclideanSpace.proj k).differentiableAt hu]
  have hproj : fderiv ℝ (EuclideanSpace.proj k : R2 →L[ℝ] ℝ) (u x) =
      (EuclideanSpace.proj k : R2 →L[ℝ] ℝ) :=
    (EuclideanSpace.proj k : R2 →L[ℝ] ℝ).hasFDerivAt.fderiv
  rw [hproj]
  rfl

/-- A classical periodic steady Euler field represents a stationary weak
Euler datum. The classical equation is `(u · ∇)u = ∇P`; its potential
is removed using the divergence-free tests and periodic integration by parts. -/
theorem isStationary_of_convective_gradient {v : L2T} {u : R2 → R2}
    (hvu : (v : R2 → R2) =ᵐ[μT] u) (hu : ContDiff ℝ 1 u)
    (hup : IsTorusPeriodic u) (hdiv : ∀ x, pd 0 u x 0 + pd 1 u x 1 = 0)
    (P : R2 → ℝ) (hP : ContDiff ℝ 1 P) (hPp : IsTorusPeriodic P)
    (hconv : ∀ x i, (∑ j : Fin 2, u x j * pd j u x i) = pd i P x) :
    IsStationary v := by
  intro ψ hψ hψp hψdiv
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
  have huc (i : Fin 2) : ContDiff ℝ 1 (fun x => u x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).contDiff.comp hu
  have hψc (i : Fin 2) : ContDiff ℝ 1 (fun x => ψ x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).contDiff.comp hψ1
  have hupc (i : Fin 2) : IsTorusPeriodic (fun x => u x i) := by
    intro x j
    exact congrArg (fun y : R2 => y i) (hup x j)
  have hψpc (i : Fin 2) : IsTorusPeriodic (fun x => ψ x i) := by
    intro x j
    exact congrArg (fun y : R2 => y i) (hψp x j)
  have hupd (x : R2) (i j : Fin 2) : pd j (fun y => u y i) x = pd j u x i :=
    torus_pd_component u x (hu.differentiable one_ne_zero x) j i
  have hψpd (x : R2) (i j : Fin 2) : pd j (fun y => ψ y i) x = pd j ψ x i :=
    torus_pd_component ψ x (hψ1.differentiable one_ne_zero x) j i
  have hprod (x : R2) (i j : Fin 2) :
      pd j (fun y => u y i * u y j) x = pd j u x i * u x j + u x i * pd j u x j := by
    rw [torus_pd_mul _ _ x ((huc i).differentiable one_ne_zero x)
      ((huc j).differentiable one_ne_zero x), hupd, hupd]
  have hflux (x : R2) (i : Fin 2) :
      (∑ j : Fin 2, pd j (fun y => u y i * u y j) x) = pd i P x := by
    simp_rw [hprod]
    have hc := hconv x i
    have hd := hdiv x
    simp only [Fin.sum_univ_two] at hc ⊢
    linear_combination hc + u x i * hd
  have hpair (i j : Fin 2) :
      (∫ x in torusBox, u x i * u x j * pd j ψ x i) =
        -∫ x in torusBox, pd j (fun y => u y i * u y j) x * ψ x i := by
    simpa only [hψpd] using integral_mul_pd_periodic (fun x => u x i * u x j)
      (fun x => ψ x i) ((huc i).mul (huc j)) (hψc i) ((hupc i).mul (hupc j)) (hψpc i) j
  have hI (i j : Fin 2) : Integrable (fun x => u x i * u x j * pd j ψ x i) μT := by
    apply integrable_torusBox_of_continuous
    exact ((huc i).continuous.mul (huc j).continuous).mul
      ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one ψ hψ1 j))
  have hJ (i j : Fin 2) :
      Integrable (fun x => pd j (fun y => u y i * u y j) x * ψ x i) μT :=
    integrable_torusBox_of_continuous
      ((continuous_pd_of_contDiff_one _ ((huc i).mul (huc j)) j).mul (hψc i).continuous)
  have hK (i : Fin 2) : Integrable (fun x => P x * pd i ψ x i) μT :=
    integrable_torusBox_of_continuous (hP.continuous.mul
      ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one ψ hψ1 i)))
  have hae : (fun x => ∑ i, ∑ j, v x i * v x j * pd j ψ x i) =ᵐ[μT]
      (fun x => ∑ i, ∑ j, u x i * u x j * pd j ψ x i) := by
    filter_upwards [hvu] with x hx
    rw [hx]
  rw [integral_congr_ae hae]
  calc
    (∫ x in torusBox, ∑ i, ∑ j, u x i * u x j * pd j ψ x i) =
        ∑ i, ∑ j, ∫ x in torusBox, u x i * u x j * pd j ψ x i := by
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hI i j))]
      exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ (fun j _ => hI i j)
    _ = ∑ i, -∫ x in torusBox, (∑ j : Fin 2, pd j (fun y => u y i * u y j) x) * ψ x i := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [hpair]
      rw [Finset.sum_neg_distrib]
      congr 1
      simp_rw [Finset.sum_mul]
      exact (integral_finset_sum _ (fun j _ => hJ i j)).symm
    _ = ∑ i, -∫ x in torusBox, pd i P x * ψ x i := by simp_rw [hflux]
    _ = ∑ i, ∫ x in torusBox, P x * pd i ψ x i := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      simpa only [hψpd] using integral_mul_pd_periodic P (fun x => ψ x i)
        hP (hψc i) hPp (hψpc i) i
    _ = ∫ x in torusBox, P x * (∑ i : Fin 2, pd i ψ x i) := by
      simp_rw [Finset.mul_sum]
      exact (integral_finset_sum _ (fun i _ => hK i)).symm
    _ = 0 := by
      have hz (x : R2) : (∑ i : Fin 2, pd i ψ x i) = 0 := by
        simpa only [Fin.sum_univ_two] using hψdiv x
      simp_rw [hz, mul_zero]
      simp

/-- The smooth stationary criterion specialized to the canonical `toLp`
representative of the velocity. -/
theorem isStationary_toLp_of_convective_gradient {u : R2 → R2}
    (hLp : MemLp u 2 μT) (hu : ContDiff ℝ 1 u)
    (hup : IsTorusPeriodic u) (hdiv : ∀ x, pd 0 u x 0 + pd 1 u x 1 = 0)
    (P : R2 → ℝ) (hP : ContDiff ℝ 1 P) (hPp : IsTorusPeriodic P)
    (hconv : ∀ x i, (∑ j : Fin 2, u x j * pd j u x i) = pd i P x) :
    IsStationary (hLp.toLp u) :=
  isStationary_of_convective_gradient hLp.coeFn_toLp hu hup hdiv P hP hPp hconv

/-- Classical pointwise incompressibility of a periodic `C¹` field
implies the distributional divergence-free condition used in the project. -/
theorem divFree_of_pointwise_divergence_zero {v : L2T} {u : R2 → R2}
    (hvu : (v : R2 → R2) =ᵐ[μT] u) (hu : ContDiff ℝ 1 u)
    (hup : IsTorusPeriodic u) (hdiv : ∀ x, pd 0 u x 0 + pd 1 u x 1 = 0) :
    DivFree v := by
  intro ψ hψ
  have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by exact_mod_cast le_top)
  have huc (i : Fin 2) : ContDiff ℝ 1 (fun x => u x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).contDiff.comp hu
  have hupc (i : Fin 2) : IsTorusPeriodic (fun x => u x i) := by
    intro x j
    exact congrArg (fun y : R2 => y i) (hup x j)
  have hupd (x : R2) (i : Fin 2) : pd i (fun y => u y i) x = pd i u x i :=
    torus_pd_component u x (hu.differentiable one_ne_zero x) i i
  have hpair (i : Fin 2) : (∫ x in torusBox, u x i * pd i ψ x) =
      -∫ x in torusBox, pd i u x i * ψ x := by
    simpa only [hupd] using
      integral_mul_pd_periodic (fun x => u x i) ψ (huc i) hψ1 (hupc i) hψ.2 i
  have hI (i : Fin 2) : Integrable (fun x => u x i * pd i ψ x) μT :=
    integrable_torusBox_of_continuous
      ((huc i).continuous.mul (continuous_pd_of_contDiff_one ψ hψ1 i))
  have hJ (i : Fin 2) : Integrable (fun x => pd i u x i * ψ x) μT :=
    integrable_torusBox_of_continuous
      (((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one u hu i)).mul hψ1.continuous)
  have hae : (fun x => ∑ i, v x i * pd i ψ x) =ᵐ[μT]
      (fun x => ∑ i, u x i * pd i ψ x) := by
    filter_upwards [hvu] with x hx
    rw [hx]
  rw [integral_congr_ae hae]
  calc
    (∫ x in torusBox, ∑ i, u x i * pd i ψ x) =
        ∑ i, ∫ x in torusBox, u x i * pd i ψ x :=
      integral_finset_sum _ (fun i _ => hI i)
    _ = -∫ x in torusBox, (∑ i : Fin 2, pd i u x i) * ψ x := by
      simp_rw [hpair]
      rw [Finset.sum_neg_distrib]
      congr 1
      simp_rw [Finset.sum_mul]
      exact (integral_finset_sum _ (fun i _ => hJ i)).symm
    _ = 0 := by
      have hz (x : R2) : (∑ i : Fin 2, pd i u x i) = 0 := by
        simpa only [Fin.sum_univ_two] using hdiv x
      simp_rw [hz, zero_mul]
      simp

end Euler2D

end

