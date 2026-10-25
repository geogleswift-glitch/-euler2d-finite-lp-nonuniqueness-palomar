module

public import RequestProject.Euler.Stationary

/-!
# Classical periodic Euler fields give the project's weak solutions

This connects the pointwise momentum equation, with its pressure, to the
actual space-time weak equation on the fundamental square. The proof uses
periodic spatial integration by parts and the time product rule.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Euler2D

/-- Joint continuity on the compact fundamental square already gives
strong `L²` continuity of any almost-everywhere equal representative path. -/
lemma continuousOn_L2_of_continuous_rep {T : ℝ} {U : ℝ → L2T} {u : ℝ → R2 → R2}
    (hu : Continuous (Function.uncurry u))
    (hae : ∀ t ∈ Icc 0 T, (U t : R2 → R2) =ᵐ[μT] u t) :
    ContinuousOn U (Icc 0 T) := by
  let A : ℝ := measureUnivNNReal μT ^ (2 : ENNReal).toReal⁻¹
  have hA : 0 ≤ A := by positivity
  have huc : UniformContinuousOn (Function.uncurry u) (Icc (0 : ℝ) T ×ˢ closedBox) :=
    (isCompact_Icc.prod isCompact_closedBox).uniformContinuousOn_of_continuous hu.continuousOn
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  let η := ε / (A + 1)
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc η hη
  refine ⟨δ, hδ, fun s hs hst => ?_⟩
  have hbound : ∀ᵐ x ∂μT, ‖(U s - U t) x‖ ≤ η := by
    filter_upwards [Lp.coeFn_sub (U s) (U t), hae s hs, hae t ht,
      ae_restrict_mem measurableSet_torusBox] with x hsub hxs hxt hx
    rw [hsub]
    change ‖U s x - U t x‖ ≤ η
    rw [hxs, hxt, ← dist_eq_norm]
    apply le_of_lt (hclose (s, x) ⟨hs, torusBox_subset_closedBox hx⟩
      (t, x) ⟨ht, torusBox_subset_closedBox hx⟩ ?_)
    simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hst
  rw [dist_eq_norm]
  apply (Lp.norm_le_of_ae_bound hη.le hbound).trans_lt
  change A * η < ε
  dsimp only [η]
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < A + 1)]
  nlinarith

lemma integral_periodic_flux_by_parts {u ψ : R2 → R2}
    (hu : ContDiff ℝ 1 u) (hup : IsTorusPeriodic u)
    (hψ : ContDiff ℝ 1 ψ) (hψp : IsTorusPeriodic ψ)
    (hdiv : ∀ x, pd 0 u x 0 + pd 1 u x 1 = 0) :
    (∫ x in torusBox, ∑ i, ∑ j, u x i * u x j * pd j ψ x i) =
      -(∫ x in torusBox, ∑ i, (∑ j, u x j * pd j u x i) * ψ x i) := by
  have huc (i : Fin 2) : ContDiff ℝ 1 (fun x => u x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).contDiff.comp hu
  have hψc (i : Fin 2) : ContDiff ℝ 1 (fun x => ψ x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).contDiff.comp hψ
  have hpc {v : R2 → R2} (hv : IsTorusPeriodic v) (i : Fin 2) :
      IsTorusPeriodic (fun x => v x i) :=
    fun x j => congrArg (fun y : R2 => y i) (hv x j)
  have hupd (x : R2) (i j : Fin 2) : pd j (fun y => u y i) x = pd j u x i :=
    torus_pd_component u x (hu.differentiable one_ne_zero x) j i
  have hψpd (x : R2) (i j : Fin 2) : pd j (fun y => ψ y i) x = pd j ψ x i :=
    torus_pd_component ψ x (hψ.differentiable one_ne_zero x) j i
  have hprod (x : R2) (i j : Fin 2) :
      pd j (fun y => u y i * u y j) x = pd j u x i * u x j + u x i * pd j u x j := by
    rw [torus_pd_mul _ _ x ((huc i).differentiable one_ne_zero x)
      ((huc j).differentiable one_ne_zero x), hupd, hupd]
  have hflux (x : R2) (i : Fin 2) :
      (∑ j : Fin 2, pd j (fun y => u y i * u y j) x) =
        ∑ j : Fin 2, u x j * pd j u x i := by
    simp_rw [hprod]
    simp only [Fin.sum_univ_two]
    linear_combination u x i * hdiv x
  have hpair (i j : Fin 2) :
      (∫ x in torusBox, u x i * u x j * pd j ψ x i) =
        -∫ x in torusBox, pd j (fun y => u y i * u y j) x * ψ x i := by
    simpa only [hψpd] using integral_mul_pd_periodic (fun x => u x i * u x j)
      (fun x => ψ x i) ((huc i).mul (huc j)) (hψc i)
        ((hpc hup i).mul (hpc hup j)) (hpc hψp i) j
  have hI (i j : Fin 2) : Integrable (fun x => u x i * u x j * pd j ψ x i) μT :=
    integrable_torusBox_of_continuous
      (((huc i).continuous.mul (huc j).continuous).mul
        ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
          (continuous_pd_of_contDiff_one ψ hψ j)))
  have hJ (i j : Fin 2) :
      Integrable (fun x => pd j (fun y => u y i * u y j) x * ψ x i) μT :=
    integrable_torusBox_of_continuous
      ((continuous_pd_of_contDiff_one _ ((huc i).mul (huc j)) j).mul (hψc i).continuous)
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hI i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hI _ j), hpair,
    Finset.sum_neg_distrib]
  congr 1
  rw [integral_finset_sum _ (fun i _ => by
    simpa only [← hflux, Finset.sum_mul] using integrable_finset_sum _ (fun j _ => hJ i j))]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [← hflux]
  simp_rw [Finset.sum_mul]
  exact (integral_finset_sum _ (fun j _ => hJ i j)).symm

lemma integral_pressure_pairing_eq_zero {P : R2 → ℝ} {ψ : R2 → R2}
    (hP : ContDiff ℝ 1 P) (hPp : IsTorusPeriodic P)
    (hψ : ContDiff ℝ 1 ψ) (hψp : IsTorusPeriodic ψ)
    (hdiv : ∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) :
    (∫ x in torusBox, ∑ i, pd i P x * ψ x i) = 0 := by
  have hψc (i : Fin 2) : ContDiff ℝ 1 (fun x => ψ x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).contDiff.comp hψ
  have hI (i : Fin 2) : Integrable (fun x => pd i P x * ψ x i) μT :=
    integrable_torusBox_of_continuous
      ((continuous_pd_of_contDiff_one P hP i).mul (hψc i).continuous)
  have hJ (i : Fin 2) : Integrable (fun x => P x * pd i ψ x i) μT :=
    integrable_torusBox_of_continuous (hP.continuous.mul
      ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one ψ hψ i)))
  have hpair (i : Fin 2) :
      (∫ x in torusBox, pd i P x * ψ x i) = -(∫ x in torusBox, P x * pd i ψ x i) := by
    have hpc : IsTorusPeriodic (fun x => ψ x i) :=
      fun x j => congrArg (fun y : R2 => y i) (hψp x j)
    have h := integral_mul_pd_periodic P (fun x => ψ x i) hP (hψc i) hPp hpc i
    simp_rw [torus_pd_component ψ _ (hψ.differentiable one_ne_zero _) i i] at h
    linarith
  rw [integral_finset_sum _ (fun i _ => hI i)]
  simp_rw [hpair]
  rw [Finset.sum_neg_distrib, ← integral_finset_sum _ (fun i _ => hJ i)]
  have hz (x : R2) : (∑ i, P x * pd i ψ x i) = 0 := by
    rw [← Finset.mul_sum, Fin.sum_univ_two, hdiv, mul_zero]
  simp_rw [hz]
  simp

/-- Time integration of the product rule for two jointly `C¹` fields. -/
lemma integral_time_product_rule {u φ : ℝ → R2 → R2}
    (hu : ContDiff ℝ 1 (Function.uncurry u))
    (hφ : ContDiff ℝ 1 (Function.uncurry φ)) (a b : ℝ) :
    (∫ t in a..b, ∫ x in torusBox,
      ∑ i, (deriv (fun s => u s x i) t * φ t x i +
        u t x i * deriv (fun s => φ s x i) t)) =
      ∫ x in torusBox, ∑ i, (u b x i * φ b x i - u a x i * φ a x i) := by
  let G : ℝ → R2 → ℝ := fun t x => ∑ i,
    (deriv (fun s => u s x i) t * φ t x i + u t x i * deriv (fun s => φ s x i) t)
  have hc : Continuous (Function.uncurry G) := by
    change Continuous (fun p : ℝ × R2 => ∑ i : Fin 2,
      (deriv (fun s => u s p.2 i) p.1 * φ p.1 p.2 i +
        u p.1 p.2 i * deriv (fun s => φ s p.2 i) p.1))
    apply continuous_finset_sum
    intro i _
    exact ((continuous_deriv_time hu i).mul
      ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp hφ.continuous)).add
      (((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp hu.continuous).mul
        (continuous_deriv_time hφ i))
  have hI : Integrable (Function.uncurry G)
      ((volume.restrict (uIoc a b)).prod μT) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hc.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_closedBox)).mono_set
        (prod_mono uIoc_subset_uIcc torusBox_subset_closedBox)
  change (∫ t in a..b, ∫ x in torusBox, G t x) = _
  rw [intervalIntegral_integral_swap hI]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∫ t in a..b, G t x) = _
    have hd (t : ℝ) : HasDerivAt (fun s => ∑ i : Fin 2, u s x i * φ s x i) (G t x) t := by
      apply HasDerivAt.fun_sum
      intro i _
      rw [deriv_time_coord (hu.differentiable one_ne_zero),
        deriv_time_coord (hφ.differentiable one_ne_zero)]
      exact (((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_time (hu.differentiable one_ne_zero) t x)).mul
        ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
          (hasDerivAt_time (hφ.differentiable one_ne_zero) t x)))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((hc.comp (Continuous.prodMk_left x)).intervalIntegrable a b)]
    exact (Finset.sum_sub_distrib
      (fun i : Fin 2 => u b x i * φ b x i)
      (fun i : Fin 2 => u a x i * φ a x i)).symm

/-- A classical periodic Euler velocity satisfies exactly the weak Euler
formulation of `Basic.lean`. Strong continuity follows from joint
continuity of its representative and is not a separate assumption. -/
theorem isWeakEulerSolution_of_classical {T : ℝ} {U : ℝ → L2T} {u : ℝ → R2 → R2}
    (hae : ∀ t ∈ Icc 0 T, (U t : R2 → R2) =ᵐ[μT] u t)
    (hu : ContDiff ℝ 1 (Function.uncurry u))
    (hup : ∀ t, IsTorusPeriodic (u t))
    (hdiv : ∀ t x, pd 0 (u t) x 0 + pd 1 (u t) x 1 = 0)
    (P : ℝ → R2 → ℝ) (hP : ∀ t, ContDiff ℝ 1 (P t))
    (hPp : ∀ t, IsTorusPeriodic (P t))
    (hEuler : ∀ t x i, deriv (fun s => u s x i) t +
      (∑ j, u t x j * pd j (u t) x i) = -pd i (P t) x)
    (hT : 0 ≤ T) : IsWeakEulerSolution T (U 0) U := by
  have hU := continuousOn_L2_of_continuous_rep hu.continuous hae
  have hus (t : ℝ) : ContDiff ℝ 1 (u t) := hu.comp (contDiff_prodMk_right t)
  refine ⟨hU, fun t ht => divFree_of_pointwise_divergence_zero
    (hae t ht) (hus t) (hup t) (hdiv t), rfl, fun φ hφ => ?_⟩
  have hφ1 := hφ.contDiff_one
  have hφs (t : ℝ) : ContDiff ℝ 1 (φ t) := hφ1.comp (contDiff_prodMk_right t)
  have hI {f : R2 → ℝ} (hf : Continuous f) : Integrable f μT :=
    integrable_torusBox_of_continuous hf
  have htime (t : ℝ) :
      (∫ x in torusBox, eulerIntegrand (u t) φ t x) =
      ∫ x in torusBox, ∑ i, (deriv (fun s => u s x i) t * φ t x i +
        u t x i * deriv (fun s => φ s x i) t) := by
    have hA (i : Fin 2) : Continuous (fun x => deriv (fun s => u s x i) t) :=
      (continuous_deriv_time hu i).comp (Continuous.prodMk_right t)
    have hB (i : Fin 2) : Continuous (fun x => deriv (fun s => φ s x i) t) :=
      (continuous_deriv_time hφ1 i).comp (Continuous.prodMk_right t)
    have hC (i : Fin 2) : Continuous (fun x => ∑ j, u t x j * pd j (u t) x i) := by
      apply continuous_finset_sum
      intro j _
      exact ((EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.comp (hus t).continuous).mul
        ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
          (continuous_pd_of_contDiff_one (u t) (hus t) j))
    have hcoord (i : Fin 2) : Continuous (fun x => φ t x i) :=
      (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp (hφs t).continuous
    have hlin : Integrable (fun x => ∑ i, u t x i * deriv (fun s => φ s x i) t) μT :=
      hI (continuous_finset_sum _ fun i _ =>
        ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp (hus t).continuous).mul (hB i))
    have hquad : Integrable (fun x => ∑ i, ∑ j, u t x i * u t x j * pd j (φ t) x i) μT := by
      apply hI
      apply continuous_finset_sum
      intro i _
      apply continuous_finset_sum
      intro j _
      exact (((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp (hus t).continuous).mul
        ((EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.comp (hus t).continuous)).mul
          ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
            (continuous_pd_of_contDiff_one (φ t) (hφs t) j))
    unfold eulerIntegrand
    rw [integral_add hlin hquad,
      integral_periodic_flux_by_parts (hus t) (hup t) (hφs t) (hφ.periodic t) (hdiv t)]
    have heq (x : R2) : (∑ i, (∑ j, u t x j * pd j (u t) x i) * φ t x i) =
        -(∑ i, deriv (fun s => u s x i) t * φ t x i) - ∑ i, pd i (P t) x * φ t x i := by
      simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      linear_combination φ t x i * hEuler t x i
    simp_rw [heq]
    have hD : Integrable (fun x => ∑ i : Fin 2, deriv (fun s => u s x i) t * φ t x i) μT :=
      hI (continuous_finset_sum _ fun i _ => (hA i).mul (hcoord i))
    have hPr : Integrable (fun x => ∑ i : Fin 2, pd i (P t) x * φ t x i) μT :=
      hI (continuous_finset_sum _ fun i _ =>
        (continuous_pd_of_contDiff_one (P t) (hP t) i).mul (hcoord i))
    have hsub := integral_sub hD.neg hPr
    simp only [Pi.neg_apply] at hsub
    rw [hsub, integral_neg,
      integral_pressure_pairing_eq_zero (hP t) (hPp t) (hφs t) (hφ.periodic t) (hφ.divFree t)]
    simp only [sub_zero, neg_neg]
    rw [← integral_add hlin hD]
    congr 1
    funext x
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrep : (∫ t in (0 : ℝ)..T, ∫ x in torusBox, eulerIntegrand (U t) φ t x) =
      ∫ t in (0 : ℝ)..T, ∫ x in torusBox, eulerIntegrand (u t) φ t x := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply integral_congr_ae
    filter_upwards [hae t (by simpa only [uIcc_of_le hT] using ht)] with x hx
    rw [eulerIntegrand, hx]
    rfl
  obtain ⟨T', hT', hsupport⟩ := hφ.support
  have hzero (x : R2) : φ T x = 0 := hsupport T hT'.le x
  have hinit : (∫ x in torusBox, ∑ i, (U 0) x i * φ 0 x i) =
      ∫ x in torusBox, ∑ i, u 0 x i * φ 0 x i := by
    apply integral_congr_ae
    filter_upwards [hae 0 ⟨le_rfl, hT⟩] with x hx
    rw [hx]
  rw [hrep]
  simp_rw [htime]
  rw [integral_time_product_rule hu hφ1 0 T, hinit]
  simp only [hzero, PiLp.zero_apply, mul_zero, zero_sub, Finset.sum_neg_distrib,
    integral_neg, neg_add_cancel]

end Euler2D

end
