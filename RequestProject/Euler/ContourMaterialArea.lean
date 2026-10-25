module

public import RequestProject.Euler.ContourPatchFlux
public import RequestProject.Euler.ContourPatchFluxIntegrability
public import RequestProject.Euler.ContourC1PatchVelocity
public import RequestProject.Euler.ContourAreaVariation

/-! The actual finite-interface material field is tangent to each
original area functional. Its zero flux is proved from the actual
patch kernels, not assumed as a property of the vector field. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate NNReal

namespace Euler2D

theorem im_conj_real_weighted_sum_mul {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (u : ι → ℂ) (a : ℂ) :
    (conj (∑ j, (g j : ℂ) * u j) * a).im = ∑ j, g j * (conj (u j) * a).im := by
  rw [map_sum, Finset.sum_mul]
  have him (v : ι → ℂ) : (∑ j, v j).im = ∑ j, (v j).im := by
    simpa only [Complex.imCLM_apply] using map_sum Complex.imCLM v Finset.univ
  rw [him]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_mul, Complex.conj_ofReal, mul_assoc, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

theorem integral_normalFlux_finitePatches_zero {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Ω : ι → Set ℂ) (R : ι → ℝ)
    {z dz : ℝ → ℂ} {M D : ℝ}
    (hm : ∀ j, MeasurableSet (Ω j)) (hR : ∀ j, 0 ≤ R j)
    (hΩ : ∀ j, Ω j ⊆ Metric.closedBall (0 : ℂ) (R j))
    (hz : ∀ θ, HasDerivAt z (dz θ) θ) (hdzc : Continuous dz)
    (hp : Function.Periodic z (2 * Real.pi))
    (hM : ∀ θ, ‖z θ‖ ≤ M) (hD : ∀ θ, ‖dz θ‖ ≤ D) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (conj (∑ j, (g j : ℂ) * velocityC ((Ω j).indicator (fun _ => (1 : ℝ))) (z θ)) * dz θ).im) = 0 := by
  have hzc : Continuous z := continuous_iff_continuousAt.mpr (fun θ => (hz θ).continuousAt)
  have hi (j : ι) := intervalIntegrable_patchNormalFlux (hm j) (hΩ j) hzc hdzc hD
  simp_rw [im_conj_real_weighted_sum_mul]
  rw [intervalIntegral.integral_finset_sum (fun j _ => (hi j).const_mul (g j))]
  apply Finset.sum_eq_zero
  intro j _
  rw [intervalIntegral.integral_const_mul,
    integral_normalFlux_patch_zero (hm j) (hR j) (hΩ j) hz hdzc hp hM hD, mul_zero]

theorem contourC1BoundaryField_normalFlux_zero {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
    (hr : ∀ j, 0 < r j) (href : ∀ j, ContourC1Space.lift γ (Z₀ j) = refCircle (r j))
    (hsmall : ∀ j, ‖Z j - Z₀ j‖ ≤ r j / 4) (i : ι) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (conj (contourC1BoundaryField g Z i θ) * deriv (ContourC1Space.lift γ (Z i)) θ).im) = 0 := by
  let Ω : ι → Set ℂ := fun j => contourC1EnclosedDomain (Z j) (Z₀ j) (hr j) (href j) (hsmall j)
  let R : ι → ℝ := fun j => r j + ‖Z j - Z₀ j‖
  have he (θ : ℝ) : contourC1BoundaryField g Z i θ =
      ∑ j, (g j : ℂ) * velocityC ((Ω j).indicator (fun _ => (1 : ℝ)))
        (ContourC1Space.lift γ (Z i) θ) := by
    unfold contourC1BoundaryField contourBoundaryField
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hv := velocityC_contourC1PatchVorticity (Z j) (Z₀ j) (hr j) (href j) (hsmall j)
      (ContourC1Space.lift γ (Z i) θ)
    change _ = (g j : ℂ) * velocityC (contourC1PatchVorticity (Z j) (Z₀ j)
      (hr j) (href j) (hsmall j)) _
    rw [hv]
    ring
  simp_rw [he]
  exact integral_normalFlux_finitePatches_zero g Ω R
    (fun j => (isOpen_contourC1EnclosedDomain (Z j) (Z₀ j) (hr j) (href j) (hsmall j)).measurableSet)
    (fun j => add_nonneg (hr j).le (norm_nonneg _))
    (fun j => (contourC1EnclosedDomain_subset_ball (Z j) (Z₀ j) (hr j) (href j) (hsmall j)).trans
      Metric.ball_subset_closedBall)
    (fun θ => (ContourC1Space.hasDerivAt_lift (Z i) θ).differentiableAt.hasDerivAt)
    (contDiff_one_iff_deriv.mp (ContourC1Space.contDiff_lift (Z i))).2
    (ContourC1Space.periodic_lift (Z i))
    (fun θ => ContourC1Space.norm_eval_le (Z i) (θ : ContourCircle))
    (ContourC1Space.norm_deriv_lift_le (Z i))

theorem hasDerivAt_contourArea_zero_of_material_boundary_field
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) {Z : ℝ → ι → ContourC1Space γ} (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (href : ∀ j, ContourC1Space.lift γ (Z₀ j) = refCircle (r j))
    {t : ℝ} {V : ι → ContourC1Space γ}
    (hsmall : ∀ j, ‖Z t j - Z₀ j‖ ≤ r j / 4)
    (hZ : ∀ i, HasDerivAt (fun s => Z s i) (V i) t)
    (hV : ∀ i θ, ContourC1Space.lift γ (V i) θ = contourC1BoundaryField g (Z t) i θ)
    (i : ι) : HasDerivAt (fun s => contourArea γ (Z s i)) 0 t := by
  have hd := hasDerivAt_contourArea_along_curve (hZ i)
  simp_rw [hV i] at hd
  rw [contourC1BoundaryField_normalFlux_zero g (Z t) Z₀ r hr href hsmall i] at hd
  exact hd

theorem contourArea_eq_initial_of_material_boundary_field
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (href : ∀ j, ContourC1Space.lift γ (Z₀ j) = refCircle (r j))
    {a b : ℝ} (V : ℝ → ι → ContourC1Space γ)
    (hsmall : ∀ s ∈ Icc a b, ∀ j, ‖Z s j - Z₀ j‖ ≤ r j / 4)
    (hZ : ∀ s ∈ Icc a b, ∀ i, HasDerivAt (fun q => Z q i) (V s i) s)
    (hV : ∀ s ∈ Icc a b, ∀ i θ, ContourC1Space.lift γ (V s i) θ =
      contourC1BoundaryField g (Z s) i θ)
    {t : ℝ} (ht : t ∈ Icc a b) (i : ι) :
    contourArea γ (Z t i) = contourArea γ (Z a i) := by
  have hd (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt (fun q => contourArea γ (Z q i)) 0 s :=
    hasDerivAt_contourArea_zero_of_material_boundary_field (Z := Z) (V := V s)
      g Z₀ r hr href (hsmall s hs) (hZ s hs) (hV s hs) i
  have hscope : Set.uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := t) (fun s hs => hd s (hscope hs))
    (intervalIntegral.intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a t)
  exact sub_eq_zero.mp (by simpa only [intervalIntegral.integral_zero] using he.symm)

theorem enclosedArea_eq_initial_of_material_boundary_field
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (href : ∀ j, ContourC1Space.lift γ (Z₀ j) = refCircle (r j))
    {a b : ℝ} (hab : a ≤ b) (V : ℝ → ι → ContourC1Space γ)
    (hsmall : ∀ s ∈ Icc a b, ∀ j, ‖Z s j - Z₀ j‖ ≤ r j / 4)
    (hZ : ∀ s ∈ Icc a b, ∀ i, HasDerivAt (fun q => Z q i) (V s i) s)
    (hV : ∀ s ∈ Icc a b, ∀ i θ, ContourC1Space.lift γ (V s i) θ =
      contourC1BoundaryField g (Z s) i θ)
    {t : ℝ} (ht : t ∈ Icc a b) (i : ι) :
    volume.real (contourC1EnclosedDomain (Z t i) (Z₀ i) (hr i) (href i) (hsmall t ht i)) =
      volume.real (contourC1EnclosedDomain (Z a i) (Z₀ i) (hr i) (href i)
        (hsmall a ⟨le_rfl, hab⟩ i)) := by
  rw [area_contourC1EnclosedDomain, area_contourC1EnclosedDomain]
  exact contourArea_eq_initial_of_material_boundary_field g Z Z₀ r hr href V hsmall hZ hV ht i

end Euler2D
