module

public import RequestProject.Euler.WeakAux

/-!
# From particle trajectories to weak vorticity transport

The particle equation is differentiated only along trajectories.  Its
weighted label integral is justified by the fundamental theorem of calculus
and Fubini.  Joint continuity on compact time/label sets supplies the
dominating bound; no global speed bound or measure-preservation assumption
is needed for this step.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Euler2D

/-- The velocity paired with the spatial gradient of a scalar test. -/
def transportTestDerivative (v : ℝ → R2 → R2) (χ : R2 → ℝ) (s : ℝ) (x : R2) : ℝ :=
  ∑ i : Fin 2, v s x i * pd i χ x

theorem fderiv_apply_eq_sum_pd (χ : R2 → ℝ) (x y : R2) :
    fderiv ℝ χ x y = ∑ i : Fin 2, y i * pd i χ x := by
  have hy : y = ∑ i : Fin 2, y i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    fin_cases j <;> simp [EuclideanSpace.single_apply]
  conv_lhs => rw [hy]
  simp [pd]

theorem continuous_transportTestDerivative {v : ℝ → R2 → R2} {χ : R2 → ℝ}
    (hv : Continuous (Function.uncurry v)) (hχ : ContDiff ℝ ∞ χ) :
    Continuous (Function.uncurry (transportTestDerivative v χ)) := by
  change Continuous (fun p : ℝ × R2 => ∑ i : Fin 2, v p.1 p.2 i * pd i χ p.2)
  apply continuous_finset_sum
  intro i _
  have hpd : Continuous (pd i χ) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i).comp hv).mul
    (hpd.comp continuous_snd)

theorem hasDerivAt_test_along_flow {X v : ℝ → R2 → R2} {χ : R2 → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (s : ℝ) (a : R2)
    (hX : HasDerivAt (fun r => X r a) (v s (X s a)) s) :
    HasDerivAt (fun r => χ (X r a)) (transportTestDerivative v χ s (X s a)) s := by
  have hc := ((hχ.differentiable (by simp) (X s a)).hasFDerivAt).comp_hasDerivAt s hX
  simpa only [Function.comp_def, fderiv_apply_eq_sum_pd, transportTestDerivative] using hc

/-- Fundamental theorem of calculus along one actual particle trajectory. -/
theorem test_along_flow_integral {X v : ℝ → R2 → R2} {χ : R2 → ℝ}
    {t : ℝ} (ht : 0 ≤ t)
    (hX : Continuous (Function.uncurry X))
    (hv : Continuous (Function.uncurry v)) (hχ : ContDiff ℝ ∞ χ)
    (a : R2) (hinit : X 0 a = a)
    (hflow : ∀ s ∈ Icc 0 t, HasDerivAt (fun r => X r a) (v s (X s a)) s) :
    χ (X t a) - χ a =
      ∫ s in (0 : ℝ)..t, transportTestDerivative v χ s (X s a) := by
  have hcont : Continuous (fun s => transportTestDerivative v χ s (X s a)) :=
    (continuous_transportTestDerivative hv hχ).comp
      (continuous_id.prodMk (hX.comp (continuous_id.prodMk continuous_const)))
  symm
  convert intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_test_along_flow hχ s a
      (hflow s (by simpa only [uIcc_of_le ht] using hs)))
    (hcont.intervalIntegrable 0 t) using 1
  rw [hinit]

private theorem integrable_weight_continuous {ω₀ : R2 → ℝ}
    (hω₀ : Integrable ω₀ μT) {f : R2 → ℝ} (hf : Continuous f) :
    Integrable (fun a => ω₀ a * f a) μT := by
  obtain ⟨C, hC⟩ := bound_on_box hf
  apply hω₀.mul_bdd hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with a ha
  simpa only [Real.norm_eq_abs] using hC a ha

/-- A continuous time/label kernel can be integrated against an `L¹` label
weight over a finite time interval.  The bound is obtained on a compact
rectangle and is allowed to depend on that interval. -/
theorem integrable_weighted_label_kernel {K : ℝ → R2 → ℝ}
    {ω₀ : R2 → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hK : Continuous (Function.uncurry K)) (hω₀ : Integrable ω₀ μT) :
    Integrable (fun p : ℝ × R2 => ω₀ p.2 * K p.1 p.2)
      ((volume.restrict (uIoc 0 t)).prod μT) := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) t)).prod
    isCompact_closedBox).exists_bound_of_continuousOn
    hK.continuousOn
  have htime : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (uIoc 0 t)) :=
    (continuous_const.intervalIntegrable 0 t).def'
  have hweight : Integrable (fun p : ℝ × R2 => ω₀ p.2)
      ((volume.restrict (uIoc 0 t)).prod μT) := by
    simpa only [one_mul] using htime.mul_prod hω₀
  apply hweight.mul_bdd hK.aestronglyMeasurable
  have hsupp : ∀ᵐ p : ℝ × R2 ∂((volume.restrict (uIoc 0 t)).prod μT),
      p ∈ (uIoc 0 t) ×ˢ torusBox := by
    change ∀ᵐ p : ℝ × R2 ∂((volume.restrict (uIoc 0 t)).prod
      (volume.restrict torusBox)), p ∈ (uIoc 0 t) ×ˢ torusBox
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_uIoc.prod measurableSet_torusBox)
  filter_upwards [hsupp] with p hp
  have hp0 : p.1 ∈ Ioc (0 : ℝ) t := by simpa only [uIoc_of_le ht] using hp.1
  exact hC p ⟨⟨hp0.1.le, hp0.2⟩, torusBox_subset_closedBox hp.2⟩

/-- The time/label integrand is integrable, with a bound obtained on the
compact image of the flow. -/
theorem integrable_lagrangian_testDerivative {X v : ℝ → R2 → R2} {χ : R2 → ℝ}
    {ω₀ : R2 → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hX : Continuous (Function.uncurry X))
    (hv : Continuous (Function.uncurry v)) (hχ : ContDiff ℝ ∞ χ)
    (hω₀ : Integrable ω₀ μT) :
    Integrable (fun p : ℝ × R2 => ω₀ p.2 *
      transportTestDerivative v χ p.1 (X p.1 p.2))
      ((volume.restrict (uIoc 0 t)).prod μT) :=
  integrable_weighted_label_kernel
    (K := fun s a => transportTestDerivative v χ s (X s a)) ht
    ((continuous_transportTestDerivative hv hχ).comp (continuous_fst.prodMk hX)) hω₀

/-- The weighted label identity before invoking any push-forward law. -/
theorem lagrangian_label_difference {X v : ℝ → R2 → R2} {χ : R2 → ℝ}
    {ω₀ : R2 → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hX : Continuous (Function.uncurry X))
    (hv : Continuous (Function.uncurry v)) (hχ : ContDiff ℝ ∞ χ)
    (hω₀ : Integrable ω₀ μT)
    (hinit : ∀ a ∈ torusBox, X 0 a = a)
    (hflow : ∀ a ∈ torusBox, ∀ s ∈ Icc 0 t,
      HasDerivAt (fun r => X r a) (v s (X s a)) s) :
    (∫ a in torusBox, ω₀ a * (χ (X t a) - χ a)) =
      ∫ s in (0 : ℝ)..t, ∫ a in torusBox,
        ω₀ a * transportTestDerivative v χ s (X s a) := by
  calc
    _ = ∫ a in torusBox, ∫ s in (0 : ℝ)..t,
        ω₀ a * transportTestDerivative v χ s (X s a) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_torusBox] with a ha
      rw [intervalIntegral.integral_const_mul,
        ← test_along_flow_integral ht hX hv hχ a (hinit a ha) (hflow a ha)]
    _ = _ := (intervalIntegral_integral_swap
      (integrable_lagrangian_testDerivative ht hX hv hχ hω₀)).symm

theorem lagrangian_label_integral {X v : ℝ → R2 → R2} {χ : R2 → ℝ}
    {ω₀ : R2 → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hX : Continuous (Function.uncurry X))
    (hv : Continuous (Function.uncurry v)) (hχ : ContDiff ℝ ∞ χ)
    (hω₀ : Integrable ω₀ μT)
    (hinit : ∀ a ∈ torusBox, X 0 a = a)
    (hflow : ∀ a ∈ torusBox, ∀ s ∈ Icc 0 t,
      HasDerivAt (fun r => X r a) (v s (X s a)) s) :
    (∫ a in torusBox, ω₀ a * χ (X t a)) = (∫ a in torusBox, ω₀ a * χ a) +
      ∫ s in (0 : ℝ)..t, ∫ a in torusBox,
        ω₀ a * transportTestDerivative v χ s (X s a) := by
  have hd := lagrangian_label_difference ht hX hv hχ hω₀ hinit hflow
  simp_rw [mul_sub] at hd
  have hcontend : Continuous (fun a : R2 => χ (X t a)) := hχ.continuous.comp
    (hX.comp (continuous_const.prodMk continuous_id))
  have hiend : Integrable (fun a => ω₀ a * χ (X t a)) μT :=
    integrable_weight_continuous hω₀ hcontend
  have hiinit : Integrable (fun a => ω₀ a * χ a) μT :=
    integrable_weight_continuous hω₀ hχ.continuous
  rw [integral_sub hiend hiinit] at hd
  linarith

/-- Distributional test derivatives inherit the period of a scalar function. -/
theorem isTorusPeriodic_pd {χ : R2 → ℝ} (hχ : IsTorusPeriodic χ) (i : Fin 2) :
    IsTorusPeriodic (pd i χ) := by
  intro x j
  have heq : (fun y : R2 => χ (y + EuclideanSpace.single j (2 * Real.pi))) = χ :=
    funext fun y => hχ y j
  have hfd := fderiv_comp_add_right (𝕜 := ℝ) (f := χ) (x := x)
    (EuclideanSpace.single j (2 * Real.pi))
  rw [heq] at hfd
  exact congrArg (fun L : R2 →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hfd.symm

theorem isTorusPeriodic_transportTestDerivative {v : ℝ → R2 → R2} {χ : R2 → ℝ}
    (hv : ∀ s, IsTorusPeriodic (v s)) (hχ : IsTorusPeriodic χ) (s : ℝ) :
    IsTorusPeriodic (transportTestDerivative v χ s) := by
  intro x j
  apply Finset.sum_congr rfl
  intro i _
  rw [hv s x j, isTorusPeriodic_pd hχ i x j]

/-- The signed vorticity is the push-forward of its initial label weight
under the particle map.  This is a law of transported integrals, with no
transport differential equation included in the definition. -/
structure IsVorticityPushForward (T : ℝ) (ω₀ : R2 → ℝ) (w : ℝ → R2 → ℝ)
    (X : ℝ → R2 → R2) : Prop where
  integrable : ∀ s ∈ Icc 0 T, Integrable (w s) μT
  pairing : ∀ s ∈ Icc 0 T, ∀ χ : R2 → ℝ, Continuous χ → IsTorusPeriodic χ →
    (∫ x in torusBox, w s x * χ x) =
      ∫ a in torusBox, ω₀ a * χ (X s a)

/-- A continuous particle flow satisfying the ODE, together with its
push-forward vorticity law, satisfies weak vorticity transport for every
smooth periodic scalar test.  Integrability of the time pairing is proved
as part of the result. -/
theorem flow_weak_vorticity_integral {X v : ℝ → R2 → R2} {χ : R2 → ℝ}
    {ω₀ : R2 → ℝ} {w : ℝ → R2 → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hX : Continuous (Function.uncurry X))
    (hv : Continuous (Function.uncurry v)) (hvper : ∀ s, IsTorusPeriodic (v s))
    (hχ : IsScalarTest χ) (hω₀ : Integrable ω₀ μT)
    (hinit : ∀ a ∈ torusBox, X 0 a = a)
    (hflow : ∀ a ∈ torusBox, ∀ s ∈ Icc 0 t,
      HasDerivAt (fun r => X r a) (v s (X s a)) s)
    (hpush : IsVorticityPushForward t ω₀ w X) :
    IntervalIntegrable (fun s => ∫ x in torusBox,
      w s x * transportTestDerivative v χ s x) volume 0 t ∧
    (∫ x in torusBox, w t x * χ x) = (∫ x in torusBox, w 0 x * χ x) +
      ∫ s in (0 : ℝ)..t, ∫ x in torusBox,
        w s x * transportTestDerivative v χ s x := by
  have hkernel : ∀ s, Continuous (transportTestDerivative v χ s) := fun s =>
    (continuous_transportTestDerivative hv hχ.1).comp (continuous_const.prodMk continuous_id)
  have hkernelper := isTorusPeriodic_transportTestDerivative hvper hχ.2
  have hpair : ∀ s ∈ Icc 0 t,
      (∫ a in torusBox, ω₀ a * transportTestDerivative v χ s (X s a)) =
        ∫ x in torusBox, w s x * transportTestDerivative v χ s x :=
    fun s hs => (hpush.pairing s hs _ (hkernel s) (hkernelper s)).symm
  have hL : IntervalIntegrable (fun s => ∫ a in torusBox,
      ω₀ a * transportTestDerivative v χ s (X s a)) volume 0 t := by
    exact intervalIntegrable_iff.mpr
      (integrable_lagrangian_testDerivative ht hX hv hχ.1 hω₀).integral_prod_left
  have hE : IntervalIntegrable (fun s => ∫ x in torusBox,
      w s x * transportTestDerivative v χ s x) volume 0 t := by
    apply hL.congr
    intro s hs
    have hs0 : s ∈ Ioc (0 : ℝ) t := by simpa only [uIoc_of_le ht] using hs
    exact hpair s ⟨hs0.1.le, hs0.2⟩
  have htime : (∫ s in (0 : ℝ)..t, ∫ a in torusBox,
      ω₀ a * transportTestDerivative v χ s (X s a)) =
      ∫ s in (0 : ℝ)..t, ∫ x in torusBox,
        w s x * transportTestDerivative v χ s x := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact hpair s (by simpa only [uIcc_of_le ht] using hs)
  have hzero : (∫ x in torusBox, w 0 x * χ x) = ∫ a in torusBox, ω₀ a * χ a := by
    rw [hpush.pairing 0 ⟨le_rfl, ht⟩ χ hχ.1.continuous hχ.2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with a ha
    rw [hinit a ha]
  refine ⟨hE, ?_⟩
  calc
    _ = ∫ a in torusBox, ω₀ a * χ (X t a) :=
      hpush.pairing t ⟨ht, le_rfl⟩ χ hχ.1.continuous hχ.2
    _ = (∫ a in torusBox, ω₀ a * χ a) +
        ∫ s in (0 : ℝ)..t, ∫ a in torusBox,
          ω₀ a * transportTestDerivative v χ s (X s a) :=
      lagrangian_label_integral ht hX hv hχ.1 hω₀ hinit hflow
    _ = _ := by rw [hzero, htime]

/-! ## Time-dependent scalar tests -/

/-- The full material derivative of a time-dependent scalar test. -/
def timeTransportTestDerivative (v : ℝ → R2 → R2) (χ : ℝ → R2 → ℝ)
    (s : ℝ) (x : R2) : ℝ :=
  deriv (fun r => χ r x) s + transportTestDerivative v (χ s) s x

theorem timeTransportTestDerivative_eq_fderiv {v : ℝ → R2 → R2}
    {χ : ℝ → R2 → ℝ} (hχ : Differentiable ℝ (Function.uncurry χ)) (s : ℝ) (x : R2) :
    timeTransportTestDerivative v χ s x =
      fderiv ℝ (Function.uncurry χ) (s, x) (1, v s x) := by
  have htime : HasDerivAt (fun r => χ r x)
      (fderiv ℝ (Function.uncurry χ) (s, x) (1, 0)) s := by
    have hpair : HasDerivAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : R2)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using
      (hχ (s, x)).hasFDerivAt.comp_hasDerivAt s hpair
  have hspace := (hχ (s, x)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right s x)
  have hspaceEq : fderiv ℝ (χ s) x (v s x) =
      fderiv ℝ (Function.uncurry χ) (s, x) (0, v s x) := by
    change fderiv ℝ ((Function.uncurry χ) ∘ (fun y : R2 => (s, y))) x (v s x) = _
    rw [hspace.fderiv]
    rfl
  have hvec : ((1 : ℝ), v s x) = ((1 : ℝ), (0 : R2)) + ((0 : ℝ), v s x) := by simp
  rw [hvec, map_add, ← htime.deriv, ← hspaceEq, fderiv_apply_eq_sum_pd]
  rfl

theorem continuous_timeTransportTestDerivative {v : ℝ → R2 → R2}
    {χ : ℝ → R2 → ℝ} (hv : Continuous (Function.uncurry v))
    (hχ : ContDiff ℝ ∞ (Function.uncurry χ)) :
    Continuous (Function.uncurry (timeTransportTestDerivative v χ)) := by
  have heq : (Function.uncurry (timeTransportTestDerivative v χ)) =
      fun p : ℝ × R2 => fderiv ℝ (Function.uncurry χ) p (1, v p.1 p.2) := by
    funext p
    exact timeTransportTestDerivative_eq_fderiv (hχ.differentiable (by simp)) p.1 p.2
  rw [heq]
  exact (hχ.continuous_fderiv (by simp)).clm_apply (continuous_const.prodMk hv)

theorem isTorusPeriodic_timeTransportTestDerivative {v : ℝ → R2 → R2}
    {χ : ℝ → R2 → ℝ} (hv : ∀ s, IsTorusPeriodic (v s))
    (hχ : Differentiable ℝ (Function.uncurry χ))
    (hχper : ∀ s, IsTorusPeriodic (χ s)) (s : ℝ) :
    IsTorusPeriodic (timeTransportTestDerivative v χ s) := by
  intro x j
  have heq : (fun p : ℝ × R2 =>
      (Function.uncurry χ) (p + (0, EuclideanSpace.single j (2 * Real.pi)))) =
      Function.uncurry χ := by
    funext p
    change χ (p.1 + 0) (p.2 + EuclideanSpace.single j (2 * Real.pi)) = χ p.1 p.2
    rw [add_zero]
    exact hχper p.1 p.2 j
  have hfd := fderiv_comp_add_right (𝕜 := ℝ) (f := Function.uncurry χ) (x := (s, x))
    ((0 : ℝ), EuclideanSpace.single j (2 * Real.pi))
  rw [heq] at hfd
  rw [timeTransportTestDerivative_eq_fderiv hχ, timeTransportTestDerivative_eq_fderiv hχ,
    hv s x j]
  have hp : (s, x) + ((0 : ℝ), EuclideanSpace.single j (2 * Real.pi)) =
      (s, x + EuclideanSpace.single j (2 * Real.pi)) := by simp
  rw [hp] at hfd
  rw [← hfd]

/-- Chain rule for an actual particle and a space-time scalar test. -/
theorem hasDerivAt_timeTest_along_flow {X v : ℝ → R2 → R2} {χ : ℝ → R2 → ℝ}
    (hχ : ContDiff ℝ ∞ (Function.uncurry χ)) (s : ℝ) (a : R2)
    (hflow : HasDerivAt (fun r => X r a) (v s (X s a)) s) :
    HasDerivAt (fun r => χ r (X r a))
      (timeTransportTestDerivative v χ s (X s a)) s := by
  have hc := ((hχ.differentiable (by simp) (s, X s a)).hasFDerivAt).comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk hflow)
  simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq,
    timeTransportTestDerivative_eq_fderiv (hχ.differentiable (by simp))] using hc

theorem timeTest_along_flow_integral {X v : ℝ → R2 → R2} {χ : ℝ → R2 → ℝ}
    {t : ℝ} (ht : 0 ≤ t)
    (hX : Continuous (Function.uncurry X))
    (hv : Continuous (Function.uncurry v)) (hχ : ContDiff ℝ ∞ (Function.uncurry χ))
    (a : R2) (hinit : X 0 a = a)
    (hflow : ∀ s ∈ Icc 0 t, HasDerivAt (fun r => X r a) (v s (X s a)) s) :
    χ t (X t a) - χ 0 a =
      ∫ s in (0 : ℝ)..t, timeTransportTestDerivative v χ s (X s a) := by
  have hcont : Continuous (fun s => timeTransportTestDerivative v χ s (X s a)) :=
    (continuous_timeTransportTestDerivative hv hχ).comp
      (continuous_id.prodMk (hX.comp (continuous_id.prodMk continuous_const)))
  symm
  convert intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_timeTest_along_flow hχ s a
      (hflow s (by simpa only [uIcc_of_le ht] using hs)))
    (hcont.intervalIntegrable 0 t) using 1
  rw [hinit]

/-- The complete time-dependent weighted-label identity, including both
endpoint pairings. -/
theorem lagrangian_time_label_integral {X v : ℝ → R2 → R2} {χ : ℝ → R2 → ℝ}
    {ω₀ : R2 → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hX : Continuous (Function.uncurry X))
    (hv : Continuous (Function.uncurry v)) (hχ : ContDiff ℝ ∞ (Function.uncurry χ))
    (hω₀ : Integrable ω₀ μT)
    (hinit : ∀ a ∈ torusBox, X 0 a = a)
    (hflow : ∀ a ∈ torusBox, ∀ s ∈ Icc 0 t,
      HasDerivAt (fun r => X r a) (v s (X s a)) s) :
    (∫ a in torusBox, ω₀ a * χ t (X t a)) = (∫ a in torusBox, ω₀ a * χ 0 a) +
      ∫ s in (0 : ℝ)..t, ∫ a in torusBox,
        ω₀ a * timeTransportTestDerivative v χ s (X s a) := by
  have hprod := integrable_weighted_label_kernel
    (K := fun s a => timeTransportTestDerivative v χ s (X s a)) ht
    ((continuous_timeTransportTestDerivative hv hχ).comp (continuous_fst.prodMk hX)) hω₀
  have hd : (∫ a in torusBox, ω₀ a * (χ t (X t a) - χ 0 a)) =
      ∫ s in (0 : ℝ)..t, ∫ a in torusBox,
        ω₀ a * timeTransportTestDerivative v χ s (X s a) := by
    calc
      _ = ∫ a in torusBox, ∫ s in (0 : ℝ)..t,
          ω₀ a * timeTransportTestDerivative v χ s (X s a) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_torusBox] with a ha
        rw [intervalIntegral.integral_const_mul,
          ← timeTest_along_flow_integral ht hX hv hχ a (hinit a ha) (hflow a ha)]
      _ = _ := (intervalIntegral_integral_swap hprod).symm
  have hend : Continuous (fun a : R2 => χ t (X t a)) :=
    hχ.continuous.comp (continuous_const.prodMk
      (hX.comp (continuous_const.prodMk continuous_id)))
  have hstart : Continuous (χ 0) :=
    hχ.continuous.comp (continuous_const.prodMk continuous_id)
  simp_rw [mul_sub] at hd
  rw [integral_sub (integrable_weight_continuous hω₀ hend)
    (integrable_weight_continuous hω₀ hstart)] at hd
  linarith

/-- A particle ODE and the push-forward law imply the complete weak
transport identity for time-dependent tests, before any support condition. -/
theorem flow_weak_vorticity_time_integral {X v : ℝ → R2 → R2}
    {χ : ℝ → R2 → ℝ} {ω₀ : R2 → ℝ} {w : ℝ → R2 → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hX : Continuous (Function.uncurry X))
    (hv : Continuous (Function.uncurry v)) (hvper : ∀ s, IsTorusPeriodic (v s))
    (hχ : ContDiff ℝ ∞ (Function.uncurry χ)) (hχper : ∀ s, IsTorusPeriodic (χ s))
    (hω₀ : Integrable ω₀ μT) (hinit : ∀ a ∈ torusBox, X 0 a = a)
    (hflow : ∀ a ∈ torusBox, ∀ s ∈ Icc 0 t,
      HasDerivAt (fun r => X r a) (v s (X s a)) s)
    (hpush : IsVorticityPushForward t ω₀ w X) :
    IntervalIntegrable (fun s => ∫ x in torusBox,
      w s x * timeTransportTestDerivative v χ s x) volume 0 t ∧
    (∫ x in torusBox, w t x * χ t x) = (∫ a in torusBox, ω₀ a * χ 0 a) +
      ∫ s in (0 : ℝ)..t, ∫ x in torusBox,
        w s x * timeTransportTestDerivative v χ s x := by
  have hkernel : ∀ s, Continuous (timeTransportTestDerivative v χ s) := fun s =>
    (continuous_timeTransportTestDerivative hv hχ).comp (continuous_const.prodMk continuous_id)
  have hkernelper := isTorusPeriodic_timeTransportTestDerivative hvper
    (hχ.differentiable (by simp)) hχper
  have hpair : ∀ s ∈ Icc 0 t,
      (∫ a in torusBox, ω₀ a * timeTransportTestDerivative v χ s (X s a)) =
        ∫ x in torusBox, w s x * timeTransportTestDerivative v χ s x :=
    fun s hs => (hpush.pairing s hs _ (hkernel s) (hkernelper s)).symm
  have hL : IntervalIntegrable (fun s => ∫ a in torusBox,
      ω₀ a * timeTransportTestDerivative v χ s (X s a)) volume 0 t :=
    intervalIntegrable_iff.mpr
      (integrable_weighted_label_kernel
        (K := fun s a => timeTransportTestDerivative v χ s (X s a)) ht
        ((continuous_timeTransportTestDerivative hv hχ).comp (continuous_fst.prodMk hX))
          hω₀).integral_prod_left
  have hE : IntervalIntegrable (fun s => ∫ x in torusBox,
      w s x * timeTransportTestDerivative v χ s x) volume 0 t := by
    apply hL.congr
    intro s hs
    have hs0 : s ∈ Ioc (0 : ℝ) t := by simpa only [uIoc_of_le ht] using hs
    exact hpair s ⟨hs0.1.le, hs0.2⟩
  have htime : (∫ s in (0 : ℝ)..t, ∫ a in torusBox,
      ω₀ a * timeTransportTestDerivative v χ s (X s a)) =
      ∫ s in (0 : ℝ)..t, ∫ x in torusBox,
        w s x * timeTransportTestDerivative v χ s x := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact hpair s (by simpa only [uIcc_of_le ht] using hs)
  refine ⟨hE, ?_⟩
  calc
    _ = ∫ a in torusBox, ω₀ a * χ t (X t a) :=
      hpush.pairing t ⟨ht, le_rfl⟩ _
        (hχ.continuous.comp (continuous_const.prodMk continuous_id)) (hχper t)
    _ = (∫ a in torusBox, ω₀ a * χ 0 a) +
        ∫ s in (0 : ℝ)..t, ∫ a in torusBox,
          ω₀ a * timeTransportTestDerivative v χ s (X s a) :=
      lagrangian_time_label_integral ht hX hv hχ hω₀ hinit hflow
    _ = _ := by rw [htime]

/-- Smooth scalar tests, periodic in space and vanishing before the final
time.  No transport equation is part of this test definition. -/
structure IsVorticityTest (T : ℝ) (χ : ℝ → R2 → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ (Function.uncurry χ)
  periodic : ∀ s, IsTorusPeriodic (χ s)
  support : ∃ T' < T, ∀ s ≥ T', ∀ x, χ s x = 0

/-- The genuine space-time weak vorticity equation, including the initial
term, follows from the particle equation and the signed push-forward law. -/
theorem flow_weak_vorticity_spacetime {X v : ℝ → R2 → R2}
    {χ : ℝ → R2 → ℝ} {ω₀ : R2 → ℝ} {w : ℝ → R2 → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hX : Continuous (Function.uncurry X))
    (hv : Continuous (Function.uncurry v)) (hvper : ∀ s, IsTorusPeriodic (v s))
    (hχ : IsVorticityTest T χ) (hω₀ : Integrable ω₀ μT)
    (hinit : ∀ a ∈ torusBox, X 0 a = a)
    (hflow : ∀ a ∈ torusBox, ∀ s ∈ Icc 0 T,
      HasDerivAt (fun r => X r a) (v s (X s a)) s)
    (hpush : IsVorticityPushForward T ω₀ w X) :
    IntervalIntegrable (fun s => ∫ x in torusBox, w s x *
      (deriv (fun r => χ r x) s + ∑ i : Fin 2, v s x i * pd i (χ s) x)) volume 0 T ∧
    (∫ s in (0 : ℝ)..T, ∫ x in torusBox, w s x *
      (deriv (fun r => χ r x) s + ∑ i : Fin 2, v s x i * pd i (χ s) x)) +
      (∫ a in torusBox, ω₀ a * χ 0 a) = 0 := by
  obtain ⟨hI, heq⟩ := flow_weak_vorticity_time_integral hT hX hv hvper
    hχ.smooth hχ.periodic hω₀ hinit hflow hpush
  obtain ⟨T', hT', hsupp⟩ := hχ.support
  have hterminal : (∫ x in torusBox, w T x * χ T x) = 0 := by
    simp only [hsupp T hT'.le, mul_zero, integral_zero]
  rw [hterminal] at heq
  refine ⟨?_, ?_⟩
  · simpa only [timeTransportTestDerivative, transportTestDerivative] using hI
  · have heq' := heq.symm
    rw [add_comm] at heq'
    simpa only [timeTransportTestDerivative, transportTestDerivative] using heq'

/-- An actual measure-preserving map and its measure-preserving a.e.
inverse construct the signed push-forward law.  In particular the density
is explicitly `ω₀ ∘ Y`; no weak transport identity is assumed.  For a
quotient flow, this applies to its fundamental-domain representative maps. -/
theorem IsVorticityPushForward.of_measurePreservingInverse
    {X Y : ℝ → R2 → R2} {ω₀ : R2 → ℝ} {T : ℝ}
    (hω₀ : Integrable ω₀ μT)
    (hX : ∀ s ∈ Icc 0 T, MeasurePreserving (X s) μT μT)
    (hY : ∀ s ∈ Icc 0 T, MeasurePreserving (Y s) μT μT)
    (hinv : ∀ s ∈ Icc 0 T, ∀ᵐ a ∂μT, Y s (X s a) = a) :
    IsVorticityPushForward T ω₀ (fun s x => ω₀ (Y s x)) X := by
  have hw : ∀ s ∈ Icc 0 T, Integrable (fun x => ω₀ (Y s x)) μT :=
    fun s hs => (hY s hs).integrable_comp_of_integrable hω₀
  refine ⟨hw, ?_⟩
  intro s hs χ hχ _
  have hg : Integrable (fun x => ω₀ (Y s x) * χ x) μT :=
    integrable_weight_continuous (hw s hs) hχ
  calc
    _ = ∫ x, ω₀ (Y s x) * χ x ∂Measure.map (X s) μT := by rw [(hX s hs).map_eq]
    _ = ∫ a in torusBox, ω₀ (Y s (X s a)) * χ (X s a) :=
      integral_map (hX s hs).aemeasurable (by rw [(hX s hs).map_eq]; exact hg.aestronglyMeasurable)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hinv s hs] with a ha
      rw [ha]

/-- The same construction for measurable invertible maps; preservation by
the inverse follows from preservation by the original map. -/
theorem IsVorticityPushForward.of_measurableEquiv
    (e : ℝ → R2 ≃ᵐ R2) {ω₀ : R2 → ℝ} {T : ℝ}
    (hω₀ : Integrable ω₀ μT) (he : ∀ s ∈ Icc 0 T, MeasurePreserving (e s) μT μT) :
    IsVorticityPushForward T ω₀ (fun s x => ω₀ ((e s).symm x)) (fun s a => e s a) := by
  apply IsVorticityPushForward.of_measurePreservingInverse hω₀ he
    (fun s hs => (he s hs).symm (e s))
  intro s _
  exact Filter.Eventually.of_forall fun a => (e s).symm_apply_apply a

end Euler2D

end
