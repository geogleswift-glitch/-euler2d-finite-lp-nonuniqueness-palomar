module

public import RequestProject.Euler.WeakAux

/-!
# Stationary data, delayed solutions, and the reduction of the main theorem

Formalization of Section `cp:refinements` of the paper (*Energy and delayed solutions*):

* a stationary divergence-free datum `u₀` gives the constant weak solution;
* if `u` is a weak solution with a stationary datum `u₀` that departs from `u₀`, then the
  delayed solutions `u_θ(t) = u₀` for `t ≤ θ`, `u_θ(t) = u(t - θ)` for `t > θ` form an
  uncountable family of pairwise distinct weak solutions with the same datum and the same
  vorticity bound (Proposition `cp:prop:delays`, without the energy statement);
* the main theorem and its corollary follow from Proposition `cp:limit`.
-/

@[expose] public section

open MeasureTheory Real Filter Topology Set
open scoped ContDiff

namespace Euler2D

/-- `u₀` is a stationary weak Euler solution: `div(u₀ ⊗ u₀)` is a gradient, i.e.
`∫ (u₀ ⊗ u₀) : ∇ψ = 0` for every smooth periodic divergence-free field `ψ`. -/
def IsStationary (u₀ : L2T) : Prop :=
  ∀ ψ : R2 → R2, ContDiff ℝ ∞ ψ → IsTorusPeriodic ψ → (∀ x, pd 0 ψ x 0 + pd 1 ψ x 1 = 0) →
    ∫ x in torusBox, ∑ i, ∑ j, u₀ x i * u₀ x j * pd j ψ x i = 0

variable {T : ℝ} {φ : ℝ → R2 → R2}

lemma IsEulerTest.contDiff_one (h : IsEulerTest T φ) : ContDiff ℝ 1 (Function.uncurry φ) :=
  h.smooth.of_le (by exact_mod_cast le_top)

lemma IsEulerTest.slice_smooth (h : IsEulerTest T φ) (t : ℝ) : ContDiff ℝ ∞ (φ t) :=
  h.smooth.comp (contDiff_prodMk_right t)

lemma quad_sum_integral (hφ : ContDiff ℝ 1 (Function.uncurry φ)) (v : L2T) (t : ℝ) :
    ∫ x in torusBox, ∑ i, ∑ j, v x i * v x j * pd j (φ t) x i =
      ∑ i, ∑ j, ∫ x in torusBox, v x i * v x j * pd j (φ t) x i := by
  have hk2 : ∀ i j, Continuous fun x => pd j (φ t) x i := fun i j =>
    (continuous_pd hφ i j).comp (Continuous.prodMk_right t)
  have I2 : ∀ i j, Integrable (fun x => v x i * v x j * pd j (φ t) x i) μT := fun i j => by
    obtain ⟨C, hC⟩ := bound_on_box (hk2 i j)
    exact integrable_bilin v v i j (hk2 i j).aestronglyMeasurable hC
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => I2 i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => I2 i j]

lemma lin_sum_integral (hφ : ContDiff ℝ 1 (Function.uncurry φ)) (v : L2T) (t : ℝ) :
    ∫ x in torusBox, ∑ i, v x i * φ t x i = ∑ i, ∫ x in torusBox, v x i * φ t x i := by
  have hk : ∀ i, Continuous fun x => φ t x i := fun i =>
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
      (hφ.continuous.comp (Continuous.prodMk_right t))
  have I : ∀ i, Integrable (fun x => v x i * φ t x i) μT := fun i => by
    obtain ⟨C, hC⟩ := bound_on_box (hk i)
    exact integrable_lin v i (hk i).aestronglyMeasurable hC
  exact integral_finset_sum _ fun i _ => I i

/-- For a stationary datum, the weak integrand reduces to the time-derivative pairing. -/
lemma stationary_integrand (hφ : IsEulerTest T φ) {u₀ : L2T} (hs : IsStationary u₀) (t : ℝ) :
    ∫ x in torusBox, eulerIntegrand u₀ φ t x =
      ∑ i, ∫ x in torusBox, u₀ x i * deriv (fun s => φ s x i) t := by
  rw [integral_eulerIntegrand_eq hφ.contDiff_one, ← quad_sum_integral hφ.contDiff_one,
    hs (φ t) (hφ.slice_smooth t) (hφ.periodic t) (hφ.divFree t), add_zero]

lemma continuous_lin_time (hφ : ContDiff ℝ 1 (Function.uncurry φ)) (v : L2T) (i : Fin 2) :
    Continuous fun t => ∫ x in torusBox, v x i * deriv (fun s => φ s x i) t :=
  continuous_iff_continuousAt.2 fun _ =>
    continuousAt_lin (v := fun _ => v) continuousAt_const (continuous_deriv_time hφ i) i

/-- Time integral of the weak integrand of a stationary datum. -/
lemma stationary_time_integral (hφ : IsEulerTest T φ) {u₀ : L2T} (hs : IsStationary u₀)
    (a b : ℝ) :
    ∫ t in a..b, ∫ x in torusBox, eulerIntegrand u₀ φ t x =
      ∑ i, ∫ x in torusBox, u₀ x i * (φ b x i - φ a x i) := by
  simp_rw [stationary_integrand hφ hs]
  rw [intervalIntegral.integral_finset_sum fun i _ =>
    (continuous_lin_time hφ.contDiff_one u₀ i).intervalIntegrable a b]
  exact Finset.sum_congr rfl fun i _ => integral_time_pairing hφ.contDiff_one u₀ i a b

/-- A stationary divergence-free datum gives the constant weak Euler solution. -/
theorem stationary_isWeakSolution {u₀ : L2T} (hdiv : DivFree u₀)
    (hs : IsStationary u₀) : IsWeakEulerSolution T u₀ (fun _ => u₀) := by
  refine ⟨continuousOn_const, fun _ _ => hdiv, rfl, fun φ hφ => ?_⟩
  obtain ⟨T', hT'T, hT'⟩ := hφ.support
  rw [stationary_time_integral hφ hs, lin_sum_integral hφ.contDiff_one, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hφT : ∀ x, φ T x = 0 := hT' T hT'T.le
  simp only [hφT, PiLp.zero_apply, zero_sub, mul_neg]
  rw [integral_neg, neg_add_cancel]


/-- If two `L²`-continuous paths differ at an interior time, their space–time distance is
positive. -/
lemma spaceTimeDistSq_pos {T : ℝ} {v w : ℝ → L2T} (hv : ContinuousOn v (Icc 0 T))
    (hw : ContinuousOn w (Icc 0 T)) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) (hne : v t₀ ≠ w t₀) :
    0 < spaceTimeDistSq T v w := by
  set f : ℝ → ℝ := fun t => ‖v t - w t‖ ^ 2
  have hf : ContinuousOn f (Icc 0 T) := ((hv.sub hw).norm).pow 2
  have hpos : 0 < f t₀ := by
    have : v t₀ - w t₀ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hIcc : Icc 0 T ∈ 𝓝 t₀ := Icc_mem_nhds ht₀.1 ht₀.2
  have hcont : ContinuousAt f t₀ := hf.continuousAt hIcc
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hcont.eventually (lt_mem_nhds (half_lt_self hpos))) (Ioo_mem_nhds ht₀.1 ht₀.2))
  set ε := δ / 2
  have hε : 0 < ε := by positivity
  have hεδ : ε = δ / 2 := rfl
  have hsub : ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), f t₀ / 2 < f t ∧ t ∈ Ioo 0 T := by
    intro t ht
    have : t ∈ Metric.ball t₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    exact hball this
  have ha : 0 ≤ t₀ - ε := (hsub _ ⟨le_rfl, by linarith⟩).2.1.le
  have hb : t₀ + ε ≤ T := (hsub _ ⟨by linarith, le_rfl⟩).2.2.le
  unfold spaceTimeDistSq
  calc (0 : ℝ) < (t₀ + ε - (t₀ - ε)) * (f t₀ / 2) := by
        have : t₀ + ε - (t₀ - ε) = 2 * ε := by ring
        rw [this]; positivity
    _ = ∫ t in (t₀ - ε)..(t₀ + ε), f t₀ / 2 := by simp; ring
    _ ≤ ∫ t in (t₀ - ε)..(t₀ + ε), f t := by
        apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        · exact (hf.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc (by linarith)
        · intro t ht; exact (hsub t ht).1.le
    _ ≤ ∫ t in (0 : ℝ)..T, f t := by
        apply intervalIntegral.integral_mono_interval ha (by linarith) hb
        · exact Eventually.of_forall fun t => by positivity
        · exact hf.intervalIntegrable_of_Icc (ha.trans (by linarith))



/-- The extension `ū` of `u|_{[0,T]}` by constants outside `[0,T]`. -/
noncomputable def extendPath (hT : 0 ≤ T) (u : ℝ → L2T) : ℝ → L2T :=
  IccExtend hT (fun s : Icc (0 : ℝ) T => u s)

lemma extendPath_eq (hT : 0 ≤ T) (u : ℝ → L2T) {s : ℝ} (hs : s ∈ Icc 0 T) :
    extendPath hT u s = u s := by
  simp [extendPath, IccExtend_of_mem _ _ hs]

lemma extendPath_of_le (hT : 0 ≤ T) (u : ℝ → L2T) {s : ℝ} (hs : s ≤ 0) :
    extendPath hT u s = u 0 := by
  simp [extendPath, IccExtend_of_le_left _ _ hs]

lemma extendPath_mem (hT : 0 ≤ T) (u : ℝ → L2T) (s : ℝ) :
    ∃ r ∈ Icc 0 T, extendPath hT u s = u r :=
  ⟨projIcc 0 T hT s, (projIcc 0 T hT s).2, rfl⟩

lemma extendPath_continuous (hT : 0 ≤ T) {u : ℝ → L2T} (hu : ContinuousOn u (Icc 0 T)) :
    Continuous (extendPath hT u) :=
  hu.restrict.Icc_extend'

/-- The delayed path `u_θ(t) = ū(t - θ)`. -/
noncomputable def delayed (hT : 0 ≤ T) (u : ℝ → L2T) (θ : ℝ) : ℝ → L2T :=
  fun t => extendPath hT u (t - θ)


/-- The time-shifted test field `φ(· + θ)`. -/
def shiftTest (φ : ℝ → R2 → R2) (θ : ℝ) : ℝ → R2 → R2 := fun s x => φ (s + θ) x

lemma shiftTest_isEulerTest (hφ : IsEulerTest T φ) {θ : ℝ} (hθ : 0 ≤ θ) :
    IsEulerTest T (shiftTest φ θ) where
  smooth := by
    have : Function.uncurry (shiftTest φ θ) =
        Function.uncurry φ ∘ (fun p : ℝ × R2 => (p.1 + θ, p.2)) := rfl
    rw [this]
    exact hφ.smooth.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  periodic s := hφ.periodic (s + θ)
  divFree s x := hφ.divFree (s + θ) x
  support := by
    obtain ⟨T', hT'T, hT'⟩ := hφ.support
    exact ⟨T' - θ, by linarith, fun s hs x => hT' (s + θ) (by linarith) x⟩

lemma eulerIntegrand_shift (v : R2 → R2) (θ s : ℝ) (x : R2) :
    eulerIntegrand v (shiftTest φ θ) s x = eulerIntegrand v φ (s + θ) x := by
  unfold eulerIntegrand shiftTest
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [deriv_comp_add_const (f := fun r => φ r x i)]

lemma eulerIntegrand_vanish {T' : ℝ}
    (hT' : ∀ t ≥ T', ∀ x, φ t x = 0) (v : R2 → R2) {r : ℝ} (hr : T' < r) (x : R2) :
    eulerIntegrand v φ r x = 0 := by
  unfold eulerIntegrand
  have h1 : ∀ i, deriv (fun s => φ s x i) r = 0 := by
    intro i
    have : (fun s => φ s x i) =ᶠ[𝓝 r] fun _ => 0 := by
      filter_upwards [lt_mem_nhds hr] with s hs
      rw [hT' s hs.le x]; rfl
    rw [this.deriv_eq, deriv_const]
  have h2 : ∀ i j, pd j (φ r) x i = 0 := by
    intro i j
    have : φ r = fun _ => 0 := funext fun y => hT' r hr.le y
    simp [pd, this]
  simp [h1, h2]


lemma delayed_continuous (hT : 0 ≤ T) {u : ℝ → L2T} (hu : ContinuousOn u (Icc 0 T)) (θ : ℝ) :
    Continuous (delayed hT u θ) :=
  (extendPath_continuous hT hu).comp (continuous_id.sub continuous_const)

lemma lin_sub_integral (hφ : ContDiff ℝ 1 (Function.uncurry φ)) (v : L2T) (a b : ℝ) :
    ∑ i, ∫ x in torusBox, v x i * (φ b x i - φ a x i) =
      (∫ x in torusBox, ∑ i, v x i * φ b x i) - ∫ x in torusBox, ∑ i, v x i * φ a x i := by
  have hk : ∀ t i, Continuous fun x => φ t x i := fun t i =>
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
      (hφ.continuous.comp (Continuous.prodMk_right t))
  have I : ∀ t i, Integrable (fun x => v x i * φ t x i) μT := fun t i => by
    obtain ⟨C, hC⟩ := bound_on_box (hk t i)
    exact integrable_lin v i (hk t i).aestronglyMeasurable hC
  rw [lin_sum_integral hφ, lin_sum_integral hφ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [mul_sub]
  exact integral_sub (I b i) (I a i)

/-- The delayed path satisfies the weak formulation. -/
lemma delayed_weak (hT : 0 ≤ T) {u₀ : L2T} {u : ℝ → L2T} (hu : IsWeakEulerSolution T u₀ u)
    (hs : IsStationary u₀) {θ : ℝ} (hθ0 : 0 ≤ θ) (hφ : IsEulerTest T φ) :
    (∫ t in (0 : ℝ)..T, ∫ x in torusBox, eulerIntegrand (delayed hT u θ t) φ t x) +
      ∫ x in torusBox, ∑ i, u₀ x i * φ 0 x i = 0 := by
  obtain ⟨T', hT'T, hT'⟩ := hφ.support
  have hφ1 := hφ.contDiff_one
  set ψ := shiftTest φ θ
  have hψ : IsEulerTest T ψ := shiftTest_isEulerTest hφ hθ0
  have hψ1 := hψ.contDiff_one
  set F : ℝ → ℝ := fun t => ∫ x in torusBox, eulerIntegrand (delayed hT u θ t) φ t x
  set H : ℝ → ℝ := fun s => ∫ x in torusBox, eulerIntegrand (extendPath hT u s) ψ s x
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun t =>
    continuousAt_eulerIntegral hφ1 (delayed_continuous hT hu.continuous θ).continuousAt
  have hHc : Continuous H := continuous_iff_continuousAt.2 fun t =>
    continuousAt_eulerIntegral hψ1 (extendPath_continuous hT hu.continuous).continuousAt
  -- first piece
  have h1 : ∫ t in (0 : ℝ)..θ, F t =
      ∑ i, ∫ x in torusBox, u₀ x i * (φ θ x i - φ 0 x i) := by
    rw [← stationary_time_integral hφ hs]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hθ0] at ht
    simp only [F, delayed]
    rw [extendPath_of_le hT u (by linarith [ht.2]), hu.initial]
  -- second piece
  have h2 : ∫ t in θ..T, F t = ∫ s in (0 : ℝ)..(T - θ), H s := by
    have := intervalIntegral.integral_comp_add_right F θ (a := 0) (b := T - θ)
    rw [zero_add, sub_add_cancel] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [F, H, delayed, add_sub_cancel_right]
    exact integral_congr_ae (Eventually.of_forall fun x => (eulerIntegrand_shift _ θ s x).symm)
  have hψT : ∀ t ≥ T' - θ, ∀ x, ψ t x = 0 := fun t ht x => hT' (t + θ) (by linarith) x
  have h3 : ∫ s in (T - θ)..T, H s = 0 := by
    rw [← intervalIntegral.integral_zero (a := T - θ) (b := T) (μ := volume)]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by linarith)] at hs
    simp only [H]
    rw [← integral_zero R2 ℝ]
    exact integral_congr_ae (Eventually.of_forall fun x =>
      eulerIntegrand_vanish hψT _ (by linarith [hs.1]) x)
  have hw := hu.weak ψ hψ
  have h4 : ∫ t in (0 : ℝ)..T, ∫ x in torusBox, eulerIntegrand (u t) ψ t x =
      ∫ s in (0 : ℝ)..T, H s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hT] at hs
    simp only [H, extendPath_eq hT u hs]
  rw [h4, ← intervalIntegral.integral_add_adjacent_intervals (b := T - θ)
    (hHc.intervalIntegrable _ _) (hHc.intervalIntegrable _ _), h3, add_zero] at hw
  have hψ0 : ψ 0 = φ θ := by funext x; simp [ψ, shiftTest]
  rw [hψ0] at hw
  show (∫ t in (0 : ℝ)..T, F t) + _ = 0
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := θ)
    (hFc.intervalIntegrable _ _) (hFc.intervalIntegrable _ _), h1, h2,
    lin_sub_integral hφ1]
  linarith


/-- Each delayed path is a weak Euler solution with the same datum. -/
theorem delayed_isWeakSolution (hT : 0 ≤ T) {u₀ : L2T} {u : ℝ → L2T}
    (hu : IsWeakEulerSolution T u₀ u) (hs : IsStationary u₀) {θ : ℝ} (hθ : 0 ≤ θ) :
    IsWeakEulerSolution T u₀ (delayed hT u θ) where
  continuous := (delayed_continuous hT hu.continuous θ).continuousOn
  divFree t _ := by
    obtain ⟨r, hr, hr'⟩ := extendPath_mem hT u (t - θ)
    simp only [delayed, hr']
    exact hu.divFree r hr
  initial := by
    simp only [delayed]
    rw [extendPath_of_le hT u (by linarith), hu.initial]
  weak φ hφ := delayed_weak hT hu hs hθ hφ

/-- Delaying preserves the vorticity bound (with the same constant). -/
lemma delayed_curlBoundedBy (hT : 0 ≤ T) {u : ℝ → L2T} {p : ENNReal} {M : ℝ}
    (hc : CurlBoundedBy T p M u) (θ : ℝ) : CurlBoundedBy T p M (delayed hT u θ) := by
  intro t _
  obtain ⟨r, hr, hr'⟩ := extendPath_mem hT u (t - θ)
  simp only [delayed, hr']
  exact hc r hr

/-- **Proposition (delays, `cp:prop:delays`), without the energy statement.**
If `u₀` is a stationary datum and `u` is a weak solution from `u₀` with a vorticity bound which
departs from `u₀` at some time `t* ∈ (0,T)`, then there is an uncountable family of weak
solutions with datum `u₀` and the same vorticity bound `M`, pairwise distinct in `L²((0,T)×𝕋²)`. -/
theorem delayed_family (hT : 0 < T) {u₀ : L2T} (hs : IsStationary u₀) {u : ℝ → L2T}
    (hu : IsWeakEulerSolution T u₀ u) {p : ENNReal} {M : ℝ} (hc : CurlBoundedBy T p M u)
    {tstar : ℝ} (htstar : tstar ∈ Ioo 0 T) (hne : u tstar ≠ u₀) :
    ∃ S : Set ℝ, ¬ S.Countable ∧ ∃ U : ℝ → ℝ → L2T,
      (∀ θ ∈ S, IsWeakEulerSolution T u₀ (U θ) ∧ CurlBoundedBy T p M (U θ)) ∧
      ∀ θ₁ ∈ S, ∀ θ₂ ∈ S, θ₁ ≠ θ₂ → 0 < spaceTimeDistSq T (U θ₁) (U θ₂) := by
  have hT0 : 0 ≤ T := hT.le
  set A : Set ℝ := {t | t ∈ Icc 0 T ∧ u t ≠ u₀}
  have hAne : A.Nonempty := ⟨tstar, ⟨htstar.1.le, htstar.2.le⟩, hne⟩
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  set τ := sInf A
  have hτ0 : 0 ≤ τ := le_csInf hAne fun t ht => ht.1.1
  have hτT : τ < T := lt_of_le_of_lt (csInf_le hAbdd ⟨⟨htstar.1.le, htstar.2.le⟩, hne⟩) htstar.2
  -- before `τ`, the solution equals the datum
  have hbefore : ∀ r, r < τ → extendPath hT0 u r = u₀ := by
    intro r hr
    rcases le_or_gt r 0 with h | h
    · rw [extendPath_of_le hT0 u h, hu.initial]
    · have hrI : r ∈ Icc 0 T := ⟨h.le, by linarith⟩
      rw [extendPath_eq hT0 u hrI]
      by_contra hc
      exact (notMem_of_lt_csInf hr hAbdd) ⟨hrI, hc⟩
  refine ⟨Ico 0 (T - τ), by rw [Cardinal.Real.Ico_countable_iff]; linarith, delayed hT0 u,
    fun θ hθ => ⟨delayed_isWeakSolution hT0 hu hs hθ.1, delayed_curlBoundedBy hT0 hc θ⟩, ?_⟩
  -- distinctness: reduce to `θ₁ < θ₂`
  suffices key : ∀ θ₁ ∈ Ico 0 (T - τ), ∀ θ₂ ∈ Ico 0 (T - τ), θ₁ < θ₂ →
      0 < spaceTimeDistSq T (delayed hT0 u θ₁) (delayed hT0 u θ₂) by
    intro θ₁ h₁ θ₂ h₂ hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key θ₁ h₁ θ₂ h₂ h
    · have := key θ₂ h₂ θ₁ h₁ h
      have hsymm : spaceTimeDistSq T (delayed hT0 u θ₁) (delayed hT0 u θ₂) =
          spaceTimeDistSq T (delayed hT0 u θ₂) (delayed hT0 u θ₁) := by
        unfold spaceTimeDistSq
        congr 1; funext t; rw [norm_sub_rev]
      rwa [hsymm]
  intro θ₁ h₁ θ₂ h₂ h12
  set ε := min (θ₂ - θ₁) (T - θ₁ - τ)
  have hε : 0 < ε := lt_min (by linarith) (by linarith [h₁.2])
  obtain ⟨s, hsA, hs_lt⟩ := exists_lt_of_csInf_lt hAne (show τ < τ + ε by linarith)
  have hτs : τ ≤ s := csInf_le hAbdd hsA
  have hs0 : 0 < s := by
    rcases hsA.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hsA.2; rw [← h, hu.initial]
  have hsε1 : s < τ + (θ₂ - θ₁) := lt_of_lt_of_le hs_lt (by simp [ε])
  have hsε2 : s < T - θ₁ := by
    have : ε ≤ T - θ₁ - τ := min_le_right _ _
    linarith
  refine spaceTimeDistSq_pos (delayed_continuous hT0 hu.continuous θ₁).continuousOn
    (delayed_continuous hT0 hu.continuous θ₂).continuousOn (t₀ := θ₁ + s)
    ⟨by linarith [h₁.1], by linarith⟩ ?_
  simp only [delayed]
  rw [add_sub_cancel_left, extendPath_eq hT0 u hsA.1, hbefore _ (by linarith)]
  exact hsA.2


end Euler2D

end
