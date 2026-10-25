module

public import RequestProject.Euler.TorusTransportContinuity
public import RequestProject.Euler.TorusSmoothKernelBounds

/-!
# Strong `L²` stability of actual area-preserving transport

The initial scalar is an arbitrary fundamental-domain `L²` class.  Smooth
periodic Fourier density and the exact transport isometry avoid any
continuity assumption on the discontinuous fundamental-domain wrapping map.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff ENNReal

namespace Euler2D

lemma scalarL2_integral_norm_sq (f : Lp ℝ 2 μT) :
    (∫ x in torusBox, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq f, MeasureTheory.L2.inner_def]
  congr 1
  funext x
  rw [real_inner_self_eq_norm_sq]

lemma torusTransportL2_scalarTest_ae {p : R2 → ℝ} (hp : IsScalarTest p)
    (Y : R2 → R2) (hY : TorusAreaPreserving Y) :
    (torusTransportL2 ((continuous_memLp_torus hp.1.continuous 2).toLp p) Y hY : R2 → ℝ)
      =ᵐ[μT] fun x => p (Y x) := by
  have hpull := hY.quasiMeasurePreserving.ae_eq_comp
    (continuous_memLp_torus hp.1.continuous 2).coeFn_toLp
  filter_upwards [torusTransportL2_ae
    ((continuous_memLp_torus hp.1.continuous 2).toLp p) Y hY, hpull] with x hx hpull
  simp only [Function.comp_apply] at hpull
  exact hx.trans (hpull.trans (hp.2.eq_torusWrap (Y x)))

/-- Dominated convergence for the actual transported smooth periodic
classes. The lifted particle maps need not be continuous or measurable. -/
theorem tendsto_torusTransportL2_scalarTest {p : R2 → ℝ} (hp : IsScalarTest p)
    {Y : ℕ → R2 → R2} {Z : R2 → R2}
    (hY : ∀ n, TorusAreaPreserving (Y n)) (hZ : TorusAreaPreserving Z)
    (hlim : ∀ᵐ x ∂μT, Tendsto (fun n => Y n x) atTop (𝓝 (Z x))) :
    Tendsto (fun n => torusTransportL2
      ((continuous_memLp_torus hp.1.continuous 2).toLp p) (Y n) (hY n)) atTop
      (𝓝 (torusTransportL2 ((continuous_memLp_torus hp.1.continuous 2).toLp p) Z hZ)) := by
  let P : Lp ℝ 2 μT := (continuous_memLp_torus hp.1.continuous 2).toLp p
  let U (n : ℕ) := torusTransportL2 P (Y n) (hY n)
  let V := torusTransportL2 P Z hZ
  have hU (n : ℕ) : (U n : R2 → ℝ) =ᵐ[μT] fun x => p (Y n x) :=
    torusTransportL2_scalarTest_ae hp (Y n) (hY n)
  have hV : (V : R2 → ℝ) =ᵐ[μT] fun x => p (Z x) :=
    torusTransportL2_scalarTest_ae hp Z hZ
  obtain ⟨C, hC⟩ := exists_global_bound_of_continuous_periodic hp.1.continuous hp.2
  let F (n : ℕ) (x : R2) : ℝ := ‖U n x - V x‖ ^ 2
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μT :=
    (((Lp.aestronglyMeasurable (U n)).sub (Lp.aestronglyMeasurable V)).norm).pow 2
  have hdom (n : ℕ) : ∀ᵐ x ∂μT, ‖F n x‖ ≤ (2 * (C : ℝ)) ^ 2 := by
    filter_upwards [hU n, hV] with x hx hz
    have hb : ‖U n x - V x‖ ≤ 2 * (C : ℝ) := by
      rw [hx, hz]
      exact (norm_sub_le _ _).trans (by linarith [hC (Y n x), hC (Z x)])
    dsimp only [F]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
  have hUall : ∀ᵐ x ∂μT, ∀ n, U n x = p (Y n x) := ae_all_iff.mpr hU
  have hpoint : ∀ᵐ x ∂μT, Tendsto (fun n => F n x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hUall, hV, hlim] with x hx hz hlim
    have hpLim := (hp.1.continuous.tendsto (Z x)).comp hlim
    dsimp only [F]
    simp_rw [hx, hz]
    simpa only [Function.comp_def, sub_self, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((hpLim.sub_const (p (Z x))).norm).pow 2
  have hint := tendsto_integral_of_dominated_convergence (μ := μT) (F := F)
    (f := fun _ => (0 : ℝ)) (fun _ => (2 * (C : ℝ)) ^ 2) hmeas
    (integrable_const _) hdom hpoint
  have hsq (n : ℕ) : ‖U n - V‖ ^ 2 = ∫ x in torusBox, F n x := by
    rw [← scalarL2_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (U n) V] with x hx
    rw [hx, Pi.sub_apply]
  have hn2 : Tendsto (fun n => ‖U n - V‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq, integral_zero] using hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn2.sqrt

/-- Actual smooth periodic scalar density in the original physical `L²`. -/
lemma exists_scalarTest_L2_dist_lt (w : Lp ℝ 2 μT) {ε : ℝ} (hε : 0 < ε) :
    ∃ (p : R2 → ℝ) (hp : IsScalarTest p),
      dist ((continuous_memLp_torus hp.1.continuous 2).toLp p) w < ε := by
  let p (N : ℕ) : R2 → ℝ := boxScalarFourierPolynomial N (boxVorticity w (Lp.memLp w))
  have hp (N : ℕ) : IsScalarTest (p N) := isScalarTest_boxScalarFourierPolynomial N _
  let P (N : ℕ) : Lp ℝ 2 μT := (continuous_memLp_torus (hp N).1.continuous 2).toLp (p N)
  have hP : Tendsto P atTop (𝓝 w) := by
    have hself : (Lp.memLp w).toLp (w : R2 → ℝ) = w := by
      apply Lp.ext
      exact (Lp.memLp w).coeFn_toLp
    have hrep (N : ℕ) : P N = boxRealPart
        (boxScalarFourierTrunc N (boxVorticity w (Lp.memLp w))) := by
      apply Lp.ext
      exact (continuous_memLp_torus (hp N).1.continuous 2).coeFn_toLp.trans
        ((coeFn_boxRealPart _).trans (coeFn_boxScalarFourierTrunc_re N _)).symm
    change Tendsto (fun N => P N) atTop (𝓝 w)
    simp_rw [hrep]
    simpa only [hself] using tendsto_boxRealPart_scalarTrunc w (Lp.memLp w)
  obtain ⟨N, hN⟩ := ((Metric.tendsto_nhds.mp hP) ε hε).exists
  exact ⟨p N, hp N, hN⟩

/-- Strong stability of transport for every actual scalar `L²` datum. -/
theorem tendsto_torusTransportL2_of_ae_tendsto (w : Lp ℝ 2 μT)
    {Y : ℕ → R2 → R2} {Z : R2 → R2}
    (hY : ∀ n, TorusAreaPreserving (Y n)) (hZ : TorusAreaPreserving Z)
    (hlim : ∀ᵐ x ∂μT, Tendsto (fun n => Y n x) atTop (𝓝 (Z x))) :
    Tendsto (fun n => torusTransportL2 w (Y n) (hY n)) atTop
      (𝓝 (torusTransportL2 w Z hZ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨p, hp, hclose⟩ := exists_scalarTest_L2_dist_lt w (show 0 < ε / 3 by linarith)
  let P := (continuous_memLp_torus hp.1.continuous 2).toLp p
  have hP := tendsto_torusTransportL2_scalarTest hp hY hZ hlim
  have hnear := (Metric.tendsto_nhds.mp hP) (ε / 3) (by linarith)
  filter_upwards [hnear] with n hn
  have hb := dist_triangle4 (torusTransportL2 w (Y n) (hY n))
    (torusTransportL2 P (Y n) (hY n)) (torusTransportL2 P Z hZ) (torusTransportL2 w Z hZ)
  rw [torusTransportL2_dist, torusTransportL2_dist, dist_comm w P] at hb
  exact hb.trans_lt (by linarith)

/-- Both the scalar datum and the area-preserving particle map may vary. -/
theorem tendsto_torusTransportL2_of_tendsto_initial_of_ae_tendsto
    {w : ℕ → Lp ℝ 2 μT} {w₀ : Lp ℝ 2 μT} (hw : Tendsto w atTop (𝓝 w₀))
    {Y : ℕ → R2 → R2} {Z : R2 → R2}
    (hY : ∀ n, TorusAreaPreserving (Y n)) (hZ : TorusAreaPreserving Z)
    (hlim : ∀ᵐ x ∂μT, Tendsto (fun n => Y n x) atTop (𝓝 (Z x))) :
    Tendsto (fun n => torusTransportL2 (w n) (Y n) (hY n)) atTop
      (𝓝 (torusTransportL2 w₀ Z hZ)) := by
  have hfixed := tendsto_torusTransportL2_of_ae_tendsto w₀ hY hZ hlim
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hnearW := (Metric.tendsto_nhds.mp hw) (ε / 2) (by linarith)
  have hnearY := (Metric.tendsto_nhds.mp hfixed) (ε / 2) (by linarith)
  filter_upwards [hnearW, hnearY] with n hnW hnY
  have hb := dist_triangle (torusTransportL2 (w n) (Y n) (hY n))
    (torusTransportL2 w₀ (Y n) (hY n)) (torusTransportL2 w₀ Z hZ)
  rw [torusTransportL2_dist] at hb
  exact hb.trans_lt (by linarith)

end Euler2D

end
