module

public import RequestProject.Euler.ScaledCellCurl

/-!
# The specified vorticity of the actual infinite velocity datum

A continuous linear map translates and restricts the original planar
vorticity series to the torus, and lowers its exponent to two. This keeps
the specified scalar series through the strong velocity limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

def scalarLpLowerToTwo {p : ENNReal} (hp : 2 ≤ p) (f : Lp ℝ p μT) : Lp ℝ 2 μT :=
  ((Lp.memLp f).mono_exponent hp).toLp f

lemma scalarLpLowerToTwo_ae {p : ENNReal} (hp : 2 ≤ p) (f : Lp ℝ p μT) :
    (scalarLpLowerToTwo hp f : R2 → ℝ) =ᵐ[μT] f :=
  ((Lp.memLp f).mono_exponent hp).coeFn_toLp

def scalarLpLowerConstant (p : ENNReal) : ℝ :=
  (μT univ ^ (1 / (2 : ℝ) - 1 / p.toReal)).toReal

lemma scalarLpLowerToTwo_norm_le {p : ENNReal} (hp : 2 ≤ p) (f : Lp ℝ p μT) :
    ‖scalarLpLowerToTwo hp f‖ ≤ scalarLpLowerConstant p * ‖f‖ := by
  have hexp : 0 ≤ 1 / (2 : ℝ) - 1 / p.toReal := by
    by_cases ht : p = ∞
    · simp [ht]
    have hpr : (2 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono ht hp
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpr
    linarith
  have hfin : eLpNorm f p μT * μT univ ^ (1 / (2 : ℝ) - 1 / p.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
      (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μT univ))
  rw [scalarLpLowerToTwo, Lp.norm_toLp]
  calc
    (eLpNorm f 2 μT).toReal ≤
        (eLpNorm f p μT * μT univ ^ (1 / (2 : ℝ) - 1 / p.toReal)).toReal := by
      apply ENNReal.toReal_mono hfin
      simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (Lp.aestronglyMeasurable f)
    _ = scalarLpLowerConstant p * ‖f‖ := by
      rw [ENNReal.toReal_mul]
      change ‖f‖ * scalarLpLowerConstant p = _
      ring

def scalarLpLowerToTwoCLM {p : ENNReal} [Fact (1 ≤ p)] (hp : 2 ≤ p) :
    Lp ℝ p μT →L[ℝ] Lp ℝ 2 μT :=
  LinearMap.mkContinuous
    { toFun := scalarLpLowerToTwo hp
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [scalarLpLowerToTwo_ae hp (f + g), Lp.coeFn_add f g,
          Lp.coeFn_add (scalarLpLowerToTwo hp f) (scalarLpLowerToTwo hp g),
          scalarLpLowerToTwo_ae hp f, scalarLpLowerToTwo_ae hp g] with x h0 h1 h2 h3 h4
        simp only [h0, h1, h2, h3, h4, Pi.add_apply]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [scalarLpLowerToTwo_ae hp (c • f), Lp.coeFn_smul c f,
          Lp.coeFn_smul c (scalarLpLowerToTwo hp f), scalarLpLowerToTwo_ae hp f]
          with x h0 h1 h2 h3
        simp only [h0, h1, h2, h3, Pi.smul_apply, RingHom.id_apply] }
    (scalarLpLowerConstant p) (scalarLpLowerToTwo_norm_le hp)

/-- Translation of a planar Lebesgue class followed by restriction to the
original coordinate fundamental square. -/
def centeredPlanarLp (p : ENNReal) [Fact (1 ≤ p)] :
    Lp ℝ p (volume : Measure R2) →L[ℝ] Lp ℝ p μT :=
  (LpToLpRestrictCLM R2 ℝ ℝ volume p torusBox).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (fun x : R2 => x - torusCenter)
      (measurePreserving_sub_right volume torusCenter)).toContinuousLinearMap

lemma centeredPlanarLp_ae {p : ENNReal} [Fact (1 ≤ p)] (f : Lp ℝ p (volume : Measure R2)) :
    (centeredPlanarLp p f : R2 → ℝ) =ᵐ[μT] fun x => f (x - torusCenter) := by
  exact (LpToLpRestrictCLM_coeFn ℝ torusBox
    (Lp.compMeasurePreserving (fun x : R2 => x - torusCenter)
      (measurePreserving_sub_right volume torusCenter) f)).trans
      (ae_restrict_of_ae (Lp.coeFn_compMeasurePreserving f
        (measurePreserving_sub_right volume torusCenter)))

def centeredPlaneToTorusL2 {p : ENNReal} [Fact (1 ≤ p)] (hp : 2 ≤ p) :
    Lp ℝ p (volume : Measure R2) →L[ℝ] Lp ℝ 2 μT :=
  (scalarLpLowerToTwoCLM hp).comp (centeredPlanarLp p)

lemma centeredPlaneToTorusL2_ae {p : ENNReal} [Fact (1 ≤ p)] (hp : 2 ≤ p)
    (f : Lp ℝ p (volume : Measure R2)) :
    (centeredPlaneToTorusL2 hp f : R2 → ℝ) =ᵐ[μT] fun x => f (x - torusCenter) :=
  (scalarLpLowerToTwo_ae hp (centeredPlanarLp p f)).trans (centeredPlanarLp_ae f)

def centeredCircularDatum {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (x : R2) : ℝ :=
  circularDatumLp (A₀ := A₀) (b := b) hR hρ hq (x - torusCenter)

lemma centeredCircularDatum_memLp {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) :
    MemLp (centeredCircularDatum (A₀ := A₀) (b := b) hR hρ hq) (ENNReal.ofReal q) μT :=
  ((Lp.memLp (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq)).comp_measurePreserving
    (measurePreserving_sub_right volume torusCenter)).mono_measure Measure.restrict_le_self

lemma centeredPlaneToTorusL2_datumTerm_ae {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (hp : 2 ≤ ENNReal.ofReal q) (j : ℕ) :
    (centeredPlaneToTorusL2 hp (datumTermLp (A₀ := A₀) (b := b) hR hρ hq j) : R2 → ℝ)
      =ᵐ[μT] fun x => datumTerm A₀ b R ρ j (x - torusCenter) :=
  (centeredPlaneToTorusL2_ae hp _).trans
    (ae_restrict_of_ae ((measurePreserving_sub_right volume torusCenter).quasiMeasurePreserving.ae_eq
      (datumTerm_memLp (A₀ := A₀) (b := b) hR hρ hq j).coeFn_toLp))

lemma IsCurl.add_L2 {u v : L2T} {w z : Lp ℝ 2 μT} (hu : IsCurl u w) (hv : IsCurl v z) :
    IsCurl (u + v : L2T) (w + z : Lp ℝ 2 μT) := by
  intro ψ hψ
  have hψmem := continuous_memLp_torus hψ.1.continuous 2
  have hpd (i : Fin 2) : Continuous (pd i ψ) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint (a : L2T) (i j : Fin 2) : Integrable (fun x => a x i * pd j ψ x) μT := by
    obtain ⟨C, hC⟩ := bound_on_box (hpd j)
    exact integrable_lin a i (hpd j).aestronglyMeasurable hC
  have hleft : (∫ x in torusBox, (w + z) x * ψ x) =
      (∫ x in torusBox, w x * ψ x) + ∫ x in torusBox, z x * ψ x := by
    calc
      _ = ∫ x in torusBox, w x * ψ x + z x * ψ x := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add w z] with x hx
        rw [hx]
        change (w x + z x) * ψ x = _
        ring
      _ = _ := integral_add ((Lp.memLp w).integrable_mul hψmem)
        ((Lp.memLp z).integrable_mul hψmem)
  have hright : (∫ x in torusBox, (u + v) x 0 * pd 1 ψ x - (u + v) x 1 * pd 0 ψ x) =
      (∫ x in torusBox, u x 0 * pd 1 ψ x - u x 1 * pd 0 ψ x) +
        ∫ x in torusBox, v x 0 * pd 1 ψ x - v x 1 * pd 0 ψ x := by
    calc
      _ = ∫ x in torusBox, (u x 0 * pd 1 ψ x - u x 1 * pd 0 ψ x) +
          (v x 0 * pd 1 ψ x - v x 1 * pd 0 ψ x) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add u v] with x hx
        rw [hx]
        simp only [Pi.add_apply, PiLp.add_apply]
        ring
      _ = _ := integral_add ((hint u 0 1).sub (hint u 1 0)) ((hint v 0 1).sub (hint v 1 0))
  rw [hleft, hu ψ hψ, hv ψ hψ, hright]

lemma isCurl_zero_L2 : IsCurl (0 : L2T) (0 : Lp ℝ 2 μT) := by
  have hraw : IsCurl (fun _ => (0 : R2)) (fun _ => (0 : ℝ)) := by
    intro ψ hψ
    simp
  exact hraw.congr_ae (Lp.coeFn_zero R2 2 μT).symm (Lp.coeFn_zero ℝ 2 μT).symm

lemma isCurl_sum_L2 {ι : Type*} (s : Finset ι) (v : ι → L2T) (w : ι → Lp ℝ 2 μT)
    (hc : ∀ i, IsCurl (v i) (w i)) :
    IsCurl (∑ i ∈ s, v i : L2T) (∑ i ∈ s, w i : Lp ℝ 2 μT) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using isCurl_zero_L2
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (hc i).add_L2 ih

lemma isCurl_velocityDatumPartialSumL2_centered {A₀ b R ρ q : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hp : 2 ≤ ENNReal.ofReal q) (N : ℕ) :
    IsCurl (velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N)
      (centeredPlaneToTorusL2 hp
        (∑ j ∈ Finset.range N, datumTermLp (A₀ := A₀) (b := b) hR hρ hq j)) := by
  unfold velocityDatumPartialSumL2
  rw [map_sum]
  apply isCurl_sum_L2
  intro j
  exact (isCurl_velocityDatumTermLp hR hR1 hρ hρ1 j).congr_ae (EventuallyEq.refl _ _)
    (centeredPlaneToTorusL2_datumTerm_ae hR hρ hq hp j).symm

/-- The strong infinite velocity datum has exactly the original circular
vorticity series, translated into the coordinate square. -/
theorem isCurl_velocityDatumL2 {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hq2 : 2 ≤ q)
    (hsmall : ρ ^ (2 / q) < b) :
    IsCurl (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ)
      (centeredCircularDatum (A₀ := A₀) (b := b) hR hρ hq) := by
  have hp : 2 ≤ ENNReal.ofReal q := by
    calc
      (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hq2
  have hv := tendsto_velocityDatumPartialSumL2 hA hb hR hR1 hρ hρ1
    (velocity_two_small_of_vorticity_small hρ hρ1 (by linarith : 1 ≤ q) hsmall)
  have hw := ((centeredPlaneToTorusL2 hp).continuous.tendsto
    (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq)).comp
      (tendsto_sum_datumTermLp hA hb hR hρ hq hsmall)
  have hcurl : IsCurl (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ)
      (centeredPlaneToTorusL2 hp (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq)) := by
    apply isCurl_of_tendsto_integrals hv
      (isCurl_velocityDatumPartialSumL2_centered hR hR1 hρ hρ1 hq hp)
    intro ψ hψ
    simp_rw [scalar_test_pairing_eq_inner _ hψ.1.continuous]
    exact hw.inner tendsto_const_nhds
  exact hcurl.congr_ae (EventuallyEq.refl _ _) (centeredPlaneToTorusL2_ae hp _)

lemma eLpNorm_centeredCircularDatum_le {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) :
    eLpNorm (centeredCircularDatum (A₀ := A₀) (b := b) hR hρ hq) (ENNReal.ofReal q) μT ≤
      eLpNorm (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq) (ENNReal.ofReal q) volume := by
  let f := circularDatumLp (A₀ := A₀) (b := b) hR hρ hq
  have hmeas : AEStronglyMeasurable (fun x : R2 => f x) volume := Lp.aestronglyMeasurable f
  calc
    eLpNorm (centeredCircularDatum (A₀ := A₀) (b := b) hR hρ hq) (ENNReal.ofReal q) μT ≤
        eLpNorm (fun x => f (x - torusCenter)) (ENNReal.ofReal q) volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = _ := eLpNorm_comp_measurePreserving hmeas (measurePreserving_sub_right volume torusCenter)

/-- The specified source keeps the paper's original geometric vorticity
bound after centering and restriction. -/
theorem norm_centeredCircularDatum_le {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q)
    (hsmall : ρ ^ (2 / q) < b) :
    (eLpNorm (centeredCircularDatum (A₀ := A₀) (b := b) hR hρ hq) (ENNReal.ofReal q) μT).toReal ≤
      (eLpNorm cellW (ENNReal.ofReal q) volume).toReal *
        (A₀ * R ^ (2 / q)) / (1 - ρ ^ (2 / q) / b) := by
  calc
    _ ≤ (eLpNorm (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq)
        (ENNReal.ofReal q) volume).toReal :=
      ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_centeredCircularDatum_le hR hρ hq)
    _ = ‖circularDatumLp (A₀ := A₀) (b := b) hR hρ hq‖ := rfl
    _ ≤ _ := by
      simpa only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, mul_one] using
        norm_circularDatumLp_sub_sum_le hA hb hR hρ hq hsmall 0

end Euler2D

end
