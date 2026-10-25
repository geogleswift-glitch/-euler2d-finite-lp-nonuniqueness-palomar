module

public import RequestProject.Euler.BoxFourierCompactness

/-!
# Bochner-measurable vorticity of the actual weak Euler solution

This file preserves the original `Euler2D.IsWeakEulerSolution` and
`Euler2D.IsCurl` definitions.  No regularity or measurability premise is added:
the velocity's existing `L²` continuity makes every Fourier coefficient of
its distributional curl continuous.  On finite-exponent `Lq`, the countable
Fourier-coordinate map is a continuous injection from a Polish space and
therefore a measurable embedding.  It follows that the pointwise curl
witnesses supplied by `CurlBounded` form a strongly measurable `Lq` curve.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Euler2D

attribute [local instance] instMeasureSpaceUnitAddCircle

/-- Inclusion from a larger to a smaller spatial exponent on the actual torus box. -/
def bochnerScalarLpLower {p q : ENNReal} (hpq : p ≤ q)
    (f : Lp ℝ q μT) : Lp ℝ p μT :=
  ((Lp.memLp f).mono_exponent hpq).toLp f

lemma bochnerScalarLpLower_ae {p q : ENNReal} (hpq : p ≤ q)
    (f : Lp ℝ q μT) :
    (bochnerScalarLpLower hpq f : R2 → ℝ) =ᵐ[μT] f :=
  ((Lp.memLp f).mono_exponent hpq).coeFn_toLp

def bochnerScalarLpLowerConstant (p q : ENNReal) : ℝ :=
  (μT univ ^ (1 / p.toReal - 1 / q.toReal)).toReal

lemma bochnerScalarLpLower_norm_le {p q : ENNReal} [Fact (1 ≤ p)]
    (hpq : p ≤ q) (hqfin : q ≠ ∞) (f : Lp ℝ q μT) :
    ‖bochnerScalarLpLower hpq f‖ ≤ bochnerScalarLpLowerConstant p q * ‖f‖ := by
  have hpfin : p ≠ ∞ := ne_top_of_le_ne_top hqfin hpq
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpfin
  have hpqr : p.toReal ≤ q.toReal := ENNReal.toReal_mono hqfin hpq
  have hexp : 0 ≤ 1 / p.toReal - 1 / q.toReal := by
    have hi := one_div_le_one_div_of_le hpr hpqr
    linarith
  have hfin : eLpNorm f q μT * μT univ ^ (1 / p.toReal - 1 / q.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
      (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μT univ))
  rw [bochnerScalarLpLower, Lp.norm_toLp]
  calc
    (eLpNorm f p μT).toReal ≤
        (eLpNorm f q μT * μT univ ^ (1 / p.toReal - 1 / q.toReal)).toReal := by
      apply ENNReal.toReal_mono hfin
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq (Lp.aestronglyMeasurable f)
    _ = bochnerScalarLpLowerConstant p q * ‖f‖ := by
      rw [ENNReal.toReal_mul]
      change ‖f‖ * bochnerScalarLpLowerConstant p q = _
      ring

/-- The finite-exponent inclusion is a continuous real linear map. -/
def bochnerScalarLpLowerCLM {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hqfin : q ≠ ∞) : Lp ℝ q μT →L[ℝ] Lp ℝ p μT :=
  LinearMap.mkContinuous
    { toFun := bochnerScalarLpLower hpq
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [bochnerScalarLpLower_ae hpq (f + g), Lp.coeFn_add f g,
          Lp.coeFn_add (bochnerScalarLpLower hpq f) (bochnerScalarLpLower hpq g),
          bochnerScalarLpLower_ae hpq f, bochnerScalarLpLower_ae hpq g]
          with x h0 h1 h2 h3 h4
        simp only [h0, h1, h2, h3, h4, Pi.add_apply]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [bochnerScalarLpLower_ae hpq (c • f), Lp.coeFn_smul c f,
          Lp.coeFn_smul c (bochnerScalarLpLower hpq f), bochnerScalarLpLower_ae hpq f]
          with x h0 h1 h2 h3
        simp only [h0, h1, h2, h3, Pi.smul_apply, RingHom.id_apply] }
    (bochnerScalarLpLowerConstant p q) (bochnerScalarLpLower_norm_le hpq hqfin)

lemma bochnerScalarLpLower_injective {p q : ENNReal} (hpq : p ≤ q) :
    Function.Injective (bochnerScalarLpLower (p := p) (q := q) hpq) := by
  intro f g hfg
  apply Lp.ext
  filter_upwards [bochnerScalarLpLower_ae hpq f, bochnerScalarLpLower_ae hpq g]
    with x hf hg
  exact hf.symm.trans ((congrArg (fun v : Lp ℝ p μT => v x) hfg).trans hg)

/-- Exponent lowering also preserves genuine Bochner membership. -/
lemma bochnerScalarLpLower_memLp {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {r p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hqfin : q ≠ ∞) {ω : α → Lp ℝ q μT}
    (hω : MemLp ω r ν) :
    MemLp (fun t => bochnerScalarLpLower hpq (ω t)) r ν :=
  (bochnerScalarLpLowerCLM hpq hqfin).comp_memLp' hω

/-- Changing a scalar vorticity representative almost everywhere preserves the
original distributional curl equation. -/
lemma bochner_isCurl_congr_ae {u : R2 → R2} {w v : R2 → ℝ}
    (hc : IsCurl u w) (hwv : w =ᵐ[μT] v) : IsCurl u v := by
  intro ψ hψ
  calc
    (∫ x in torusBox, v x * ψ x) = ∫ x in torusBox, w x * ψ x := by
      apply integral_congr_ae
      filter_upwards [hwv] with x hx
      rw [hx]
    _ = _ := hc ψ hψ

lemma bochnerScalarLpLower_isCurl {p q : ENNReal} (hpq : p ≤ q)
    {u : R2 → R2} {w : Lp ℝ q μT} (hc : IsCurl u w) :
    IsCurl u (bochnerScalarLpLower hpq w) :=
  bochner_isCurl_congr_ae hc (bochnerScalarLpLower_ae hpq w).symm

/-- Complexification of scalar real `L²` in the unchanged torus model. -/
def bochnerScalarComplexify : Lp ℝ 2 μT →L[ℝ] BoxFourierL2 :=
  Complex.ofRealCLM.compLpL 2 μT

lemma bochnerScalarComplexify_ae (f : Lp ℝ 2 μT) :
    (bochnerScalarComplexify f : R2 → ℂ) =ᵐ[μT] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

lemma bochnerScalarComplexify_injective : Function.Injective bochnerScalarComplexify := by
  intro f g hfg
  apply Lp.ext
  filter_upwards [bochnerScalarComplexify_ae f, bochnerScalarComplexify_ae g]
    with x hf hg
  apply Complex.ofReal_injective
  exact hf.symm.trans ((congrArg (fun v : BoxFourierL2 => v x) hfg).trans hg)

lemma bochnerScalarComplexify_lower_eq_boxVorticity {q : ENNReal} (hq2 : 2 ≤ q)
    (f : Lp ℝ q μT) :
    bochnerScalarComplexify (bochnerScalarLpLower hq2 f) =
      boxVorticity f ((Lp.memLp f).mono_exponent hq2) := by
  apply Lp.ext
  filter_upwards [bochnerScalarComplexify_ae (bochnerScalarLpLower hq2 f),
    bochnerScalarLpLower_ae hq2 f,
    coeFn_boxVorticity f ((Lp.memLp f).mono_exponent hq2)] with x h0 h1 h2
  exact h0.trans ((congrArg Complex.ofReal h1).trans h2.symm)

/-- Countably many complex Fourier coordinates determine a real `Lq` vorticity. -/
def bochnerFourierCoordinates {q : ENNReal} (hq2 : 2 ≤ q)
    (f : Lp ℝ q μT) (k : Fin 2 → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff
    (torusL2Equiv (bochnerScalarComplexify (bochnerScalarLpLower hq2 f))) k

lemma bochner_mFourierCoeff_continuous (k : Fin 2 → ℤ) :
    Continuous (fun f : FourierL2 => UnitAddTorus.mFourierCoeff f k) := by
  simp_rw [← UnitAddTorus.mFourierBasis_repr, HilbertBasis.repr_apply_apply]
  exact continuous_const.inner continuous_id

lemma bochnerFourierCoordinates_continuous {q : ENNReal} [Fact (1 ≤ q)]
    (hq2 : 2 ≤ q) (hqfin : q ≠ ∞) : Continuous (bochnerFourierCoordinates hq2) := by
  apply continuous_pi
  intro k
  exact (bochner_mFourierCoeff_continuous k).comp
    (torusL2Equiv.continuous.comp (bochnerScalarComplexify.continuous.comp
      (bochnerScalarLpLowerCLM hq2 hqfin).continuous))

lemma bochnerFourierCoordinates_injective {q : ENNReal} (hq2 : 2 ≤ q) :
    Function.Injective (bochnerFourierCoordinates hq2) := by
  intro f g hfg
  apply bochnerScalarLpLower_injective hq2
  apply bochnerScalarComplexify_injective
  apply torusL2Equiv.injective
  apply UnitAddTorus.mFourierBasis.repr.injective
  ext k
  simpa only [UnitAddTorus.mFourierBasis_repr, bochnerFourierCoordinates] using
    congrFun hfg k

lemma bochnerFourierCoordinates_of_curl {q : ENNReal} (hq2 : 2 ≤ q)
    (u : L2T) (w : Lp ℝ q μT) (hc : IsCurl u w) (k : Fin 2 → ℤ) :
    bochnerFourierCoordinates hq2 w k =
      Complex.I * ((k 0 : ℂ) *
        UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 1 u)) k -
        (k 1 : ℂ) *
        UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 0 u)) k) := by
  unfold bochnerFourierCoordinates
  rw [bochnerScalarComplexify_lower_eq_boxVorticity]
  exact (lifted_curl_identity u w ((Lp.memLp w).mono_exponent hq2) hc k).symm

/-- The original every-time curl bound and the velocity's existing continuity
give an actual Bochner `L∞` curve, with the original curl equation at every
time in the closed interval.  The theorem needs no positivity assumption on
`T`; an empty interval causes no exception. -/
theorem exists_bochner_vorticity_of_continuous_curlBounded
    {T : ℝ} {q : ENNReal} (hq2 : 2 ≤ q) (hqfin : q ≠ ∞)
    {u : ℝ → L2T} (hu : ContinuousOn u (Icc 0 T)) (hc : CurlBounded T q u) :
    letI : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq2⟩
    ∃ ω : ℝ → Lp ℝ q μT,
      StronglyMeasurable ω ∧
      MemLp ω ∞ (volume.restrict (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, IsCurl (u t) (ω t) := by
  classical
  letI : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq2⟩
  letI : Fact (q ≠ ∞) := ⟨hqfin⟩
  letI : MeasurableSpace (Lp ℝ q μT) := borel _
  letI : BorelSpace (Lp ℝ q μT) := ⟨rfl⟩
  let J := Icc (0 : ℝ) T
  obtain ⟨M, hM⟩ := hc
  have hchoose : ∀ t : J, ∃ w : Lp ℝ q μT,
      IsCurl (u t) w ∧ ‖w‖ ≤ M := by
    intro t
    obtain ⟨w, hw, hcurl, hnorm⟩ := hM t t.property
    refine ⟨hw.toLp w, bochner_isCurl_congr_ae hcurl hw.coeFn_toLp.symm, ?_⟩
    simpa only [Lp.norm_toLp] using hnorm
  choose W hWcurl hWbound using hchoose
  have huc : Continuous (fun t : J => u t) :=
    continuousOn_iff_continuous_restrict.mp hu
  have hFW : Continuous (fun t : J => bochnerFourierCoordinates hq2 (W t)) := by
    apply continuous_pi
    intro k
    have hcoord (j : Fin 2) : Continuous (fun t : J =>
        UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord j (u t))) k) :=
      (bochner_mFourierCoeff_continuous k).comp
        (torusL2Equiv.continuous.comp ((boxComplexCoord j).continuous.comp huc))
    have hright : Continuous (fun t : J =>
        Complex.I * ((k 0 : ℂ) *
          UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 1 (u t))) k -
          (k 1 : ℂ) *
          UnitAddTorus.mFourierCoeff (torusL2Equiv (boxComplexCoord 0 (u t))) k)) :=
      continuous_const.mul
        ((continuous_const.mul (hcoord 1)).sub (continuous_const.mul (hcoord 0)))
    exact hright.congr (fun t =>
      (bochnerFourierCoordinates_of_curl hq2 (u t) (W t) (hWcurl t) k).symm)
  have hWmeas : Measurable W :=
    ((bochnerFourierCoordinates_continuous hq2 hqfin).measurableEmbedding
      (bochnerFourierCoordinates_injective hq2)).measurable_comp_iff.mp hFW.measurable
  have hWsm : StronglyMeasurable W := hWmeas.stronglyMeasurable
  let ω : ℝ → Lp ℝ q μT :=
    Function.extend (Subtype.val : J → ℝ) W (fun _ => 0)
  have hωeq (t : J) : ω t = W t :=
    Subtype.coe_injective.extend_apply W (fun _ => 0) t
  have hωsm : StronglyMeasurable ω :=
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).stronglyMeasurable_extend
      hWsm stronglyMeasurable_const
  letI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.2 isCompact_Icc.measure_lt_top.ne
  have hωmem : MemLp ω ∞ (volume.restrict (Icc 0 T)) := by
    apply MemLp.of_bound hωsm.aestronglyMeasurable M
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hωeq ⟨t, ht⟩]
    exact hWbound ⟨t, ht⟩
  refine ⟨ω, hωsm, hωmem, ?_⟩
  intro t ht
  rw [hωeq ⟨t, ht⟩]
  exact hWcurl ⟨t, ht⟩

/-- Named bridge for the exact original weak Euler solution and real finite
spatial exponent at least two. -/
theorem exists_bochner_vorticity_of_weakEuler
    {T q : ℝ} (hq : 2 ≤ q) {u₀ : L2T} {u : ℝ → L2T}
    (hu : IsWeakEulerSolution T u₀ u) (hc : CurlBounded T (ENNReal.ofReal q) u) :
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨by
        have h1q : (1 : ℝ) ≤ q := le_trans (by norm_num) hq
        simpa using ENNReal.ofReal_le_ofReal h1q⟩
    ∃ ω : ℝ → Lp ℝ (ENNReal.ofReal q) μT,
      StronglyMeasurable ω ∧
      MemLp ω ∞ (volume.restrict (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, IsCurl (u t) (ω t) := by
  exact exists_bochner_vorticity_of_continuous_curlBounded
    (by simpa using ENNReal.ofReal_le_ofReal hq) ENNReal.ofReal_ne_top hu.continuous hc

/-- The same actual vorticity may be lowered continuously to every smaller
finite spatial exponent at least one, including the endpoint one. -/
theorem exists_bochner_vorticity_of_weakEuler_lowerExponent
    {T p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hq : 2 ≤ q)
    {u₀ : L2T} {u : ℝ → L2T} (hu : IsWeakEulerSolution T u₀ u)
    (hc : CurlBounded T (ENNReal.ofReal q) u) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    ∃ ω : ℝ → Lp ℝ (ENNReal.ofReal p) μT,
      StronglyMeasurable ω ∧
      MemLp ω ∞ (volume.restrict (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, IsCurl (u t) (ω t) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  letI : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal (le_trans hp hpq)⟩
  have hpqE : ENNReal.ofReal p ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hpq
  obtain ⟨ω, hωsm, hωmem, hωcurl⟩ := exists_bochner_vorticity_of_weakEuler hq hu hc
  refine ⟨fun t => bochnerScalarLpLower hpqE (ω t),
    (bochnerScalarLpLowerCLM hpqE ENNReal.ofReal_ne_top).continuous.comp_stronglyMeasurable
      hωsm,
    bochnerScalarLpLower_memLp hpqE ENNReal.ofReal_ne_top hωmem, ?_⟩
  intro t ht
  exact bochnerScalarLpLower_isCurl hpqE (hωcurl t ht)

end Euler2D
