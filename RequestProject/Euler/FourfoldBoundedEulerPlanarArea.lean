module

public import RequestProject.Euler.FourfoldBoundedEulerConstruction
public import RequestProject.Euler.SmoothRegularizedPlanarArea
public import RequestProject.Euler.MeasurePreservingPairLimit

/-! The same fourfold finite Euler construction retains global planar
area for both of its actual maps. The original datum, equation and
common forward/inverse subsequence are preserved. -/

@[expose] public section

set_option maxHeartbeats 8000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_fourfoldBoundedEulerParticleSystem_with_planar_area (f : Lp ℝ 2 μT)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    {T B : ℝ} (hT : 0 ≤ T) (hB0 : 0 ≤ B) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B) :
    ∃ S : BoundedEulerParticleSystem f T, IsFourfoldBoundedEulerParticleSystem S ∧
      ∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
        MeasurePreserving (S.backward t) volume volume := by
  have hw : Integrable w μT :=
    ((Lp.memLp f).integrable (by norm_num)).congr hwf.symm
  have hwB : ∀ᵐ a ∂μT, ‖w a‖ ≤ B := by
    filter_upwards [hwf, hB] with a ha hba
    simpa only [ha] using hba
  have hex (n : ℕ) : ∃ C : ℝ≥0, ∃ S : SmoothRegularizedParticleSystem
      (fourfoldRegularizedTorusKernel (radialApproxScale n) (radialApproxScale_pos n)) w T C C,
      IsFourfoldParticleSystem S :=
    exists_fourfoldRegularizedTorusParticleSystem_with_symmetry hw hwper hwrot hT
      (radialApproxScale_pos n) (radialApproxScale_le_one n)
  choose C A hA using hex
  obtain ⟨F, G, hFc, hGc, hFMP, hGMP, _hF0, _hG0, hFlat, hGlat,
    hFG, hGF, φ, hφ, hFlim, hGlim⟩ :=
    uniform_subseq_fourfoldRegularizedParticleSystem_pair hT radialApproxScale radialApproxScale_pos
      radialApproxScale_le_one A hw.aestronglyMeasurable hB0 hwB
  have hFrot (t : Icc (0 : ℝ) T) (a : R2) :
      F (t, torusQuarterTurn a) = torusQuarterTurn (F (t, a)) := by
    have hleft := hFlim.tendsto_at (t, torusQuarterTurn a)
    have hright := (torusQuarterTurn_smooth.continuous.tendsto (F (t, a))).comp
      (hFlim.tendsto_at (t, a))
    exact tendsto_nhds_unique hleft
      (hright.congr' (Eventually.of_forall fun n => ((hA (φ n)).forward t t.property a).symm))
  have hGrot (t : Icc (0 : ℝ) T) (a : R2) :
      G (t, torusQuarterTurn a) = torusQuarterTurn (G (t, a)) := by
    have hleft := hGlim.tendsto_at (t, torusQuarterTurn a)
    have hright := (torusQuarterTurn_smooth.continuous.tendsto (G (t, a))).comp
      (hGlim.tendsto_at (t, a))
    exact tendsto_nhds_unique hleft
      (hright.congr' (Eventually.of_forall fun n => ((hA (φ n)).backward t t.property a).symm))
  let Y : ℝ → R2 → R2 := particleVelocityExtension hT (fun t a => G (t, a))
  have hYc : Continuous (Function.uncurry Y) := continuous_particleVelocityExtension hT hGc
  have hY (t : ℝ) : TorusAreaPreserving (Y t) := hGMP (projIcc 0 T hT t)
  have hYeq (t : Icc (0 : ℝ) T) (a : R2) : Y t a = G (t, a) := by
    dsimp only [Y, particleVelocityExtension]
    rw [projIcc_of_mem hT t.property]
  have hYlat (t : ℝ) (a : R2) (k : Fin 2 → ℤ) :
      Y t (a + torusLatticeShift k) = Y t a + torusLatticeShift k :=
    hGlat (projIcc 0 T hT t) a k
  have hYrot (t : ℝ) (a : R2) : Y t (torusQuarterTurn a) = torusQuarterTurn (Y t a) :=
    hGrot (projIcc 0 T hT t) a
  have hFY (t : Icc (0 : ℝ) T) (a : R2) : F (t, Y t a) = a := by
    rw [hYeq]
    exact hFG t a
  have hYF (t : Icc (0 : ℝ) T) (a : R2) : Y t (F (t, a)) = a :=
    (hYeq t (F (t, a))).trans (hGF t a)
  have hForward (t : Icc (0 : ℝ) T) (a : R2) :
      Tendsto (fun n => (A (φ n)).forward t a) atTop (𝓝 (F (t, a))) :=
    hFlim.tendsto_at (t, a)
  have hBackward (t : Icc (0 : ℝ) T) : ∀ᵐ a ∂μT,
      Tendsto (fun n => (A (φ n)).backward t a) atTop (𝓝 (Y t a)) :=
    Eventually.of_forall fun a => by
      simpa only [hYeq] using hGlim.tendsto_at (t, a)
  have hεlim : Tendsto radialApproxScale atTop (𝓝 (0 : ℝ)) :=
    (tendsto_nhdsWithin_iff.mp tendsto_radialApproxScale).1
  have hInt := fourfoldParticleSystem_subseq_integral_eq f hwf hT radialApproxScale
    radialApproxScale_pos radialApproxScale_le_one hεlim A hB0 hB φ hφ hY hForward hBackward
  have hVlim (t : Icc (0 : ℝ) T) : TendstoUniformly
      (fun n => (A (φ n)).velocity t) (particleVelocityRepresentative f Y hY t) atTop :=
    tendstoUniformly_fourfoldRegularizedParticleVelocity f hwf
      (fun n => radialApproxScale (φ n)) (fun n => radialApproxScale_pos (φ n))
      (hεlim.comp hφ.tendsto_atTop) (fun n => A (φ n)) hB0 hB t.property (hY t) (hBackward t)
  have hVrot (t : Icc (0 : ℝ) T) (x : R2) :
      particleVelocityRepresentative f Y hY t (torusQuarterTurn x) =
        perpJ (particleVelocityRepresentative f Y hY t x) := by
    have hleft := (hVlim t).tendsto_at (torusQuarterTurn x)
    have hright := (perpJL.continuous.tendsto (particleVelocityRepresentative f Y hY t x)).comp
      ((hVlim t).tendsto_at x)
    exact tendsto_nhds_unique hleft
      (hright.congr' (Eventually.of_forall fun n => ((hA (φ n)).velocity t t.property x).symm))
  obtain ⟨S, hSF, hSY⟩ := exists_boundedEulerParticleSystem_of_integral_flow_with_maps f hT hB0 hB
    (fun t a => F (t, a)) hFc Y hYc hY hFMP hFlat hYlat hFY hYF hInt
  refine ⟨S, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t ht a
    rw [hSF ⟨t, ht⟩, hSF ⟨t, ht⟩]
    exact hFrot ⟨t, ht⟩ a
  · intro t ht a
    rw [hSY]
    exact hYrot t a
  · intro t ht x
    simpa only [hSY] using hVrot ⟨t, ht⟩ x
  · intro t ht
    have hlimF : ∀ᵐ a ∂(volume : Measure R2),
        Tendsto (fun n => (A (φ n)).forward t a) atTop (𝓝 (F (⟨t, ht⟩, a))) :=
      ae_of_all _ (fun a => hFlim.tendsto_at (⟨t, ht⟩, a))
    have hlimG : ∀ᵐ a ∂(volume : Measure R2),
        Tendsto (fun n => (A (φ n)).backward t a) atTop (𝓝 (G (⟨t, ht⟩, a))) :=
      ae_of_all _ (fun a => hGlim.tendsto_at (⟨t, ht⟩, a))
    have hvol := measurePreserving_inverse_pair_of_ae_tendsto
      (fun n => ((A (φ n)).planar_area hT ht).1)
      (fun n => ((A (φ n)).planar_area hT ht).2)
      (hFc.comp (continuous_const.prodMk continuous_id)).measurable
      (hGc.comp (continuous_const.prodMk continuous_id)).measurable
      hlimF hlimG (fun a => hGF ⟨t, ht⟩ a) (fun a => hFG ⟨t, ht⟩ a)
    constructor
    · have he : S.forward t = fun a => F (⟨t, ht⟩, a) := funext (hSF ⟨t, ht⟩)
      rw [he]
      exact hvol.1
    · have he : S.backward t = fun a => G (⟨t, ht⟩, a) := by
        rw [hSY]
        exact funext (hYeq ⟨t, ht⟩)
      rw [he]
      exact hvol.2

end Euler2D

end