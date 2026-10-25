module

public import RequestProject.Euler.BoundedEulerParticleMaps
public import RequestProject.Euler.FourfoldParticleSystem
public import RequestProject.Euler.FourfoldParticleEquationLimit

/-!
# Constructed fourfold-symmetric bounded-vorticity Euler systems

Actual symmetric smooth systems are selected before compactness.  The
common forward/inverse limit retains their rotation identities, and its
actual primitive supplies the original closed-interval particle equation.
The raw periodic scalar and its `L²` class are related only by a.e. equality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

structure IsFourfoldBoundedEulerParticleSystem {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) : Prop where
  forward : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
    S.forward t (torusQuarterTurn a) = torusQuarterTurn (S.forward t a)
  backward : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
    S.backward t (torusQuarterTurn a) = torusQuarterTurn (S.backward t a)
  velocity : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
    particleVelocityRepresentative f S.backward S.backward_area t (torusQuarterTurn x) =
      perpJ (particleVelocityRepresentative f S.backward S.backward_area t x)

namespace IsFourfoldBoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} {S : BoundedEulerParticleSystem f T}
    (hS : IsFourfoldBoundedEulerParticleSystem S)

include hS

theorem forward_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    S.forward t torusCenter = torusCenter := by
  apply eq_center_of_eq_torusQuarterTurn
  simpa only [torusQuarterTurn_center] using hS.forward t ht torusCenter

theorem backward_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    S.backward t torusCenter = torusCenter := by
  apply eq_center_of_eq_torusQuarterTurn
  simpa only [torusQuarterTurn_center] using hS.backward t ht torusCenter

theorem velocity_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    particleVelocityRepresentative f S.backward S.backward_area t torusCenter = 0 := by
  apply eq_zero_of_eq_perpJ
  simpa only [torusQuarterTurn_center] using hS.velocity t ht torusCenter

end IsFourfoldBoundedEulerParticleSystem

theorem exists_fourfoldBoundedEulerParticleSystem (f : Lp ℝ 2 μT)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    {T B : ℝ} (hT : 0 ≤ T) (hB0 : 0 ≤ B) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B) :
    ∃ S : BoundedEulerParticleSystem f T, IsFourfoldBoundedEulerParticleSystem S := by
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
  refine ⟨S, ?_, ?_, ?_⟩
  · intro t ht a
    rw [hSF ⟨t, ht⟩, hSF ⟨t, ht⟩]
    exact hFrot ⟨t, ht⟩ a
  · intro t ht a
    rw [hSY]
    exact hYrot t a
  · intro t ht x
    simpa only [hSY] using hVrot ⟨t, ht⟩ x

theorem exists_fourfoldBoundedVorticity_weakEuler (f : Lp ℝ 2 μT)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    {T B : ℝ} (hT : 0 ≤ T) (hmean : (∫ x in torusBox, f x) = 0)
    (hB0 : 0 ≤ B) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B) :
    ∃ S : BoundedEulerParticleSystem f T, IsFourfoldBoundedEulerParticleSystem S ∧
      IsWeakEulerSolution T (biotSavartL2 f) (particleVelocity f S.backward S.backward_area) := by
  obtain ⟨S, hS⟩ := exists_fourfoldBoundedEulerParticleSystem f hwf hwper hwrot hT hB0 hB
  exact ⟨S, hS, S.weakEuler hT hmean hB0 hB⟩

end Euler2D

end
