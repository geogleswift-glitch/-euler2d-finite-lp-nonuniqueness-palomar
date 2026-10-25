module

public import RequestProject.Euler.BoundedEulerExistence

/-! An explicit integral-flow construction retaining the actual forward
and inverse maps, so geometric properties pass to the returned witness. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

def boundedEulerParticleSystemWithMapsOfIntegralFlow (f : Lp ℝ 2 μT)
    {T B : ℝ} (hT : 0 ≤ T) (hB0 : 0 ≤ B) (hB : ∀ᵐ x ∂μT, ‖f x‖ ≤ B)
    (F : Icc (0 : ℝ) T → R2 → R2) (hFc : Continuous (Function.uncurry F))
    (Y : ℝ → R2 → R2) (hYc : Continuous (Function.uncurry Y))
    (hY : ∀ t, TorusAreaPreserving (Y t))
    (hFMP : ∀ t, TorusAreaPreserving (F t))
    (hFlat : ∀ t a k, F t (a + torusLatticeShift k) = F t a + torusLatticeShift k)
    (hYlat : ∀ t a k, Y t (a + torusLatticeShift k) = Y t a + torusLatticeShift k)
    (hFY : ∀ (t : Icc (0 : ℝ) T) a, F t (Y t a) = a)
    (hYF : ∀ (t : Icc (0 : ℝ) T) a, Y t (F t a) = a)
    (hInt : ∀ (t : Icc (0 : ℝ) T) a,
      F t a = a + ∫ s in (0 : ℝ)..(t : ℝ), clampedParticleDerivative hT
        (fun u x => particleVelocityRepresentative f Y hY u x) F s a) :
    BoundedEulerParticleSystem f T := by
  let V : Icc (0 : ℝ) T → R2 → R2 := fun t x => particleVelocityRepresentative f Y hY t x
  have hvfull : Continuous (Function.uncurry (particleVelocityRepresentative f Y hY)) :=
    continuous_particleVelocityRepresentative f (M := B) hB0 hB (Y := Y) hY hYc
  have hsub : Continuous (fun p : Icc (0 : ℝ) T × R2 => ((p.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hv : Continuous (Function.uncurry V) := (hvfull.comp hsub).congr (fun _ => rfl)
  let X := particleIntegralExtension hT V F
  have hXeq (t : Icc (0 : ℝ) T) (a : R2) : X t a = F t a :=
    particleIntegralExtension_eq hT hInt t a
  refine {
    forward := X
    backward := Y
    forward_continuous := continuous_particleIntegralExtension hT hv hFc
    backward_continuous := hYc
    backward_area := hY
    forward_area := ?_
    initial := particleIntegralExtension_zero hT V F
    forward_lattice := ?_
    backward_lattice := hYlat
    backward_forward := ?_
    forward_backward := ?_
    derivative := ?_
  }
  · intro t ht
    have he : X t = F ⟨t, ht⟩ := funext (hXeq ⟨t, ht⟩)
    rw [he]
    exact hFMP _
  · intro t ht a k
    rw [hXeq ⟨t, ht⟩, hXeq ⟨t, ht⟩]
    exact hFlat _ _ _
  · intro t ht a
    rw [hXeq ⟨t, ht⟩]
    exact hYF ⟨t, ht⟩ a
  · intro t ht a
    rw [hXeq ⟨t, ht⟩]
    exact hFY ⟨t, ht⟩ a
  · intro t ht a
    have hd := particleIntegralExtension_hasDerivAt_on_Icc hT hv hFc hInt ht a
    have hc : projIcc 0 T hT t = (⟨t, ht⟩ : Icc (0 : ℝ) T) :=
      Subtype.ext (congrArg Subtype.val (projIcc_of_mem hT ht))
    simpa only [particleVelocityExtension, hc, V] using hd

theorem exists_boundedEulerParticleSystem_of_integral_flow_with_maps (f : Lp ℝ 2 μT)
    {T B : ℝ} (hT : 0 ≤ T) (hB0 : 0 ≤ B) (hB : ∀ᵐ x ∂μT, ‖f x‖ ≤ B)
    (F : Icc (0 : ℝ) T → R2 → R2) (hFc : Continuous (Function.uncurry F))
    (Y : ℝ → R2 → R2) (hYc : Continuous (Function.uncurry Y))
    (hY : ∀ t, TorusAreaPreserving (Y t))
    (hFMP : ∀ t, TorusAreaPreserving (F t))
    (hFlat : ∀ t a k, F t (a + torusLatticeShift k) = F t a + torusLatticeShift k)
    (hYlat : ∀ t a k, Y t (a + torusLatticeShift k) = Y t a + torusLatticeShift k)
    (hFY : ∀ (t : Icc (0 : ℝ) T) a, F t (Y t a) = a)
    (hYF : ∀ (t : Icc (0 : ℝ) T) a, Y t (F t a) = a)
    (hInt : ∀ (t : Icc (0 : ℝ) T) a,
      F t a = a + ∫ s in (0 : ℝ)..(t : ℝ), clampedParticleDerivative hT
        (fun u x => particleVelocityRepresentative f Y hY u x) F s a) :
    ∃ S : BoundedEulerParticleSystem f T,
      (∀ (t : Icc (0 : ℝ) T) a, S.forward t a = F t a) ∧ S.backward = Y := by
  let S := boundedEulerParticleSystemWithMapsOfIntegralFlow f hT hB0 hB F hFc Y hYc
    hY hFMP hFlat hYlat hFY hYF hInt
  refine ⟨S, ?_, rfl⟩
  intro t a
  change particleIntegralExtension hT
    (fun r x => particleVelocityRepresentative f Y hY r x) F t a = F t a
  exact particleIntegralExtension_eq hT hInt t a

end Euler2D

end
