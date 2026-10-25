module

public import RequestProject.Euler.RegularizedApproximationLimit
public import RequestProject.Euler.RegularizedVelocityLimit
public import RequestProject.Euler.ParticleEquationLimit
public import RequestProject.Euler.BoundedLagrangianEuler

/-!
# Actual bounded-vorticity particle systems

The velocity is the constructed singular integral of the transported
vorticity. Area preservation, inverse maps and the particle equation are
properties of the actual witnesses used by the original weak formulation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

structure BoundedEulerParticleSystem (f : Lp ℝ 2 μT) (T : ℝ) where
  forward : ℝ → R2 → R2
  backward : ℝ → R2 → R2
  forward_continuous : Continuous (Function.uncurry forward)
  backward_continuous : Continuous (Function.uncurry backward)
  backward_area : ∀ t, TorusAreaPreserving (backward t)
  forward_area : ∀ t ∈ Icc (0 : ℝ) T, TorusAreaPreserving (forward t)
  initial : ∀ a, forward 0 a = a
  forward_lattice : ∀ t ∈ Icc (0 : ℝ) T, ∀ a k,
    forward t (a + torusLatticeShift k) = forward t a + torusLatticeShift k
  backward_lattice : ∀ t a k,
    backward t (a + torusLatticeShift k) = backward t a + torusLatticeShift k
  backward_forward : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, backward t (forward t a) = a
  forward_backward : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, forward t (backward t a) = a
  derivative : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
    HasDerivAt (fun s => forward s a)
      (particleVelocityRepresentative f backward backward_area t (forward t a)) t

theorem BoundedEulerParticleSystem.weakEuler {f : Lp ℝ 2 μT} {T B : ℝ}
    (S : BoundedEulerParticleSystem f T) (hT : 0 ≤ T)
    (hf : (∫ x in torusBox, f x) = 0) (hB0 : 0 ≤ B) (hB : ∀ᵐ x ∂μT, ‖f x‖ ≤ B) :
    IsWeakEulerSolution T (biotSavartL2 f) (particleVelocity f S.backward S.backward_area) := by
  apply weakEuler_of_kernel_particle_flow hT f hf hB0 hB S.backward_area
    S.backward_continuous S.forward_continuous S.forward_area _
    (fun a _ => S.initial a) (fun a _ t ht => S.derivative t ht a)
  intro t ht
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with a ha
  rw [torusWrap_comp_torusWrap_of_lattice_equivariant (S.backward_lattice t),
    S.backward_forward t ht a]
  exact torusRep_torusProj ha

theorem boundedEulerParticleSystem_of_integral_flow (f : Lp ℝ 2 μT)
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
    Nonempty (BoundedEulerParticleSystem f T) := by
  let V : Icc (0 : ℝ) T → R2 → R2 := fun t x => particleVelocityRepresentative f Y hY t x
  have hvfull : Continuous (Function.uncurry (particleVelocityRepresentative f Y hY)) :=
    continuous_particleVelocityRepresentative f (M := B) hB0 hB (Y := Y) hY hYc
  have hsub : Continuous (fun p : Icc (0 : ℝ) T × R2 => ((p.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hv : Continuous (Function.uncurry V) := (hvfull.comp hsub).congr (fun _ => rfl)
  let X := particleIntegralExtension hT V F
  have hXeq (t : Icc (0 : ℝ) T) (a : R2) : X t a = F t a :=
    particleIntegralExtension_eq hT hInt t a
  refine ⟨{
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
  }⟩
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

end Euler2D

end
