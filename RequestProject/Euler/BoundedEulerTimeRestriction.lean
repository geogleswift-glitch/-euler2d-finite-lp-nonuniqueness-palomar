module

public import RequestProject.Euler.TorusParticleCorrectionField

/-! Restrict the same actual torus particle system to a shorter time
interval. The maps and the actual Green correction are unchanged. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T D : ℝ} (S : BoundedEulerParticleSystem f T)

def restrictTime (hDT : D ≤ T) : BoundedEulerParticleSystem f D where
  forward := S.forward
  backward := S.backward
  forward_continuous := S.forward_continuous
  backward_continuous := S.backward_continuous
  backward_area := S.backward_area
  forward_area := fun t ht => S.forward_area t ⟨ht.1, ht.2.trans hDT⟩
  initial := S.initial
  forward_lattice := fun t ht => S.forward_lattice t ⟨ht.1, ht.2.trans hDT⟩
  backward_lattice := S.backward_lattice
  backward_forward := fun t ht => S.backward_forward t ⟨ht.1, ht.2.trans hDT⟩
  forward_backward := fun t ht => S.forward_backward t ⟨ht.1, ht.2.trans hDT⟩
  derivative := fun t ht => S.derivative t ⟨ht.1, ht.2.trans hDT⟩

@[simp] theorem restrictTime_forward (hDT : D ≤ T) : (S.restrictTime hDT).forward = S.forward := rfl

@[simp] theorem restrictTime_backward (hDT : D ≤ T) : (S.restrictTime hDT).backward = S.backward := rfl

@[simp] theorem restrictTime_correctionLabelField (hDT : D ≤ T) :
    (S.restrictTime hDT).correctionLabelField = S.correctionLabelField := rfl

end BoundedEulerParticleSystem
end Euler2D

end
