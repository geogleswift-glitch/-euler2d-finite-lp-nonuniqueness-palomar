module

public import RequestProject.Euler.TorusPhysicalLabelCommonField

/-! The same actual inner-label field in the complex coordinates of
the material contours. The translation by the torus centre is retained. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def physicalLabelComplexField (w : R2 → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  complexPhysicalPlane.symm (S.physicalLabelCommonField w t (complexTorusPoint z))

theorem physicalLabelComplexField_eq (w : R2 → ℝ) (t : ℝ) (z : ℂ) :
    S.physicalLabelComplexField w t z = velocityC (S.physicalComplexSource w t) z +
      planeComplexEquiv (S.correctionLabelField t (complexTorusPoint z)) := by
  apply complexPhysicalPlane.injective
  simp only [physicalLabelComplexField, LinearIsometryEquiv.apply_symm_apply, map_add,
    ← complexPhysicalPlane_symm_eq_planeComplexEquiv]
  rw [S.physicalComplexLabelVelocity_eq_raw_spatial]
  rfl

theorem exists_physicalLabelComplexField_bounds {w : R2 → ℝ} {M : ℝ}
    (hw : MemLp w 2 μT) (hwper : IsTorusPeriodic w) (hM : ∀ x, ‖w x‖ ≤ M) :
    ∃ MB CB : ℝ≥0,
      Continuous (Function.uncurry (S.physicalLabelComplexField w)) ∧
      (∀ t z, ‖S.physicalLabelComplexField w t z‖ ≤ MB) ∧
      (∀ t z v, ‖z - v‖ ≤ 1 / 2 →
        ‖S.physicalLabelComplexField w t z - S.physicalLabelComplexField w t v‖ ≤
          CB * logFlowModulus ‖z - v‖) ∧
      ∀ t, IsPlanarWeaklyDivergenceFree (fun x : R2 =>
        complexPhysicalPlane (S.physicalLabelComplexField w t (complexPhysicalPlane.symm x))) := by
  obtain ⟨MB, CB, hc, hb, hl, hd⟩ := S.exists_physicalLabelCommonField_bounds hw hwper hM
  have hct : Continuous (fun z : ℂ => complexTorusPoint z) :=
    complexPhysicalPlane.continuous.add continuous_const
  have harg : Continuous (fun p : ℝ × ℂ => (p.1, complexTorusPoint p.2)) :=
    continuous_fst.prodMk (hct.comp continuous_snd)
  have hcc : Continuous (Function.uncurry (S.physicalLabelComplexField w)) := by
    apply Continuous.comp (f := fun p : ℝ × ℂ =>
      S.physicalLabelCommonField w p.1 (complexTorusPoint p.2))
      (g := fun x : R2 => complexPhysicalPlane.symm x)
    · exact complexPhysicalPlane.symm.continuous
    · exact Continuous.comp (f := fun p : ℝ × ℂ => (p.1, complexTorusPoint p.2))
        (g := fun p : ℝ × R2 => S.physicalLabelCommonField w p.1 p.2) hc harg
  refine ⟨MB, CB, hcc, ?_, ?_, ?_⟩
  · intro t z
    simpa only [physicalLabelComplexField, LinearIsometryEquiv.norm_map] using
      hb t (complexTorusPoint z)
  · intro t z v hzv
    have he : ‖complexTorusPoint z - complexTorusPoint v‖ = ‖z - v‖ := by
      simp only [complexTorusPoint, add_sub_add_right_eq_sub, ← map_sub,
        LinearIsometryEquiv.norm_map]
    have hh := hl t (complexTorusPoint z) (complexTorusPoint v) (he.symm ▸ hzv)
    simpa only [physicalLabelComplexField, ← map_sub, LinearIsometryEquiv.norm_map, he] using hh
  · intro t ψ hψ hs
    simpa only [physicalLabelComplexField, complexTorusPoint,
      LinearIsometryEquiv.apply_symm_apply, sub_neg_eq_add] using
      planarWeakDivergenceFree_translate_kernel (hd t) hψ hs (-torusCenter)

end BoundedEulerParticleSystem
end Euler2D

end
