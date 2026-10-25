module

public import RequestProject.Euler.BoundedEulerGeometry

/-!
# Area of genuine transported patches in the physical fundamental square

When a patch and its actual image stay in the square, torus area
preservation is precisely ordinary plane area preservation on that patch.
The proof uses the true lifted inverse and the lattice equivariance.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem preimage_patch_inter_box (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    {D : Set R2} (hDbox : D ⊆ torusBox) (himage : S.forward t '' D ⊆ torusBox) :
    ((torusWrap ∘ S.backward t) ⁻¹' D) ∩ torusBox = S.forward t '' D := by
  ext x
  constructor
  · rintro ⟨hxD, hxbox⟩
    change torusWrap (S.backward t x) ∈ D at hxD
    have hdF : S.forward t (torusWrap (S.backward t x)) ∈ torusBox :=
      himage ⟨_, hxD, rfl⟩
    have he : S.forward t (torusWrap (S.backward t x)) = x := by
      calc
        _ = torusWrap (S.forward t (torusWrap (S.backward t x))) :=
          (torusRep_torusProj hdF).symm
        _ = torusWrap (S.forward t (S.backward t x)) :=
          torusWrap_comp_torusWrap_of_lattice_equivariant (S.forward_lattice t ht) _
        _ = torusWrap x := congrArg torusWrap (S.forward_backward t ht x)
        _ = x := torusRep_torusProj hxbox
    exact ⟨_, hxD, he⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨?_, himage ⟨a, ha, rfl⟩⟩
    change torusWrap (S.backward t (S.forward t a)) ∈ D
    rw [S.backward_forward t ht a]
    simpa only [torusWrap, torusRep_torusProj (hDbox ha)] using ha

theorem volume_image_patch (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    {D : Set R2} (hD : MeasurableSet D) (hDbox : D ⊆ torusBox)
    (himage : S.forward t '' D ⊆ torusBox) :
    volume (S.forward t '' D) = volume D := by
  have hpre : MeasurableSet ((torusWrap ∘ S.backward t) ⁻¹' D) :=
    hD.preimage (S.backward_area t).measurable
  have hm := (S.backward_area t).measure_preimage hD.nullMeasurableSet
  change μT ((torusWrap ∘ S.backward t) ⁻¹' D) = μT D at hm
  rw [Measure.restrict_apply hpre, Measure.restrict_apply hD,
    S.preimage_patch_inter_box t ht hDbox himage, inter_eq_left.mpr hDbox] at hm
  exact hm

end BoundedEulerParticleSystem
end Euler2D

end
