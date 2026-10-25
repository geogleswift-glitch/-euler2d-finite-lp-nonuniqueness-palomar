module

public import RequestProject.Euler.TorusTransport
public import RequestProject.Euler.SmoothFlowVolume

/-!
# Plane volume preservation descends to the physical square torus

The square is proved to be an actual fundamental domain for the integer
lattice action.  A volume-preserving lattice-equivariant map pulls it
back to another fundamental domain.  Equality of invariant-set measures
on these two domains proves area preservation of the wrapped map.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology Function
open scoped ENNReal Pointwise NNReal ContDiff

namespace Euler2D

namespace TorusFlowVolumeConstruction

abbrev Lattice := Fin 2 → ℤ

instance latticeAddAction : AddAction Lattice R2 where
  vadd k x := x + torusLatticeShift k
  zero_vadd x := by
    change x + torusLatticeShift 0 = x
    rw [torusLatticeShift_zero, add_zero]
  add_vadd k l x := by
    change x + torusLatticeShift (k + l) = (x + torusLatticeShift l) + torusLatticeShift k
    rw [torusLatticeShift_add]
    abel

lemma lattice_vadd (k : Lattice) (x : R2) : k +ᵥ x = x + torusLatticeShift k := rfl

instance latticeMeasurableConstVAdd : MeasurableConstVAdd Lattice R2 :=
  ⟨fun _ => measurable_id.add_const _⟩

instance latticeVolumeInvariant : VAddInvariantMeasure Lattice R2 (volume : Measure R2) where
  measure_preimage_vadd k _s hs :=
    (measurePreserving_add_right volume (torusLatticeShift k)).measure_preimage hs.nullMeasurableSet

/-- Every point has exactly one lattice translate in the half-open
physical square, including points on its faces. -/
lemma existsUnique_lattice_translate_mem_torusBox (x : R2) :
    ∃! k : Lattice, x + torusLatticeShift k ∈ torusBox := by
  let k : Lattice := fun i => -⌊x i / (2 * π)⌋
  have hP : (0 : ℝ) < 2 * π := by positivity
  refine ⟨k, ?_, ?_⟩
  · intro i
    have he : (x + torusLatticeShift k) i = (2 * π) * Int.fract (x i / (2 * π)) := by
      simp only [PiLp.add_apply, torusLatticeShift_apply, k, Int.cast_neg, Int.fract]
      field_simp
      ring
    rw [he]
    exact ⟨mul_nonneg hP.le (Int.fract_nonneg _), by
      simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one (x i / (2 * π))) hP⟩
  · intro l hl
    funext i
    have hi : x i / (2 * π) + (l i : ℝ) ∈ Ico (0 : ℝ) 1 := by
      have hli := hl i
      have he : x i / (2 * π) + (l i : ℝ) = (x + torusLatticeShift l) i / (2 * π) := by
        simp only [PiLp.add_apply, torusLatticeShift_apply]
        field_simp
      rw [he]
      exact ⟨div_nonneg hli.1 hP.le, (div_lt_one hP).mpr hli.2⟩
    have hfloor := Int.floor_eq_zero_iff.mpr hi
    rw [Int.floor_add_intCast] at hfloor
    change l i = -⌊x i / (2 * π)⌋
    omega

theorem isAddFundamentalDomain_torusBox :
    IsAddFundamentalDomain Lattice torusBox (volume : Measure R2) :=
  IsAddFundamentalDomain.mk' measurableSet_torusBox.nullMeasurableSet
    existsUnique_lattice_translate_mem_torusBox

/-- The preimage square is a genuine fundamental domain for a
measure-preserving map commuting with every lattice translation. -/
theorem isAddFundamentalDomain_preimage {X : R2 → R2}
    (hX : MeasurePreserving X (volume : Measure R2) volume)
    (hlat : ∀ x k, X (x + torusLatticeShift k) = X x + torusLatticeShift k) :
    IsAddFundamentalDomain Lattice (X ⁻¹' torusBox) (volume : Measure R2) := by
  apply isAddFundamentalDomain_torusBox.preimage_of_equiv hX.quasiMeasurePreserving
    (e := id) bijective_id
  intro k x
  exact hlat x k

end TorusFlowVolumeConstruction

/-- Wrapping a lattice-equivariant map gives a genuinely periodic map. -/
lemma isTorusPeriodic_torusWrap_comp_of_lattice_equivariant {X : R2 → R2}
    (hlat : ∀ x k, X (x + torusLatticeShift k) = X x + torusLatticeShift k) :
    IsTorusPeriodic (torusWrap ∘ X) := by
  intro x i
  change torusWrap (X (x + EuclideanSpace.single i (2 * π))) = torusWrap (X x)
  rw [← torusLatticeShift_single, hlat, isTorusPeriodic_torusWrap.eq_add_torusLatticeShift]

lemma torusWrap_comp_torusWrap_of_lattice_equivariant {X : R2 → R2}
    (hlat : ∀ x k, X (x + torusLatticeShift k) = X x + torusLatticeShift k) (x : R2) :
    torusWrap (X (torusWrap x)) = torusWrap (X x) :=
  (isTorusPeriodic_torusWrap_comp_of_lattice_equivariant hlat).eq_torusWrap x

/-- Plane volume preservation and actual lattice equivariance imply
area preservation on the torus.  No PDE or torus preservation hypothesis
is used to prove the conclusion. -/
theorem torusAreaPreserving_of_measurePreserving_lattice_equivariant {X : R2 → R2}
    (hX : MeasurePreserving X (volume : Measure R2) volume)
    (hlat : ∀ x k, X (x + torusLatticeShift k) = X x + torusLatticeShift k) :
    TorusAreaPreserving X := by
  have hm : Measurable (torusWrap ∘ X) := measurable_torusWrap.comp hX.measurable
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hm hB]
  let A : Set R2 := torusWrap ⁻¹' B
  have hA : MeasurableSet A := measurable_torusWrap hB
  have hC : MeasurableSet (X ⁻¹' A) := hX.measurable hA
  have hInv (k : TorusFlowVolumeConstruction.Lattice) :
      (fun x : R2 => k +ᵥ x) ⁻¹' (X ⁻¹' A) = X ⁻¹' A := by
    ext x
    change torusWrap (X (x + torusLatticeShift k)) ∈ B ↔ torusWrap (X x) ∈ B
    rw [hlat, isTorusPeriodic_torusWrap.eq_add_torusLatticeShift]
  have hFD := TorusFlowVolumeConstruction.isAddFundamentalDomain_preimage hX hlat
  have hdomains := TorusFlowVolumeConstruction.isAddFundamentalDomain_torusBox.measure_set_eq
    hFD hC hInv
  have hinter : (X ⁻¹' A) ∩ (X ⁻¹' torusBox) = X ⁻¹' (A ∩ torusBox) := rfl
  have hwrapBox : A ∩ torusBox = B ∩ torusBox := by
    ext x
    constructor
    · rintro ⟨hxA, hxBox⟩
      refine ⟨?_, hxBox⟩
      change torusWrap x ∈ B at hxA
      simpa only [torusWrap, torusRep_torusProj hxBox] using hxA
    · rintro ⟨hxB, hxBox⟩
      refine ⟨?_, hxBox⟩
      change torusWrap x ∈ B
      simpa only [torusWrap, torusRep_torusProj hxBox] using hxB
  change μT (X ⁻¹' A) = μT B
  rw [Measure.restrict_apply hC, Measure.restrict_apply hB]
  rw [hdomains, hinter, hX.measure_preimage (hA.inter measurableSet_torusBox).nullMeasurableSet,
    hwrapBox]

/-- The actual forward particle flow of a bounded smooth periodic
divergence-free velocity preserves the physical torus area. -/
theorem torusAreaPreserving_boundedParticleForward {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : ContDiff ℝ 1 (Function.uncurry v)) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    (hper : ∀ t, IsTorusPeriodic (v t)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    TorusAreaPreserving (boundedParticleForward hv hT t) :=
  torusAreaPreserving_of_measurePreserving_lattice_equivariant
    (measurePreserving_boundedParticleForward hv hC1 hT hdiv ht)
    (boundedParticleForward_lattice_equivariant hv hT hper t)

/-- The actual inverse particle flow also preserves the torus area. -/
theorem torusAreaPreserving_boundedParticleBackward {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : ContDiff ℝ 1 (Function.uncurry v)) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    (hper : ∀ t, IsTorusPeriodic (v t)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    TorusAreaPreserving (boundedParticleBackward hv hT t) :=
  torusAreaPreserving_of_measurePreserving_lattice_equivariant
    (measurePreserving_boundedParticleBackward hv hC1 hT hdiv ht)
    (boundedParticleBackward_lattice_equivariant hv hT hper t)

/-- The inverse flow already clamps its source time into the physical
interval, so its torus area preservation holds at every real time. -/
theorem torusAreaPreserving_boundedParticleBackward_all {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : ContDiff ℝ 1 (Function.uncurry v)) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    (hper : ∀ t, IsTorusPeriodic (v t)) (t : ℝ) :
    TorusAreaPreserving (boundedParticleBackward hv hT t) := by
  let τ := projIcc 0 T hT t
  have he : boundedParticleBackward hv hT t = boundedParticleBackward hv hT (τ : ℝ) := by
    funext a
    unfold boundedParticleBackward
    rw [projIcc_of_mem hT τ.property]
  rw [he]
  exact torusAreaPreserving_boundedParticleBackward hv hC1 hT hdiv hper τ.property

/-- The actual signed vorticity defined using the inverse particle map
satisfies the push-forward identity for every continuous periodic test. -/
theorem isVorticityPushForward_boundedParticleForward {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : ContDiff ℝ 1 (Function.uncurry v)) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    (hper : ∀ t, IsTorusPeriodic (v t)) {w₀ : R2 → ℝ} (hw₀ : Integrable w₀ μT) :
    IsVorticityPushForward T w₀
      (fun t x => w₀ (torusWrap (boundedParticleBackward hv hT t x)))
      (boundedParticleForward hv hT) := by
  apply IsVorticityPushForward.of_torusInverse hw₀
    (fun _ ht => torusAreaPreserving_boundedParticleForward hv hC1 hT hdiv hper ht)
    (fun _ ht => torusAreaPreserving_boundedParticleBackward hv hC1 hT hdiv hper ht)
  intro t ht
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with a ha
  rw [torusWrap_comp_torusWrap_of_lattice_equivariant
    (boundedParticleBackward_lattice_equivariant hv hT hper t),
    boundedParticleBackward_forward hv hT ht]
  exact torusRep_torusProj ha

end Euler2D

end
