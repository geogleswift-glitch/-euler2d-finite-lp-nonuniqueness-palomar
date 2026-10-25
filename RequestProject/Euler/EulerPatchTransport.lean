module

public import RequestProject.Euler.BoundedEulerPatchTransport
public import RequestProject.Euler.FourfoldBoundedEulerConstruction
public import RequestProject.Euler.CircularCell

/-!
# Actual patch densities transported by the constructed Euler flow

Identifying wrapped torus transport with a physical image patch requires
both the source and its actual image to stay in the fundamental square.
These support hypotheses are explicit in every such identification.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def transportedScalar (w : R2 → ℝ) (t : ℝ) (x : R2) : ℝ :=
  w (torusWrap (S.backward t x))

theorem isTorusPeriodic_transportedScalar (w : R2 → ℝ) (t : ℝ) :
    IsTorusPeriodic (S.transportedScalar w t) := by
  intro x i
  exact congrArg w ((isTorusPeriodic_torusWrap_comp_of_lattice_equivariant
    (S.backward_lattice t)) x i)

theorem transportedScalar_eq_of_periodic {w : R2 → ℝ} (hw : IsTorusPeriodic w)
    (t : ℝ) (x : R2) : S.transportedScalar w t x = w (S.backward t x) :=
  hw.eq_torusWrap _

theorem aestronglyMeasurable_transportedScalar {w : R2 → ℝ}
    (hw : AEStronglyMeasurable w μT) (t : ℝ) :
    AEStronglyMeasurable (S.transportedScalar w t) μT :=
  hw.comp_quasiMeasurePreserving (S.backward_area t).quasiMeasurePreserving

theorem memLp_transportedScalar {w : R2 → ℝ} {p : ENNReal} (hw : MemLp w p μT) (t : ℝ) :
    MemLp (S.transportedScalar w t) p μT := hw.comp_measurePreserving (S.backward_area t)

theorem norm_transportedScalar_ae_le {w : R2 → ℝ} {B : ℝ}
    (hw : ∀ᵐ x ∂μT, ‖w x‖ ≤ B) (t : ℝ) :
    ∀ᵐ x ∂μT, ‖S.transportedScalar w t x‖ ≤ B :=
  (S.backward_area t).quasiMeasurePreserving.ae hw

theorem torusTransportL2_ae_transportedScalar (g : Lp ℝ 2 μT) {w : R2 → ℝ}
    (hwg : w =ᵐ[μT] (g : R2 → ℝ)) (t : ℝ) :
    (torusTransportL2 g (S.backward t) (S.backward_area t) : R2 → ℝ) =ᵐ[μT]
      S.transportedScalar w t := by
  have hpull := (S.backward_area t).quasiMeasurePreserving.ae_eq_comp hwg
  filter_upwards [torusTransportL2_ae g (S.backward t) (S.backward_area t), hpull] with x hx hw
  simp only [Function.comp_apply] at hw
  exact hx.trans hw.symm

theorem particleCurlL2_ae_transportedScalar {w : R2 → ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (t : ℝ) :
    (particleCurlL2 f S.backward S.backward_area t : R2 → ℝ) =ᵐ[μT]
      S.transportedScalar w t :=
  S.torusTransportL2_ae_transportedScalar f hwf t

theorem particleVelocityRepresentative_eq_raw (w : R2 → ℝ)
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (t : ℝ) (x : R2) :
    particleVelocityRepresentative f S.backward S.backward_area t x =
      torusKernelVelocity (S.transportedScalar w t) x := by
  unfold particleVelocityRepresentative torusKernelVelocity
  apply integral_congr_ae
  filter_upwards [S.particleCurlL2_ae_transportedScalar hwf t] with y hy
  rw [hy]

theorem isCurl_particleVelocity_transportedScalar {w : R2 → ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (hmean : (∫ x in torusBox, f x) = 0) (t : ℝ) :
    IsCurl (particleVelocity f S.backward S.backward_area t) (S.transportedScalar w t) := by
  have hc := isCurl_biotSavartL2 (particleCurlL2 f S.backward S.backward_area t)
    ((integral_particleCurlL2 f S.backward S.backward_area t).trans hmean)
  exact hc.congr_ae (EventuallyEq.refl _ _) (S.particleCurlL2_ae_transportedScalar hwf t)

theorem measurableSet_image_patch (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    {D : Set R2} (hD : MeasurableSet D) : MeasurableSet (S.forward t '' D) := by
  rw [S.image_eq_preimage_backward t ht D]
  exact hD.preimage (S.backward_continuous.comp (continuous_const.prodMk continuous_id)).measurable

/-- The two support conditions are needed for this physical image formula. -/
theorem indicator_wrapped_backward (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    {D : Set R2} (hDbox : D ⊆ torusBox) (himage : S.forward t '' D ⊆ torusBox)
    (c : ℝ) {x : R2} (hx : x ∈ torusBox) :
    D.indicator (fun _ => c) (torusWrap (S.backward t x)) =
      (S.forward t '' D).indicator (fun _ => c) x := by
  classical
  have hm := Set.ext_iff.mp (S.preimage_patch_inter_box t ht hDbox himage) x
  have hiff : torusWrap (S.backward t x) ∈ D ↔ x ∈ S.forward t '' D := by
    simpa only [mem_inter_iff, mem_preimage, Function.comp_apply, hx, and_true] using hm
  by_cases hd : torusWrap (S.backward t x) ∈ D
  · rw [indicator_of_mem hd, indicator_of_mem (hiff.mp hd)]
  · rw [indicator_of_notMem hd, indicator_of_notMem (fun hi => hd (hiff.mpr hi))]

theorem indicator_wrapped_backward_ae (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    {D : Set R2} (hDbox : D ⊆ torusBox) (himage : S.forward t '' D ⊆ torusBox) (c : ℝ) :
    (fun x => D.indicator (fun _ => c) (torusWrap (S.backward t x))) =ᵐ[μT]
      (S.forward t '' D).indicator (fun _ => c) := by
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
  exact S.indicator_wrapped_backward t ht hDbox himage c hx

theorem torusTransportL2_indicator_ae_image (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    {D : Set R2} (hD : MeasurableSet D) (hDbox : D ⊆ torusBox)
    (himage : S.forward t '' D ⊆ torusBox) (c : ℝ) :
    (torusTransportL2 (indicatorConstLp (μ := μT) 2 hD (measure_ne_top μT D) c)
      (S.backward t) (S.backward_area t) : R2 → ℝ) =ᵐ[μT]
        (S.forward t '' D).indicator (fun _ => c) := by
  have hp : (indicatorConstLp (μ := μT) 2 hD (measure_ne_top μT D) c : R2 → ℝ)
      =ᵐ[μT] D.indicator (fun _ => c) := indicatorConstLp_coeFn
  exact (S.torusTransportL2_ae_transportedScalar _ hp.symm t).trans
    (S.indicator_wrapped_backward_ae t ht hDbox himage c)

theorem torusTransportL2_indicator_eq_image (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    {D : Set R2} (hD : MeasurableSet D) (hDbox : D ⊆ torusBox)
    (himage : S.forward t '' D ⊆ torusBox) (c : ℝ) :
    torusTransportL2 (indicatorConstLp (μ := μT) 2 hD (measure_ne_top μT D) c)
      (S.backward t) (S.backward_area t) =
        indicatorConstLp (μ := μT) 2 (S.measurableSet_image_patch t ht hD)
          (measure_ne_top μT (S.forward t '' D)) c := by
  apply Lp.ext
  exact (S.torusTransportL2_indicator_ae_image t ht hD hDbox himage c).trans
    indicatorConstLp_coeFn.symm

theorem twoInterface_wrapped_backward (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    {D E : Set R2} (hD : D ⊆ torusBox) (hE : E ⊆ torusBox)
    (hFD : S.forward t '' D ⊆ torusBox) (hFE : S.forward t '' E ⊆ torusBox)
    {x : R2} (hx : x ∈ torusBox) :
    twoInterface D E (torusWrap (S.backward t x)) =
      twoInterface (S.forward t '' D) (S.forward t '' E) x := by
  unfold twoInterface
  rw [S.indicator_wrapped_backward t ht hD hFD (5 / 2) hx,
    S.indicator_wrapped_backward t ht hE hFE (3 / 2) hx]

theorem finset_indicators_wrapped_backward {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (D : ι → Set R2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hD : ∀ j ∈ s, D j ⊆ torusBox) (hFD : ∀ j ∈ s, S.forward t '' D j ⊆ torusBox)
    {x : R2} (hx : x ∈ torusBox) :
    (∑ j ∈ s, (D j).indicator (fun _ => c j) (torusWrap (S.backward t x))) =
      ∑ j ∈ s, (S.forward t '' D j).indicator (fun _ => c j) x := by
  apply Finset.sum_congr rfl
  intro j hj
  exact S.indicator_wrapped_backward t ht (hD j hj) (hFD j hj) (c j) hx

theorem finset_twoInterface_wrapped_backward {ι : Type*} (s : Finset ι)
    (A : ι → ℝ) (D E : ι → Set R2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hD : ∀ j ∈ s, D j ⊆ torusBox) (hE : ∀ j ∈ s, E j ⊆ torusBox)
    (hFD : ∀ j ∈ s, S.forward t '' D j ⊆ torusBox)
    (hFE : ∀ j ∈ s, S.forward t '' E j ⊆ torusBox)
    {x : R2} (hx : x ∈ torusBox) :
    (∑ j ∈ s, A j * twoInterface (D j) (E j) (torusWrap (S.backward t x))) =
      ∑ j ∈ s, A j * twoInterface (S.forward t '' D j) (S.forward t '' E j) x := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [S.twoInterface_wrapped_backward t ht (hD j hj) (hE j hj) (hFD j hj) (hFE j hj) hx]

theorem particleCurlL2_ae_finset_twoInterface {ι : Type*} (s : Finset ι)
    (A : ι → ℝ) (D E : ι → Set R2)
    (hinit : (fun x => ∑ j ∈ s, A j * twoInterface (D j) (E j) x) =ᵐ[μT] (f : R2 → ℝ))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hD : ∀ j ∈ s, D j ⊆ torusBox) (hE : ∀ j ∈ s, E j ⊆ torusBox)
    (hFD : ∀ j ∈ s, S.forward t '' D j ⊆ torusBox)
    (hFE : ∀ j ∈ s, S.forward t '' E j ⊆ torusBox) :
    (particleCurlL2 f S.backward S.backward_area t : R2 → ℝ) =ᵐ[μT]
      fun x => ∑ j ∈ s, A j * twoInterface (S.forward t '' D j) (S.forward t '' E j) x := by
  filter_upwards [S.particleCurlL2_ae_transportedScalar hinit t,
    ae_restrict_mem measurableSet_torusBox] with x hx hxbox
  exact hx.trans (S.finset_twoInterface_wrapped_backward s A D E t ht hD hE hFD hFE hxbox)

theorem image_patch_quarterTurn (hS : IsFourfoldBoundedEulerParticleSystem S)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) {D : Set R2}
    (hD : ∀ x, torusQuarterTurn x ∈ D ↔ x ∈ D) (x : R2) :
    torusQuarterTurn x ∈ S.forward t '' D ↔ x ∈ S.forward t '' D := by
  rw [S.image_eq_preimage_backward t ht D]
  change S.backward t (torusQuarterTurn x) ∈ D ↔ S.backward t x ∈ D
  rw [hS.backward t ht]
  exact hD _

theorem transportedScalar_quarterTurn (hS : IsFourfoldBoundedEulerParticleSystem S)
    {w : R2 → ℝ} (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    S.transportedScalar w t (torusQuarterTurn x) = S.transportedScalar w t x := by
  rw [S.transportedScalar_eq_of_periodic hwper, S.transportedScalar_eq_of_periodic hwper,
    hS.backward t ht, hwrot]

end BoundedEulerParticleSystem
end Euler2D

end
