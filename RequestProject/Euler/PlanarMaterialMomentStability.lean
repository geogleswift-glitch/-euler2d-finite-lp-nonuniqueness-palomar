module

public import RequestProject.Euler.PlanarFourthMomentBounds
public import RequestProject.Euler.CircularMaterialTransferProfile

/-! The original conjugate fourth moment is compared through genuine
initial labels and actual particle maps. No replacement observation
functional or separately selected positive-time solution is used. -/

@[expose] public section

set_option maxHeartbeats 9000000
set_option maxRecDepth 6500

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem norm_conjugateFourthMonomial_sub_le {R : ℝ} (hR : 0 ≤ R)
    {x y : R2} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖(star (complexPhysicalPlane.symm x)) ^ 4 - (star (complexPhysicalPlane.symm y)) ^ 4‖ ≤
      4 * R ^ 3 * ‖x - y‖ := by
  let z := star (complexPhysicalPlane.symm x)
  let w := star (complexPhysicalPlane.symm y)
  have hz : ‖z‖ ≤ R := by simpa only [z, norm_star, LinearIsometryEquiv.norm_map] using hx
  have hw : ‖w‖ ≤ R := by simpa only [w, norm_star, LinearIsometryEquiv.norm_map] using hy
  have hdiff : ‖z - w‖ = ‖x - y‖ := by
    dsimp only [z, w]
    rw [← star_sub, norm_star, ← complexPhysicalPlane.symm.map_sub, LinearIsometryEquiv.norm_map]
  have hsum : ‖z + w‖ ≤ 2 * R := (norm_add_le _ _).trans (by linarith only [hz, hw])
  have hsum2 : ‖z ^ 2 + w ^ 2‖ ≤ 2 * R ^ 2 := by
    have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    have hw2 : ‖w‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    exact (norm_add_le _ _).trans (by simp only [norm_pow]; linarith only [hz2, hw2])
  have he : z ^ 4 - w ^ 4 = (z - w) * (z + w) * (z ^ 2 + w ^ 2) := by ring
  change ‖z ^ 4 - w ^ 4‖ ≤ _
  rw [he, norm_mul, norm_mul, hdiff]
  calc
    _ ≤ (‖x - y‖ * (2 * R)) * (2 * R ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsum (norm_nonneg _)) hsum2
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem integrable_materialFourthMoment {w : R2 → ℝ} {R : ℝ}
    (hw : Integrable w) {X : R2 → R2} (hX : Continuous X)
    (hbound : ∀ b, w b ≠ 0 → ‖X b‖ ≤ R) :
    Integrable (fun b => (w b : ℂ) * (star (complexPhysicalPlane.symm (X b))) ^ 4) := by
  have hpoly : Continuous (fun b => (star (complexPhysicalPlane.symm (X b))) ^ 4) := by fun_prop
  have hm := (Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).mul
    hpoly.aestronglyMeasurable
  apply (hw.norm.mul_const (R ^ 4)).mono' hm
  apply ae_of_all
  intro b
  change ‖(w b : ℂ) * (star (complexPhysicalPlane.symm (X b))) ^ 4‖ ≤ ‖w b‖ * R ^ 4
  by_cases hb : w b = 0
  · simp only [hb, Complex.ofReal_zero, zero_mul, norm_zero, le_refl]
  · have hh := pow_le_pow_left₀ (norm_nonneg _) (hbound b hb) 4
    simpa only [norm_mul, Complex.norm_real, norm_pow, norm_star, LinearIsometryEquiv.norm_map] using
      mul_le_mul_of_nonneg_left hh (norm_nonneg (w b))

theorem planarFourthMoment_eq_material (w : R2 → ℝ) (X : R2 ≃ₜ R2)
    (hX : MeasurePreserving X volume volume) :
    planarFourthMoment (fun x => w (X.symm x)) =
      ∫ b, (w b : ℂ) * (star (complexPhysicalPlane.symm (X b))) ^ 4 := by
  have he := hX.integral_comp X.measurableEmbedding
    (planarFourthMomentIntegrand (fun x => w (X.symm x)))
  simpa only [planarFourthMoment, planarFourthMomentIntegrand, Homeomorph.symm_apply_apply] using he.symm

theorem norm_materialFourthMoment_sub_le {w f : R2 → ℝ} {R η : ℝ}
    (hw : Integrable w) (hf : Integrable f) (hR : 0 ≤ R) (hη : 0 ≤ η)
    (X Y : R2 → R2) (hX : Continuous X) (hY : Continuous Y)
    (hXR : ∀ b, w b ≠ 0 ∨ f b ≠ 0 → ‖X b‖ ≤ R)
    (hYR : ∀ b, w b ≠ 0 ∨ f b ≠ 0 → ‖Y b‖ ≤ R)
    (hclose : ∀ b, w b ≠ 0 → ‖X b - Y b‖ ≤ η) :
    ‖(∫ b, (w b : ℂ) * (star (complexPhysicalPlane.symm (X b))) ^ 4) -
        ∫ b, (f b : ℂ) * (star (complexPhysicalPlane.symm (Y b))) ^ 4‖ ≤
      (4 * R ^ 3 * η) * (∫ b, ‖w b‖) + R ^ 4 * ∫ b, ‖w b - f b‖ := by
  let ψ : R2 → ℂ := fun x => (star (complexPhysicalPlane.symm x)) ^ 4
  have hiX := integrable_materialFourthMoment hw hX (fun b hb => hXR b (Or.inl hb))
  have hiY := integrable_materialFourthMoment hf hY (fun b hb => hYR b (Or.inr hb))
  rw [← integral_sub hiX hiY]
  have hpoint (b : R2) : ‖(w b : ℂ) * ψ (X b) - (f b : ℂ) * ψ (Y b)‖ ≤
      (4 * R ^ 3 * η) * ‖w b‖ + R ^ 4 * ‖w b - f b‖ := by
    have hfirst : ‖(w b : ℂ) * (ψ (X b) - ψ (Y b))‖ ≤ (4 * R ^ 3 * η) * ‖w b‖ := by
      by_cases hb : w b = 0
      · simp only [hb, Complex.ofReal_zero, zero_mul, norm_zero, mul_zero, le_refl]
      · have hh := (norm_conjugateFourthMonomial_sub_le hR (hXR b (Or.inl hb))
          (hYR b (Or.inl hb))).trans (mul_le_mul_of_nonneg_left (hclose b hb) (by positivity))
        rw [norm_mul, Complex.norm_real]
        exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_comm _ _)
    have hsecond : ‖((w b - f b : ℝ) : ℂ) * ψ (Y b)‖ ≤ R ^ 4 * ‖w b - f b‖ := by
      by_cases hb : w b - f b = 0
      · simp only [hb, Complex.ofReal_zero, zero_mul, norm_zero, mul_zero, le_refl]
      · have hactive : w b ≠ 0 ∨ f b ≠ 0 := by
          by_contra hn
          push_neg at hn
          exact hb (by rw [hn.1, hn.2, sub_zero])
        have hh := pow_le_pow_left₀ (norm_nonneg _) (hYR b hactive) 4
        rw [norm_mul, Complex.norm_real]
        simpa only [ψ, norm_pow, norm_star, LinearIsometryEquiv.norm_map, mul_comm] using
          mul_le_mul_of_nonneg_left hh (norm_nonneg (w b - f b))
    have he : (w b : ℂ) * ψ (X b) - (f b : ℂ) * ψ (Y b) =
        (w b : ℂ) * (ψ (X b) - ψ (Y b)) + ((w b - f b : ℝ) : ℂ) * ψ (Y b) := by
      push_cast
      ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  have hi := (hw.norm.const_mul (4 * R ^ 3 * η)).add ((hw.sub hf).norm.const_mul (R ^ 4))
  have hb := norm_integral_le_of_norm_le hi (ae_of_all _ hpoint)
  calc
    _ ≤ ∫ b, (4 * R ^ 3 * η) * ‖w b‖ + R ^ 4 * ‖w b - f b‖ := by
      simpa only [ψ, Pi.add_apply, Pi.sub_apply] using hb
    _ = _ := by
      have he := integral_add (hw.norm.const_mul (4 * R ^ 3 * η)) ((hw.sub hf).norm.const_mul (R ^ 4))
      simpa only [Pi.add_apply, Pi.sub_apply, integral_const_mul] using he

theorem norm_planarFourthMoment_material_sub_le {w f : R2 → ℝ} {R η : ℝ}
    (hw : Integrable w) (hf : Integrable f) (hR : 0 ≤ R) (hη : 0 ≤ η)
    (X Y : R2 ≃ₜ R2) (hX : MeasurePreserving X volume volume) (hY : MeasurePreserving Y volume volume)
    (hXR : ∀ b, w b ≠ 0 ∨ f b ≠ 0 → ‖X b‖ ≤ R)
    (hYR : ∀ b, w b ≠ 0 ∨ f b ≠ 0 → ‖Y b‖ ≤ R)
    (hclose : ∀ b, w b ≠ 0 → ‖X b - Y b‖ ≤ η) :
    ‖planarFourthMoment (fun x => w (X.symm x)) - planarFourthMoment (fun x => f (Y.symm x))‖ ≤
      (4 * R ^ 3 * η) * (∫ b, ‖w b‖) + R ^ 4 * ∫ b, ‖w b - f b‖ := by
  rw [planarFourthMoment_eq_material w X hX, planarFourthMoment_eq_material f Y hY]
  exact norm_materialFourthMoment_sub_le hw hf hR hη X Y X.continuous Y.continuous hXR hYR hclose

theorem CircularMaterialTransferProfile.moment_positive_eq_material {γ : ℝ≥0}
    {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1} (P : CircularMaterialTransferProfile hγ hγ1)
    {t : ℝ} (ht : 0 ≤ t) :
    P.moment t = ∫ b, (circularPhasePatchPlanarVorticity (P.ancient 0) b : ℂ) *
      (star (complexPhysicalPlane.symm (P.positive.forward t b))) ^ 4 := by
  rw [P.moment_positive t ht]
  exact planarFourthMoment_eq_material _ (P.positive.homeomorph t ht) (P.positive.forward_area t ht)

end Euler2D

end
