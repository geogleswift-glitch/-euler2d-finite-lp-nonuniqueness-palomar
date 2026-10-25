module

public import RequestProject.Euler.EulerRadialSupportBarrier

/-! A radius fence for an arbitrary genuine finite-stage start time,
and support transport for the same actual Euler inverse map. -/

@[expose] public section

set_option maxHeartbeats 2100000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem forward_radius_le_of_stage_radial_barrier {a H a₀ a₁ B V L F : ℝ}
    (ha : 0 ≤ a) (haH : a ≤ H) (hHT : H ≤ T) (ha₀ : 0 ≤ a₀) (ha₀₁ : a₀ ≤ a₁)
    (ha₁ : 0 < a₁) (hB : 0 < B) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hF : V + L * B ^ 3 < F) (hbudget : a₁ + F * (H - a) ≤ B)
    (hradial : ∀ s ∈ Icc a H, ∀ x, ‖x - torusCenter‖ ≤ B →
      inner ℝ (x - torusCenter) (particleVelocityRepresentative f S.backward S.backward_area s x) ≤
        ‖x - torusCenter‖ * (V + L * ‖x - torusCenter‖ ^ 3))
    {y : R2} (hy : ‖S.forward a y - torusCenter‖ ≤ a₀) {t : ℝ} (ht : t ∈ Icc a H) :
    ‖S.forward t y - torusCenter‖ ≤ a₁ + F * (t - a) := by
  have hFpos : 0 < F := (add_nonneg hV (mul_nonneg hL (pow_nonneg hB.le 3))).trans_lt hF
  have htime (s : ℝ) (hs : s ∈ Icc a H) : 0 < a₁ + F * (s - a) := by
    nlinarith [mul_nonneg hFpos.le (sub_nonneg.mpr hs.1)]
  let G : ℝ → ℝ := fun s => ‖S.forward s y - torusCenter‖ ^ 2
  let G' : ℝ → ℝ := fun s => 2 * inner ℝ (S.forward s y - torusCenter)
    (particleVelocityRepresentative f S.backward S.backward_area s (S.forward s y))
  have hc : ContinuousOn G (Icc a H) :=
    (((S.forward_continuous.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow 2).continuousOn
  have hd : ∀ s ∈ Ico a H, HasDerivWithinAt G (G' s) (Ici s) s := by
    intro s hs
    exact ((S.derivative s ⟨ha.trans hs.1, hs.2.le.trans hHT⟩ y).sub_const torusCenter).norm_sq.hasDerivWithinAt
  have hinit : G a ≤ (a₁ + F * (a - a)) ^ 2 := by
    simp only [G, sub_self, mul_zero, add_zero]
    exact pow_le_pow_left₀ (norm_nonneg _) (hy.trans ha₀₁) 2
  have hbd (s : ℝ) : HasDerivAt (fun s => (a₁ + F * (s - a)) ^ 2)
      (2 * (a₁ + F * (s - a)) * F) s := by
    convert ((hasDerivAt_const s a₁).add (((hasDerivAt_id s).sub_const a).const_mul F)).pow 2 using 1
      <;> dsimp <;> ring
  have hbound := image_le_of_deriv_right_lt_deriv_boundary hc hd hinit hbd (fun s hs he => by
    have hscc : s ∈ Icc a H := ⟨hs.1, hs.2.le⟩
    have hp := htime s hscc
    have hnorm : ‖S.forward s y - torusCenter‖ = a₁ + F * (s - a) := by
      dsimp [G] at he
      nlinarith [norm_nonneg (S.forward s y - torusCenter)]
    have hlocal : ‖S.forward s y - torusCenter‖ ≤ B := by
      rw [hnorm]
      exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (sub_le_sub_right hs.2.le a) hFpos.le)).trans hbudget
    have hrad := hradial s hscc (S.forward s y) hlocal
    have hpow := pow_le_pow_left₀ (norm_nonneg (S.forward s y - torusCenter)) hlocal 3
    have hdot := hrad.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow hL)) (norm_nonneg _))
    dsimp [G']
    calc
      _ ≤ 2 * (‖S.forward s y - torusCenter‖ * (V + L * B ^ 3)) :=
        mul_le_mul_of_nonneg_left hdot (by norm_num)
      _ < 2 * (‖S.forward s y - torusCenter‖ * F) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hF (by rw [hnorm]; exact hp)) (by norm_num)
      _ = _ := by rw [hnorm]; ring)
  have hh := hbound ht
  have hp := htime t ht
  dsimp [G] at hh
  nlinarith [norm_nonneg (S.forward t y - torusCenter)]

theorem transportedScalar_support_of_stage_radial_barrier
    {a H a₀ a₁ B V L F : ℝ} {w : R2 → ℝ} {A : Set R2}
    (ha : 0 ≤ a) (haH : a ≤ H) (hHT : H ≤ T) (ha₀ : 0 ≤ a₀) (ha₀₁ : a₀ ≤ a₁)
    (ha₁ : 0 < a₁) (hB : 0 < B) (hB1 : B < 1) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hF : V + L * B ^ 3 < F) (hbudget : a₁ + F * (H - a) ≤ B)
    (hradial : ∀ s ∈ Icc a H, ∀ x, ‖x - torusCenter‖ ≤ B →
      inner ℝ (x - torusCenter) (particleVelocityRepresentative f S.backward S.backward_area s x) ≤
        ‖x - torusCenter‖ * (V + L * ‖x - torusCenter‖ ^ 3))
    (hAbox : A ⊆ torusBox) (hw : ∀ x ∈ torusBox, x ∉ A → w x = 0)
    (hstart : ∀ y ∈ A, ‖S.forward a y - torusCenter‖ ≤ a₀)
    {t : ℝ} (ht : t ∈ Icc a H) :
    ∀ x ∈ torusBox, B < ‖x - torusCenter‖ → S.transportedScalar w t x = 0 := by
  have hFpos : 0 < F := (add_nonneg hV (mul_nonneg hL (pow_nonneg hB.le 3))).trans_lt hF
  have himage_norm (y : R2) (hy : y ∈ A) : ‖S.forward t y - torusCenter‖ ≤ B := by
    exact (S.forward_radius_le_of_stage_radial_barrier ha haH hHT ha₀ ha₀₁ ha₁ hB hV hL hF
      hbudget hradial (hstart y hy) ht).trans
        ((add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hFpos.le)).trans hbudget)
  have himage : S.forward t '' A ⊆ torusBox := by
    rintro y ⟨z, hz, rfl⟩
    exact norm_sub_center_lt_one_mem_box ((himage_norm z hz).trans_lt hB1)
  intro x hx hxa
  by_contra hne
  have hpre : torusWrap (S.backward t x) ∈ A := by
    by_contra hn
    exact hne (hw _ (torusRep_mem _) hn)
  have hximage : x ∈ S.forward t '' A := by
    rw [← S.preimage_patch_inter_box t ⟨ha.trans ht.1, ht.2.trans hHT⟩ hAbox himage]
    exact ⟨hpre, hx⟩
  obtain ⟨y, hy, he⟩ := hximage
  have hn := himage_norm y hy
  rw [he] at hn
  exact (not_lt_of_ge hn) hxa

end BoundedEulerParticleSystem
end Euler2D

end
