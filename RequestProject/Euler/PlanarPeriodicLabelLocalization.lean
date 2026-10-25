module

public import RequestProject.Euler.CircularSinglePlanarLabelTransport
public import RequestProject.Euler.EulerPatchTransport
public import RequestProject.Euler.CircularFiniteLabelActiveWindow
public import RequestProject.Euler.CircularFiniteInnerInitialRadius

/-! Localize the original wrapped Euler label by its actual particle
support. This remains valid after the transported domains cease to have
a chosen smooth contour parametrization. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 5000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem transportedScalar_eq_singlePlanar_of_support
    (v q₀ : R2 → ℝ) (hinit : ∀ y ∈ torusBox, v y = q₀ y)
    (hstart : ∀ y, q₀ y ≠ 0 → y ∈ torusBox) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (himage : ∀ y, q₀ y ≠ 0 → S.forward t y ∈ torusBox)
    {x : R2} (hx : x ∈ torusBox) :
    S.transportedScalar v t x = q₀ (S.backward t x) := by
  let D : Set R2 := {y | q₀ y ≠ 0}
  have hDbox : D ⊆ torusBox := fun y hy => hstart y hy
  have himagebox : S.forward t '' D ⊆ torusBox := by
    rintro _ ⟨y, hy, rfl⟩
    exact himage y hy
  have hm := Set.ext_iff.mp (S.preimage_patch_inter_box t ht hDbox himagebox) x
  have hiff : torusWrap (S.backward t x) ∈ D ↔ x ∈ S.forward t '' D := by
    simpa only [mem_inter_iff, mem_preimage, Function.comp_apply, hx, and_true] using hm
  unfold transportedScalar
  rw [hinit (torusWrap (S.backward t x)) (torusRep_mem (torusProj (S.backward t x)))]
  by_cases hq : q₀ (S.backward t x) = 0
  · have hwrap : q₀ (torusWrap (S.backward t x)) = 0 := by
      by_contra hn
      obtain ⟨y, hy, hyx⟩ := hiff.mp hn
      have hback : S.backward t x = y := by rw [← hyx, S.backward_forward t ht y]
      exact hy (hback ▸ hq)
    rw [hwrap, hq]
  · simp only [torusWrap, torusRep_torusProj (hstart _ hq)]

end BoundedEulerParticleSystem

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem normalized_finiteSinglePlanarLabel_eq_periodicLabel_of_particle_bound
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N j : ℕ)
    {f : Lp ℝ 2 μT} {T t B : ℝ} (S : BoundedEulerParticleSystem f T)
    (ht : t ∈ Icc (0 : ℝ) T) (hB : B < 1)
    (hparticles : ∀ y ∈ torusBox, P.finitePeriodicLabel s A₀ b R ρ N j y ≠ 0 →
      ‖S.forward t y - torusCenter‖ ≤ B) (A r : ℝ)
    {z : R2} (hz : r • z + torusCenter ∈ torusBox) :
    S.normalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j) A r t z =
      A⁻¹ * S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t (r • z + torusCenter) := by
  have hzero := P.finitePlanarLabel_zero_of_one_le_norm (A₀ := A₀) (b := b) hs hR hRmax hρ hρ1 N j
  have hinit : ∀ y ∈ torusBox, P.finitePeriodicLabel s A₀ b R ρ N j y =
      P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j y := by
    intro y hy
    exact periodicCenteredSource_eq_on_box hzero hy
  have hstart : ∀ y, P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j y ≠ 0 → y ∈ torusBox := by
    intro y hne
    apply norm_sub_center_lt_one_mem_box
    by_contra hn
    exact hne (hzero _ (not_lt.mp hn))
  have himage : ∀ y, P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j y ≠ 0 →
      S.forward t y ∈ torusBox := by
    intro y hne
    have hy := hstart y hne
    have hperiodic : P.finitePeriodicLabel s A₀ b R ρ N j y ≠ 0 := by
      rwa [hinit y hy]
    exact norm_sub_center_lt_one_mem_box ((hparticles y hy hperiodic).trans_lt hB)
  unfold BoundedEulerParticleSystem.normalizedPlanarLabelSource
  congr 1
  exact (S.transportedScalar_eq_singlePlanar_of_support _ _ hinit hstart ht himage hz).symm

theorem exists_uniform_actualFinite_planar_label_localization :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T H c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ H → H ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * H < c → c * R < 1 →
      ∀ N : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      ∀ t ∈ Icc (0 : ℝ) H, ∀ j : ℕ,
        (∀ A r : ℝ, ∀ z : R2, r • z + torusCenter ∈ torusBox →
          S.normalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j) A r t z =
            A⁻¹ * S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t (r • z + torusCenter)) ∧
        ∀ x : R2, c * R < ‖x - torusCenter‖ →
          P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j (S.backward t x) = 0 := by
  obtain ⟨C, hC, hwindow⟩ := P.exists_uniform_finiteEuler_label_active_window
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T H c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hH hHT hdrift hcR N S
  have hactual := hwindow (s := s) (A₀ := A₀) (b := b) (R := R) (ρ := ρ)
    (q := q) (T := T) (H := H) (c := c)
    hs hA hb hR hRmax hρ hρ1 hρb hq hqE hH hHT hdrift hcR N S
  have hinitial (j : ℕ) (y : R2)
      (hne : P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j y ≠ 0) :
      ‖y - torusCenter‖ ≤ (5 / 4 : ℝ) * R := by
    have hrj : radScale R ρ j ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
    apply le_of_not_gt
    intro hn
    exact hne (P.finitePlanarLabel_eq_zero_of_radius hs hR hρ N j
      ((mul_le_mul_of_nonneg_left hrj (by norm_num : (0 : ℝ) ≤ 5 / 4)).trans_lt hn))
  intro t ht j
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans hHT⟩
  refine ⟨?_, ?_⟩
  · intro A r z hz
    apply P.normalized_finiteSinglePlanarLabel_eq_periodicLabel_of_particle_bound
      hs hR hRmax hρ hρ1 N j S htT hcR ?_ A r hz
    intro y hy hne
    have hper : P.finitePeriodicLabel s A₀ b R ρ N j y =
        P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j y := by
      exact periodicCenteredSource_eq_on_box
        (P.finitePlanarLabel_zero_of_one_le_norm (A₀ := A₀) (b := b) hs hR hRmax hρ hρ1 N j) hy
    have hplain : P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j y ≠ 0 := by
      rwa [hper] at hne
    exact (hactual.1 t ht y (hinitial j y hplain)).le
  · intro x hx
    by_contra hne
    have hbound := hactual.1 t ht (S.backward t x) (hinitial j (S.backward t x) hne)
    rw [S.forward_backward t htT x] at hbound
    exact lt_asymm hx hbound

end CircularMaterialTransferProfile
end Euler2D

end
