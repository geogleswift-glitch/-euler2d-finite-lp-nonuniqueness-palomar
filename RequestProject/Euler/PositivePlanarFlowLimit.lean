module

public import RequestProject.Euler.ExpandingPlanarFlowCompactness
public import RequestProject.Euler.PlanarTransportFlowLimit

/-! A common expanding-window limit retains genuine inverses and
infinite-plane area preservation at every nonnegative time. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

def positivePairForwardAt (H : C(ℝ≥0 × R2, R2 × R2)) (t : ℝ≥0) : C(R2, R2) :=
  ⟨fun a => (H (t, a)).1, H.continuous.fst.comp (continuous_const.prodMk continuous_id)⟩

def positivePairBackwardAt (H : C(ℝ≥0 × R2, R2 × R2)) (t : ℝ≥0) : C(R2, R2) :=
  ⟨fun a => (H (t, a)).2, H.continuous.snd.comp (continuous_const.prodMk continuous_id)⟩

def positivePairRestriction {T : ℝ} (H : C(ℝ≥0 × R2, R2 × R2)) :
    C(Icc (0 : ℝ) T × R2, R2 × R2) :=
  H.comp ⟨fun p => (⟨p.1.val, p.1.property.1⟩, p.2),
    ((continuous_subtype_val.comp continuous_fst).subtype_mk (fun p => p.1.property.1)).prodMk
      continuous_snd⟩

theorem positivePlanarFlow_limit_restriction
    {v : ℕ → ℝ → R2 → R2} (P : ∀ n, PlanarLogParticleFlow (v n) ((n : ℝ) + 1))
    (hF : ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) →
      MeasurePreserving ((P n).forward t) volume volume)
    (hB : ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) →
      MeasurePreserving ((P n).backward t) volume volume)
    {H : C(ℝ≥0 × R2, R2 × R2)} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hlim : Tendsto (fun n => positivePlanarFlowPairMap (P (φ n))) atTop (𝓝 H))
    {T : ℝ} (hT : 0 ≤ T) :
    (∀ t a, planarPairBackwardAt (positivePairRestriction (T := T) H) t
      (planarPairForwardAt (positivePairRestriction H) t a) = a) ∧
    (∀ t a, planarPairForwardAt (positivePairRestriction (T := T) H) t
      (planarPairBackwardAt (positivePairRestriction H) t a) = a) ∧
    (∀ t, MeasurePreserving (planarPairForwardAt (positivePairRestriction (T := T) H) t) volume volume ∧
      MeasurePreserving (planarPairBackwardAt (positivePairRestriction H) t) volume volume) ∧
    (∀ t : Icc (0 : ℝ) T, (t : ℝ) = 0 → ∀ a,
      planarPairForwardAt (positivePairRestriction H) t a = a) := by
  let N : ℕ := ⌈T⌉₊
  have hTN (n : ℕ) : T ≤ (φ (n + N) : ℝ) + 1 := by
    have ha : N ≤ n + N := Nat.le_add_left N n
    have hb : n + N ≤ φ (n + N) := hφ.id_le _
    have hc : (N : ℝ) ≤ (φ (n + N) : ℝ) := by exact_mod_cast ha.trans hb
    have hd : T ≤ (N : ℝ) := Nat.le_ceil T
    linarith
  have hsub (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
      t ∈ Icc (0 : ℝ) ((φ (n + N) : ℝ) + 1) := ⟨ht.1, ht.2.trans (hTN n)⟩
  let Q (n : ℕ) : PlanarLogParticleFlow (v (φ (n + N))) T := {
    forward := (P (φ (n + N))).forward
    backward := (P (φ (n + N))).backward
    continuous_forward := (P (φ (n + N))).continuous_forward
    continuous_backward := (P (φ (n + N))).continuous_backward
    initial := (P (φ (n + N))).initial
    derivative := fun t ht => (P (φ (n + N))).derivative t (hsub n ht)
    left_inv := fun t ht => (P (φ (n + N))).left_inv t (hsub n ht)
    right_inv := fun t ht => (P (φ (n + N))).right_inv t (hsub n ht)
  }
  let j : C(Icc (0 : ℝ) T × R2, ℝ≥0 × R2) :=
    ⟨fun p => (⟨p.1.val, p.1.property.1⟩, p.2),
      ((continuous_subtype_val.comp continuous_fst).subtype_mk (fun p => p.1.property.1)).prodMk
        continuous_snd⟩
  have hshift := hlim.comp (tendsto_add_atTop_nat N)
  have hlocal : Tendsto (fun n => planarFlowPairMap (Q n)) atTop
      (𝓝 (positivePairRestriction (T := T) H)) :=
    ((ContinuousMap.continuous_precomp j).tendsto H).comp hshift
  exact planarFlowPair_limit_inverse_area Q (fun n t ht => hF (φ (n + N)) t (hsub n ht))
    (fun n t ht => hB (φ (n + N)) t (hsub n ht)) hlocal

theorem positivePlanarFlow_limit_inverse_area
    {v : ℕ → ℝ → R2 → R2} (P : ∀ n, PlanarLogParticleFlow (v n) ((n : ℝ) + 1))
    (hF : ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) →
      MeasurePreserving ((P n).forward t) volume volume)
    (hB : ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) →
      MeasurePreserving ((P n).backward t) volume volume)
    {H : C(ℝ≥0 × R2, R2 × R2)} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hlim : Tendsto (fun n => positivePlanarFlowPairMap (P (φ n))) atTop (𝓝 H)) :
    (∀ t a, positivePairBackwardAt H t (positivePairForwardAt H t a) = a) ∧
    (∀ t a, positivePairForwardAt H t (positivePairBackwardAt H t a) = a) ∧
    (∀ t, MeasurePreserving (positivePairForwardAt H t) volume volume ∧
      MeasurePreserving (positivePairBackwardAt H t) volume volume) ∧
    (∀ a, positivePairForwardAt H 0 a = a) := by
  have hp := fun {T : ℝ} (hT : 0 ≤ T) =>
    positivePlanarFlow_limit_restriction P hF hB hφ hlim hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a
    exact (hp t.coe_nonneg).1 ⟨t, t.coe_nonneg, le_rfl⟩ a
  · intro t a
    exact (hp t.coe_nonneg).2.1 ⟨t, t.coe_nonneg, le_rfl⟩ a
  · intro t
    exact (hp t.coe_nonneg).2.2.1 ⟨t, t.coe_nonneg, le_rfl⟩
  · intro a
    exact (hp (le_refl (0 : ℝ))).2.2.2 ⟨0, le_rfl, le_rfl⟩ rfl a

end Euler2D

end
