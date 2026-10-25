module

public import RequestProject.Euler.LocallyUniformMapCompactness
public import RequestProject.Euler.PlanarLogParticleFlow
public import RequestProject.Euler.MeasurePreservingPairLimit

/-! One common compact-open subsequence for the actual forward and
inverse maps on the whole plane. Genuine inverse identities and
preservation of infinite planar volume pass to this same limit. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped UniformConvergence

namespace Euler2D

def planarFlowPairMap {v : ℝ → R2 → R2} {T : ℝ}
    (P : PlanarLogParticleFlow v T) : C(Icc (0 : ℝ) T × R2, R2 × R2) :=
  ⟨fun p => (P.forward p.1 p.2, P.backward p.1 p.2),
    (P.continuous_forward.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      continuous_snd)).prodMk
    (P.continuous_backward.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      continuous_snd))⟩

def planarPairForwardAt {T : ℝ} (H : C(Icc (0 : ℝ) T × R2, R2 × R2))
    (t : Icc (0 : ℝ) T) : C(R2, R2) :=
  ⟨fun a => (H (t, a)).1, H.continuous.fst.comp (continuous_const.prodMk continuous_id)⟩

def planarPairBackwardAt {T : ℝ} (H : C(Icc (0 : ℝ) T × R2, R2 × R2))
    (t : Icc (0 : ℝ) T) : C(R2, R2) :=
  ⟨fun a => (H (t, a)).2, H.continuous.snd.comp (continuous_const.prodMk continuous_id)⟩

theorem continuous_planarPairBackwardAt_map {T : ℝ} (t : Icc (0 : ℝ) T) :
    Continuous (fun H : C(Icc (0 : ℝ) T × R2, R2 × R2) => planarPairBackwardAt H t) :=
  (ContinuousMap.continuous_postcomp (⟨Prod.snd, continuous_snd⟩ : C(R2 × R2, R2))).comp
    (ContinuousMap.continuous_precomp
      (⟨fun a => (t, a), continuous_const.prodMk continuous_id⟩ : C(R2, Icc (0 : ℝ) T × R2)))

theorem continuous_planarPairBackwardAt_time {T : ℝ}
    (H : C(Icc (0 : ℝ) T × R2, R2 × R2)) : Continuous (planarPairBackwardAt H) :=
  ContinuousMap.continuous_of_continuous_uncurry _ H.continuous.snd

theorem exists_compactOpen_planarFlow_pair_subseq
    {T C V : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (hV : 0 ≤ V)
    {v : ℕ → ℝ → R2 → R2} (P : ∀ n, PlanarLogParticleFlow (v n) T)
    (hbound : ∀ n t, t ∈ Icc (0 : ℝ) T → ∀ x, ‖v n t x‖ ≤ V)
    (hlog : ∀ n t, t ∈ Icc (0 : ℝ) T → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v n t x - v n t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    ∃ H : C(Icc (0 : ℝ) T × R2, R2 × R2), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun n => planarFlowPairMap (P (φ n))) atTop (𝓝 H) := by
  have hF := uniformEquicontinuous_logFlow_family hT hC hV v
    (fun n => (P n).forward) (fun n => (P n).continuous_forward)
    (fun n => (P n).derivative) (fun n => (P n).initial) hbound hlog
  have hB := uniformEquicontinuous_inverse_logFlow_family hT hC hV v
    (fun n => (P n).forward) (fun n => (P n).backward)
    (fun n => (P n).continuous_forward) (fun n => (P n).derivative)
    (fun n => (P n).initial) (fun n => (P n).right_inv) (fun n => (P n).left_inv)
    hbound hlog
  have he : UniformEquicontinuous (fun n p => planarFlowPairMap (P n) p) := by
    apply Metric.uniformEquicontinuous_iff.mpr
    intro ε hε
    obtain ⟨d, hd, hFd⟩ := Metric.uniformEquicontinuous_iff.mp hF ε hε
    obtain ⟨r, hr, hBr⟩ := Metric.uniformEquicontinuous_iff.mp hB ε hε
    refine ⟨min d r, lt_min hd hr, fun p q hpq n => ?_⟩
    change dist ((P n).forward p.1 p.2, (P n).backward p.1 p.2)
      ((P n).forward q.1 q.2, (P n).backward q.1 q.2) < ε
    rw [Prod.dist_eq]
    exact max_lt (hFd p q (hpq.trans_le (min_le_left _ _)) n)
      (hBr p q (hpq.trans_le (min_le_right _ _)) n)
  have hvalues (p : Icc (0 : ℝ) T × R2) :
      ∃ Q : Set (R2 × R2), IsCompact Q ∧ ∀ n, planarFlowPairMap (P n) p ∈ Q := by
    let Q := closedBall (0 : R2) (‖p.2‖ + V * T)
    refine ⟨Q ×ˢ Q, (isCompact_closedBall _ _).prod (isCompact_closedBall _ _), ?_⟩
    intro n
    constructor
    · exact mem_closedBall_zero_iff.mpr (norm_logFlow_family_le hT hV v
        (fun n => (P n).forward) (fun n => (P n).derivative)
        (fun n => (P n).initial) hbound n p.1.property le_rfl)
    · exact mem_closedBall_zero_iff.mpr (norm_inverse_logFlow_family_le hT hV v
        (fun n => (P n).forward) (fun n => (P n).backward)
        (fun n => (P n).derivative) (fun n => (P n).initial)
        (fun n => (P n).right_inv) hbound n p.1.property le_rfl)
  obtain ⟨H, φ, hφ, hlim⟩ := exists_compactOpen_subseq_of_equicontinuous
    (fun n p => planarFlowPairMap (P n) p) he.equicontinuous hvalues
  exact ⟨H, φ, hφ, hlim⟩

theorem planarFlowPair_limit_inverse_area
    {T : ℝ} {v : ℕ → ℝ → R2 → R2} (P : ∀ n, PlanarLogParticleFlow (v n) T)
    (hF : ∀ n t, t ∈ Icc (0 : ℝ) T → MeasurePreserving ((P n).forward t) volume volume)
    (hB : ∀ n t, t ∈ Icc (0 : ℝ) T → MeasurePreserving ((P n).backward t) volume volume)
    {H : C(Icc (0 : ℝ) T × R2, R2 × R2)}
    (hlim : Tendsto (fun n => planarFlowPairMap (P n)) atTop (𝓝 H)) :
    (∀ t a, planarPairBackwardAt H t (planarPairForwardAt H t a) = a) ∧
    (∀ t a, planarPairForwardAt H t (planarPairBackwardAt H t a) = a) ∧
    (∀ t, MeasurePreserving (planarPairForwardAt H t) volume volume ∧
      MeasurePreserving (planarPairBackwardAt H t) volume volume) ∧
    (∀ t : Icc (0 : ℝ) T, (t : ℝ) = 0 → ∀ a, planarPairForwardAt H t a = a) := by
  have heval {p : Icc (0 : ℝ) T × R2} {pn : ℕ → Icc (0 : ℝ) T × R2}
      (hp : Tendsto pn atTop (𝓝 p)) :
      Tendsto (fun n => planarFlowPairMap (P n) (pn n)) atTop (𝓝 (H p)) :=
    continuous_eval.continuousAt.tendsto.comp (hlim.prodMk_nhds hp)
  have hleft (t : Icc (0 : ℝ) T) (a : R2) :
      planarPairBackwardAt H t (planarPairForwardAt H t a) = a := by
    have ha := (heval (p := (t, a)) tendsto_const_nhds).fst_nhds
    have hx := (heval ((tendsto_const_nhds (x := t)).prodMk_nhds ha)).snd_nhds
    have he : (fun n => (planarFlowPairMap (P n)
        (t, (planarFlowPairMap (P n) (t, a)).1)).2) = fun _ => a := by
      funext n
      exact (P n).left_inv t t.property a
    rw [he] at hx
    exact tendsto_nhds_unique hx tendsto_const_nhds
  have hright (t : Icc (0 : ℝ) T) (a : R2) :
      planarPairForwardAt H t (planarPairBackwardAt H t a) = a := by
    have ha := (heval (p := (t, a)) tendsto_const_nhds).snd_nhds
    have hx := (heval ((tendsto_const_nhds (x := t)).prodMk_nhds ha)).fst_nhds
    have he : (fun n => (planarFlowPairMap (P n)
        (t, (planarFlowPairMap (P n) (t, a)).2)).1) = fun _ => a := by
      funext n
      exact (P n).right_inv t t.property a
    rw [he] at hx
    exact tendsto_nhds_unique hx tendsto_const_nhds
  refine ⟨hleft, hright, ?_, ?_⟩
  · intro t
    exact measurePreserving_inverse_pair_of_ae_tendsto
      (fun n => hF n t t.property) (fun n => hB n t t.property)
      (planarPairForwardAt H t).continuous.measurable
      (planarPairBackwardAt H t).continuous.measurable
      (ae_of_all _ fun a => (heval (p := (t, a)) tendsto_const_nhds).fst_nhds)
      (ae_of_all _ fun a => (heval (p := (t, a)) tendsto_const_nhds).snd_nhds)
      (hleft t) (hright t)
  · intro t ht a
    have hx := (heval (p := (t, a)) tendsto_const_nhds).fst_nhds
    have he : (fun n => (planarFlowPairMap (P n) (t, a)).1) = fun _ => a := by
      funext n
      change (P n).forward t a = a
      rw [ht, (P n).initial]
    rw [he] at hx
    exact tendsto_nhds_unique hx tendsto_const_nhds

end Euler2D

end
