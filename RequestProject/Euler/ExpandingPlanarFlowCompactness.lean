module

public import RequestProject.Euler.PlanarFlowPairCompactness

/-! Compactness on all nonnegative times from actual flows on expanding
windows. A finite head never obstructs equicontinuity; a common tail
is controlled on each bounded time window by the actual Osgood estimates. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal UniformConvergence

namespace Euler2D

theorem equicontinuousAt_of_tail {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {U : ℕ → X → Y} {x : X} (hU : ∀ n, ContinuousAt (U n) x)
    (N : ℕ) (htail : EquicontinuousAt (fun n => U (n + N)) x) : EquicontinuousAt U x := by
  have hhead : EquicontinuousAt (fun n : Fin N => U n.val) x :=
    equicontinuousAt_finite.mpr (fun n => hU n.val)
  intro V hV
  filter_upwards [hhead V hV, htail V hV] with y hyhead hytail n
  by_cases hn : n < N
  · exact hyhead ⟨n, hn⟩
  · have he : n - N + N = n := Nat.sub_add_cancel (Nat.le_of_not_gt hn)
    simpa only [he] using hytail (n - N)

def positivePlanarFlowPairMap {v : ℝ → R2 → R2} {T : ℝ}
    (P : PlanarLogParticleFlow v T) : C(ℝ≥0 × R2, R2 × R2) :=
  ⟨fun p => (P.forward p.1 p.2, P.backward p.1 p.2),
    (P.continuous_forward.comp ((NNReal.continuous_coe.comp continuous_fst).prodMk
      continuous_snd)).prodMk
    (P.continuous_backward.comp ((NNReal.continuous_coe.comp continuous_fst).prodMk
      continuous_snd))⟩

theorem uniformEquicontinuous_planarFlow_pair
    {T C V : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (hV : 0 ≤ V)
    {v : ℕ → ℝ → R2 → R2} (P : ∀ n, PlanarLogParticleFlow (v n) T)
    (hbound : ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) T → ∀ x, ‖v n t x‖ ≤ V)
    (hlog : ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) T → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v n t x - v n t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    UniformEquicontinuous (fun n p => planarFlowPairMap (P n) p) := by
  have hF := uniformEquicontinuous_logFlow_family hT hC hV v
    (fun n => (P n).forward) (fun n => (P n).continuous_forward)
    (fun n => (P n).derivative) (fun n => (P n).initial) hbound hlog
  have hB := uniformEquicontinuous_inverse_logFlow_family hT hC hV v
    (fun n => (P n).forward) (fun n => (P n).backward)
    (fun n => (P n).continuous_forward) (fun n => (P n).derivative)
    (fun n => (P n).initial) (fun n => (P n).right_inv) (fun n => (P n).left_inv)
    hbound hlog
  apply Metric.uniformEquicontinuous_iff.mpr
  intro ε hε
  obtain ⟨d, hd, hFd⟩ := Metric.uniformEquicontinuous_iff.mp hF ε hε
  obtain ⟨r, hr, hBr⟩ := Metric.uniformEquicontinuous_iff.mp hB ε hε
  refine ⟨min d r, lt_min hd hr, fun p q hpq n => ?_⟩
  rw [Prod.dist_eq]
  exact max_lt (hFd p q (hpq.trans_le (min_le_left _ _)) n)
    (hBr p q (hpq.trans_le (min_le_right _ _)) n)

theorem equicontinuous_expanding_planarFlow_pairs
    {C V : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V)
    {v : ℕ → ℝ → R2 → R2} (P : ∀ n, PlanarLogParticleFlow (v n) ((n : ℝ) + 1))
    (hbound : ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) → ∀ x, ‖v n t x‖ ≤ V)
    (hlog : ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v n t x - v n t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    Equicontinuous (fun n p => positivePlanarFlowPairMap (P n) p) := by
  intro p
  let K : ℝ := (p.1 : ℝ) + 1
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let N : ℕ := ⌈K⌉₊
  have hKT (n : ℕ) : K ≤ ((n + N : ℕ) : ℝ) + 1 := by
    have hc : K ≤ (N : ℝ) := Nat.le_ceil K
    have hn : (N : ℝ) ≤ ((n + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left N n
    linarith
  have hsub (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) K) :
      t ∈ Icc (0 : ℝ) (((n + N : ℕ) : ℝ) + 1) := ⟨ht.1, ht.2.trans (hKT n)⟩
  let Q (n : ℕ) : PlanarLogParticleFlow (v (n + N)) K := {
    forward := (P (n + N)).forward
    backward := (P (n + N)).backward
    continuous_forward := (P (n + N)).continuous_forward
    continuous_backward := (P (n + N)).continuous_backward
    initial := (P (n + N)).initial
    derivative := fun t ht => (P (n + N)).derivative t (hsub n ht)
    left_inv := fun t ht => (P (n + N)).left_inv t (hsub n ht)
    right_inv := fun t ht => (P (n + N)).right_inv t (hsub n ht)
  }
  have he := (uniformEquicontinuous_planarFlow_pair hK hC hV Q
    (fun n t ht => hbound (n + N) t (hsub n ht))
    (fun n t ht => hlog (n + N) t (hsub n ht))).equicontinuous
  let j : ℝ≥0 × R2 → Icc (0 : ℝ) K × R2 := fun q => (projIcc 0 K hK q.1, q.2)
  have hj : Continuous j :=
    ((continuous_projIcc (h := hK)).comp (NNReal.continuous_coe.comp continuous_fst)).prodMk
      continuous_snd
  have hpmem : (p.1 : ℝ) ∈ Icc (0 : ℝ) K := ⟨p.1.coe_nonneg, by dsimp only [K]; linarith⟩
  have hnear : ∀ᶠ q : ℝ≥0 × R2 in 𝓝 p, (q.1 : ℝ) < K :=
    (NNReal.continuous_coe.comp continuous_fst).continuousAt.eventually
      (eventually_lt_nhds (by dsimp only [K]; linarith : (p.1 : ℝ) < K))
  apply equicontinuousAt_of_tail
    (fun n => (positivePlanarFlowPairMap (P n)).continuous.continuousAt) N
  intro W hW
  have hh := hj.continuousAt.tendsto.eventually (he (j p) W hW)
  filter_upwards [hh, hnear] with q hq hqK n
  have hqmem : (q.1 : ℝ) ∈ Icc (0 : ℝ) K := ⟨q.1.coe_nonneg, hqK.le⟩
  have hep : (projIcc 0 K hK (p.1 : ℝ) : ℝ) = p.1 := congrArg Subtype.val (projIcc_of_mem hK hpmem)
  have heq : (projIcc 0 K hK (q.1 : ℝ) : ℝ) = q.1 := congrArg Subtype.val (projIcc_of_mem hK hqmem)
  simpa only [j, planarFlowPairMap, positivePlanarFlowPairMap, ContinuousMap.coe_mk, Q, hep, heq]
    using hq n

theorem exists_compactOpen_expandingPlanarFlow_subseq
    {C V : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V)
    {v : ℕ → ℝ → R2 → R2} (P : ∀ n, PlanarLogParticleFlow (v n) ((n : ℝ) + 1))
    (hbound : ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) → ∀ x, ‖v n t x‖ ≤ V)
    (hlog : ∀ (n : ℕ) t, t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) → ∀ x y, ‖x - y‖ ≤ 1 / 2 →
      ‖v n t x - v n t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    ∃ H : C(ℝ≥0 × R2, R2 × R2), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => positivePlanarFlowPairMap (P (φ n))) atTop (𝓝 H) := by
  have he := equicontinuous_expanding_planarFlow_pairs hC hV P hbound hlog
  have hvalues (p : ℝ≥0 × R2) :
      ∃ Q : Set (R2 × R2), IsCompact Q ∧ ∀ n, positivePlanarFlowPairMap (P n) p ∈ Q := by
    let N : ℕ := ⌈(p.1 : ℝ)⌉₊
    let R := ‖p.2‖ + V * p.1
    let Q := closedBall (0 : R2) R ×ˢ closedBall (0 : R2) R
    let A : Set (R2 × R2) := range (fun n : Fin N => positivePlanarFlowPairMap (P n) p)
    refine ⟨Q ∪ A, ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).union
      (finite_range (fun n : Fin N => positivePlanarFlowPairMap (P n) p)).isCompact, ?_⟩
    intro n
    by_cases hn : n < N
    · exact Or.inr ⟨⟨n, hn⟩, rfl⟩
    · have hpT : (p.1 : ℝ) ≤ (n : ℝ) + 1 := by
        have hN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_not_gt hn
        have hc : (p.1 : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
        linarith
      have hsub {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (p.1 : ℝ)) :
          s ∈ Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨hs.1, hs.2.trans hpT⟩
      apply Or.inl
      constructor
      · apply mem_closedBall_zero_iff.mpr
        exact norm_logFlow_family_le p.1.coe_nonneg hV (fun _ : Unit => v n)
          (fun _ : Unit => (P n).forward)
          (fun _ s hs => (P n).derivative s (hsub hs))
          (fun _ => (P n).initial) (fun _ s hs => hbound n s (hsub hs))
          () ⟨p.1.coe_nonneg, le_rfl⟩ le_rfl
      · apply mem_closedBall_zero_iff.mpr
        exact norm_inverse_logFlow_family_le p.1.coe_nonneg hV (fun _ : Unit => v n)
          (fun _ : Unit => (P n).forward) (fun _ : Unit => (P n).backward)
          (fun _ s hs => (P n).derivative s (hsub hs)) (fun _ => (P n).initial)
          (fun _ s hs => (P n).right_inv s (hsub hs))
          (fun _ s hs => hbound n s (hsub hs)) () ⟨p.1.coe_nonneg, le_rfl⟩ le_rfl
  obtain ⟨H, φ, hφ, hlim⟩ := exists_compactOpen_subseq_of_equicontinuous
    (fun n p => positivePlanarFlowPairMap (P n) p) he hvalues
  exact ⟨H, φ, hφ, hlim⟩

end Euler2D

end
