module

public import RequestProject.Euler.TorusPeriodization
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Actual particle flows on arbitrary finite time windows

Uniform spatial Lipschitz and speed bounds allow Picard--Lindelöf on a
padded time interval of any prescribed length. Uniqueness supplies the
two-parameter flow law and its actual inverse.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

structure IsBoundedLipschitzVelocity (v : ℝ → R2 → R2) (K M : ℝ≥0) : Prop where
  continuous : Continuous (Function.uncurry v)
  lipschitz : ∀ t, LipschitzWith K (v t)
  norm_le : ∀ t x, ‖v t x‖ ≤ M

abbrev ParticleTime (T : ℝ) := Icc (0 : ℝ) T

def particleTimeClamp {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : Icc (-1 : ℝ) (T + 1) :=
  projIcc (-1) (T + 1) (by linarith) t

lemma particleTime_mem_padded {T : ℝ} (s : ParticleTime T) :
    (s : ℝ) ∈ Ioo (-1 : ℝ) (T + 1) := by
  constructor <;> linarith [s.2.1, s.2.2]

structure PaddedParticleCurve (v : ℝ → R2 → R2) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a : R2) where
  toFun : ℝ → R2
  continuous : Continuous toFun
  initial : toFun s = a
  derivative : ∀ t ∈ Ioo (-1 : ℝ) (T + 1), HasDerivAt toFun (v t (toFun t)) t
  clamp : ∀ t, toFun t = toFun (particleTimeClamp hT t)

instance {v : ℝ → R2 → R2} {T : ℝ} {hT : 0 ≤ T} {s : ParticleTime T} {a : R2} :
    CoeFun (PaddedParticleCurve v hT s a) (fun _ => ℝ → R2) := ⟨PaddedParticleCurve.toFun⟩

lemma isPicardLindelof_boundedVelocity {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a : R2) (r : ℝ≥0) :
    IsPicardLindelof v
      (⟨(s : ℝ), (particleTime_mem_padded s).1.le, (particleTime_mem_padded s).2.le⟩ :
        Icc (-1 : ℝ) (T + 1)) a (M * ⟨T + 2, by linarith⟩ + r) r M K := by
  refine ⟨fun t ht => (hv.lipschitz t).lipschitzOnWith, ?_,
    fun t ht x hx => hv.norm_le t x, ?_⟩
  · intro x hx
    exact (hv.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  · change (M : ℝ) * max (T + 1 - (s : ℝ)) ((s : ℝ) - -1) ≤
        ((M * NNReal.mk (T + 2) (by linarith) + r : ℝ≥0) : ℝ) - (r : ℝ)
    have hmax : max (T + 1 - (s : ℝ)) ((s : ℝ) - -1) ≤ T + 2 :=
      max_le (by linarith [s.2.1]) (by linarith [s.2.2])
    simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk,
      add_sub_cancel_right] using mul_le_mul_of_nonneg_left hmax M.2

/-- Actual existence, derived from Picard--Lindelöf with a radius chosen
from the speed bound and the prescribed finite time window. -/
theorem exists_paddedParticleCurve {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a : R2) : Nonempty (PaddedParticleCurve v hT s a) := by
  obtain ⟨α, hα0, hαd⟩ :=
    (isPicardLindelof_boundedVelocity hv hT s a 0).exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  let β : ℝ → R2 := fun t => α (particleTimeClamp hT t)
  have hβ (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) (T + 1)) : β t = α t := by
    simp only [β, particleTimeClamp, projIcc_of_mem _ ht]
  have hcont : Continuous β :=
    (HasDerivWithinAt.continuousOn hαd).restrict.comp
      (continuous_projIcc (h := by linarith))
  refine ⟨⟨β, hcont, ?_, ?_, ?_⟩⟩
  · rw [hβ s ⟨(particleTime_mem_padded s).1.le, (particleTime_mem_padded s).2.le⟩]
    exact hα0
  · intro t ht
    have htJ : Icc (-1 : ℝ) (T + 1) ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have heq : β =ᶠ[𝓝 t] α := by
      filter_upwards [htJ] with u hu
      exact hβ u hu
    have hd := (hαd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt htJ
    simpa only [hβ t ⟨ht.1.le, ht.2.le⟩] using hd.congr_of_eventuallyEq heq
  · intro t
    simp only [β, particleTimeClamp, projIcc_val]

def selectedParticleCurve {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a : R2) : PaddedParticleCurve v hT s a :=
  Classical.choice (exists_paddedParticleCurve hv hT s a)

def boundedParticleFlow {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (t : ℝ) (a : R2) : R2 :=
  selectedParticleCurve hv hT s a t

@[simp] lemma boundedParticleFlow_initial {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a : R2) : boundedParticleFlow hv hT s s a = a :=
  (selectedParticleCurve hv hT s a).initial

lemma boundedParticleFlow_continuous_time {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a : R2) : Continuous (fun t => boundedParticleFlow hv hT s t a) :=
  (selectedParticleCurve hv hT s a).continuous

lemma boundedParticleFlow_hasDerivAt {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a : R2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) (T + 1)) :
    HasDerivAt (fun τ => boundedParticleFlow hv hT s τ a)
      (v t (boundedParticleFlow hv hT s t a)) t :=
  (selectedParticleCurve hv hT s a).derivative t ht

lemma boundedParticleFlow_clamp {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (t : ℝ) (a : R2) :
    boundedParticleFlow hv hT s t a = boundedParticleFlow hv hT s (particleTimeClamp hT t) a :=
  (selectedParticleCurve hv hT s a).clamp t

lemma PaddedParticleCurve.unique {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} {hT : 0 ≤ T}
    {s : ParticleTime T} {a : R2} (α β : PaddedParticleCurve v hT s a) :
    (α : ℝ → R2) = β := by
  have heq : EqOn (α : ℝ → R2) β (Icc (-1 : ℝ) (T + 1)) :=
    ODE_solution_unique_of_mem_Icc (s := fun _ => univ)
      (fun t ht => (hv.lipschitz t).lipschitzOnWith) (particleTime_mem_padded s)
      α.continuous.continuousOn α.derivative (fun _ _ => trivial)
      β.continuous.continuousOn β.derivative (fun _ _ => trivial) (α.initial.trans β.initial.symm)
  funext t
  rw [α.clamp t, β.clamp t]
  exact heq (particleTimeClamp hT t).2

/-- The genuine two-parameter composition law, including the continuous
constant extension outside the padded time window. -/
theorem boundedParticleFlow_cocycle {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s t : ParticleTime T) (r : ℝ) (a : R2) :
    boundedParticleFlow hv hT t r (boundedParticleFlow hv hT s t a) =
      boundedParticleFlow hv hT s r a := by
  let β : PaddedParticleCurve v hT t (boundedParticleFlow hv hT s t a) :=
    { toFun := fun r => boundedParticleFlow hv hT s r a
      continuous := boundedParticleFlow_continuous_time hv hT s a
      initial := rfl
      derivative := fun r hr => boundedParticleFlow_hasDerivAt hv hT s a hr
      clamp := fun r => boundedParticleFlow_clamp hv hT s r a }
  exact congrFun ((selectedParticleCurve hv hT t _).unique hv β) r

theorem boundedParticleFlow_inverse {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s t : ParticleTime T) (a : R2) :
    boundedParticleFlow hv hT t s (boundedParticleFlow hv hT s t a) = a := by
  rw [boundedParticleFlow_cocycle, boundedParticleFlow_initial]

lemma boundedParticleFlow_lipschitz_time {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a : R2) :
    LipschitzOnWith M (fun t => boundedParticleFlow hv hT s t a) (Icc (0 : ℝ) T) := by
  apply (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun t => v t (boundedParticleFlow hv hT s t a))
    (fun t ht => (boundedParticleFlow_hasDerivAt hv hT s a
      (particleTime_mem_padded ⟨t, ht⟩)).hasDerivWithinAt)
  intro t ht
  exact_mod_cast hv.norm_le t (boundedParticleFlow hv hT s t a)

lemma boundedParticleFlow_locally_lipschitz_space {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) (a₀ : R2) :
    ∃ L : ℝ≥0, ∀ t, LipschitzOnWith L (boundedParticleFlow hv hT s t) (closedBall a₀ 1) := by
  obtain ⟨α, hα, L, hL⟩ := (isPicardLindelof_boundedVelocity hv hT s a₀ 1)
    |>.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  have heq (a : R2) (ha : a ∈ closedBall a₀ 1) (t : ℝ) :
      boundedParticleFlow hv hT s t a = α a (particleTimeClamp hT t) := by
    let β : ℝ → R2 := fun t => α a (particleTimeClamp hT t)
    have hβ (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) (T + 1)) : β u = α a u := by
      simp only [β, particleTimeClamp, projIcc_of_mem _ hu]
    let γ : PaddedParticleCurve v hT s a :=
      { toFun := β
        continuous := (HasDerivWithinAt.continuousOn (hα a ha).2).restrict.comp
          (continuous_projIcc (h := by linarith))
        initial := by rw [hβ s ⟨(particleTime_mem_padded s).1.le,
            (particleTime_mem_padded s).2.le⟩]; exact (hα a ha).1
        derivative := by
          intro u hu
          have huJ : Icc (-1 : ℝ) (T + 1) ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
          have hevent : β =ᶠ[𝓝 u] α a := by
            filter_upwards [huJ] with z hz
            exact hβ z hz
          have hd := ((hα a ha).2 u ⟨hu.1.le, hu.2.le⟩).hasDerivAt huJ
          simpa only [hβ u ⟨hu.1.le, hu.2.le⟩] using hd.congr_of_eventuallyEq hevent
        clamp := by intro u; simp only [β, particleTimeClamp, projIcc_val] }
    exact congrFun ((selectedParticleCurve hv hT s a).unique hv γ) t
  refine ⟨L, fun t => LipschitzOnWith.of_dist_le_mul (fun a ha b hb => ?_)⟩
  rw [heq a ha, heq b hb]
  exact (hL (particleTimeClamp hT t) (particleTimeClamp hT t).2).dist_le_mul a ha b hb

/-- Joint continuity in position and destination time for a fixed source time. -/
theorem boundedParticleFlow_continuous_fixed_source {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s : ParticleTime T) : Continuous (fun p : R2 × ℝ => boundedParticleFlow hv hT s p.2 p.1) := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨L, hL⟩ := boundedParticleFlow_locally_lipschitz_space hv hT s p.1
  have hc : ContinuousOn (fun p : R2 × ℝ => boundedParticleFlow hv hT s p.2 p.1)
      (closedBall p.1 1 ×ˢ univ) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ L
      (fun a ha => (boundedParticleFlow_continuous_time hv hT s a).continuousOn)
      (fun t ht => hL t)
  exact hc.continuousAt (prod_mem_nhds (closedBall_mem_nhds p.1 (by norm_num)) univ_mem)

lemma boundedParticleFlow_continuousAt_source_diagonal {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s₀ : ParticleTime T) (a₀ : R2) :
    ContinuousAt (fun p : ParticleTime T × R2 => boundedParticleFlow hv hT p.1 s₀ p.2) (s₀, a₀) := by
  change Tendsto _ _ (𝓝 (boundedParticleFlow hv hT s₀ s₀ a₀))
  rw [boundedParticleFlow_initial]
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb (p : ParticleTime T × R2) :
      dist (boundedParticleFlow hv hT p.1 s₀ p.2) a₀ ≤
        (M : ℝ) * dist (s₀ : ℝ) (p.1 : ℝ) + dist p.2 a₀ := by
    calc
      dist (boundedParticleFlow hv hT p.1 s₀ p.2) a₀ ≤
          dist (boundedParticleFlow hv hT p.1 s₀ p.2) p.2 + dist p.2 a₀ := dist_triangle _ _ _
      _ ≤ _ := by
        have hd := (boundedParticleFlow_lipschitz_time hv hT p.1 p.2).dist_le_mul
          s₀ s₀.2 p.1 p.1.2
        simpa only [boundedParticleFlow_initial] using
          add_le_add hd (le_refl (dist p.2 a₀))
  have hc : Continuous (fun p : ParticleTime T × R2 =>
      (M : ℝ) * dist (s₀ : ℝ) (p.1 : ℝ) + dist p.2 a₀) := by fun_prop
  exact squeeze_zero (fun _ => dist_nonneg) hb (by simpa using hc.tendsto (s₀, a₀))

/-- Joint continuity in both time parameters and the initial particle position. -/
theorem boundedParticleFlow_continuous {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T) :
    Continuous (fun p : ParticleTime T × (ℝ × R2) =>
      boundedParticleFlow hv hT p.1 p.2.1 p.2.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hb : ContinuousAt (fun q : ParticleTime T × (ℝ × R2) =>
      boundedParticleFlow hv hT q.1 p.1 q.2.2) p :=
    (boundedParticleFlow_continuousAt_source_diagonal hv hT p.1 p.2.2).comp
      (f := fun q : ParticleTime T × (ℝ × R2) => (q.1, q.2.2))
      (continuousAt_fst.prodMk continuousAt_snd.snd)
  have hc := (boundedParticleFlow_continuous_fixed_source hv hT p.1).continuousAt.comp
    (f := fun q : ParticleTime T × (ℝ × R2) =>
      (boundedParticleFlow hv hT q.1 p.1 q.2.2, q.2.1))
    (hb.prodMk continuousAt_snd.fst)
  apply hc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun q =>
    (boundedParticleFlow_cocycle hv hT q.1 p.1 q.2.1 q.2.2).symm)

lemma IsTorusPeriodic.eq_add_torusLatticeShift {F : Type*} {f : R2 → F}
    (hf : IsTorusPeriodic f) (x : R2) (k : Fin 2 → ℤ) :
    f (x + torusLatticeShift k) = f x := by
  have h₀ : Function.Periodic f (EuclideanSpace.single 0 (2 * Real.pi)) := fun x => hf x 0
  have h₁ : Function.Periodic f (EuclideanSpace.single 1 (2 * Real.pi)) := fun x => hf x 1
  have heq : torusLatticeShift k = k 0 • EuclideanSpace.single 0 (2 * Real.pi) +
      k 1 • EuclideanSpace.single 1 (2 * Real.pi) := by
    ext i
    fin_cases i <;> simp [torusLatticeShift, EuclideanSpace.single_apply, mul_comm]
  rw [heq]
  exact ((h₀.zsmul (k 0)).add_period (h₁.zsmul (k 1))) x

/-- A spatially periodic velocity produces a lattice-equivariant actual flow. -/
theorem boundedParticleFlow_lattice_equivariant {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (hper : ∀ t, IsTorusPeriodic (v t)) (s : ParticleTime T) (t : ℝ)
    (a : R2) (k : Fin 2 → ℤ) :
    boundedParticleFlow hv hT s t (a + torusLatticeShift k) =
      boundedParticleFlow hv hT s t a + torusLatticeShift k := by
  let β : PaddedParticleCurve v hT s (a + torusLatticeShift k) :=
    { toFun := fun t => boundedParticleFlow hv hT s t a + torusLatticeShift k
      continuous := (boundedParticleFlow_continuous_time hv hT s a).add continuous_const
      initial := by simp only [boundedParticleFlow_initial]
      derivative := by
        intro r hr
        simpa only [(hper r).eq_add_torusLatticeShift] using
          (boundedParticleFlow_hasDerivAt hv hT s a hr).add_const (torusLatticeShift k)
      clamp := fun r => congrArg (fun x => x + torusLatticeShift k)
        (boundedParticleFlow_clamp hv hT s r a) }
  exact congrFun ((selectedParticleCurve hv hT s _).unique hv β) t

/-- At each pair of times the forward and reverse particle flows are actual
mutually inverse homeomorphisms of the plane. -/
def boundedParticleHomeomorph {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (s t : ParticleTime T) : R2 ≃ₜ R2 where
  toFun := boundedParticleFlow hv hT s t
  invFun := boundedParticleFlow hv hT t s
  left_inv := boundedParticleFlow_inverse hv hT s t
  right_inv := boundedParticleFlow_inverse hv hT t s
  continuous_toFun := (boundedParticleFlow_continuous_fixed_source hv hT s).comp
    (continuous_id.prodMk continuous_const)
  continuous_invFun := (boundedParticleFlow_continuous_fixed_source hv hT t).comp
    (continuous_id.prodMk continuous_const)

def boundedParticleForward {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (t : ℝ) (a : R2) : R2 := boundedParticleFlow hv hT ⟨0, le_rfl, hT⟩ t a

def boundedParticleBackward {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (t : ℝ) (a : R2) : R2 := boundedParticleFlow hv hT (projIcc 0 T hT t) 0 a

theorem boundedParticleForward_continuous {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T) :
    Continuous (Function.uncurry (boundedParticleForward hv hT)) :=
  (boundedParticleFlow_continuous_fixed_source hv hT ⟨0, le_rfl, hT⟩).comp
    (continuous_snd.prodMk continuous_fst)

theorem boundedParticleBackward_continuous {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T) :
    Continuous (Function.uncurry (boundedParticleBackward hv hT)) :=
  (boundedParticleFlow_continuous hv hT).comp
    (((continuous_projIcc (h := hT)).comp continuous_fst).prodMk
      (continuous_const.prodMk continuous_snd))

@[simp] lemma boundedParticleForward_zero {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T) (a : R2) :
    boundedParticleForward hv hT 0 a = a := boundedParticleFlow_initial hv hT _ a

theorem boundedParticleForward_hasDerivAt {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    HasDerivAt (fun s => boundedParticleForward hv hT s a)
      (v t (boundedParticleForward hv hT t a)) t :=
  boundedParticleFlow_hasDerivAt hv hT _ a (particleTime_mem_padded ⟨t, ht⟩)

theorem boundedParticleBackward_forward {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    boundedParticleBackward hv hT t (boundedParticleForward hv hT t a) = a := by
  simp only [boundedParticleBackward, boundedParticleForward, projIcc_of_mem _ ht]
  exact boundedParticleFlow_inverse hv hT ⟨0, le_rfl, hT⟩ ⟨t, ht⟩ a

theorem boundedParticleForward_backward {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    boundedParticleForward hv hT t (boundedParticleBackward hv hT t a) = a := by
  simp only [boundedParticleBackward, boundedParticleForward, projIcc_of_mem _ ht]
  exact boundedParticleFlow_inverse hv hT ⟨t, ht⟩ ⟨0, le_rfl, hT⟩ a

theorem boundedParticleForward_lattice_equivariant {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (hper : ∀ t, IsTorusPeriodic (v t)) (t : ℝ) (a : R2) (k : Fin 2 → ℤ) :
    boundedParticleForward hv hT t (a + torusLatticeShift k) =
      boundedParticleForward hv hT t a + torusLatticeShift k :=
  boundedParticleFlow_lattice_equivariant hv hT hper _ t a k

theorem boundedParticleBackward_lattice_equivariant {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M) {T : ℝ} (hT : 0 ≤ T)
    (hper : ∀ t, IsTorusPeriodic (v t)) (t : ℝ) (a : R2) (k : Fin 2 → ℤ) :
    boundedParticleBackward hv hT t (a + torusLatticeShift k) =
      boundedParticleBackward hv hT t a + torusLatticeShift k :=
  boundedParticleFlow_lattice_equivariant hv hT hper _ 0 a k

end Euler2D

end
