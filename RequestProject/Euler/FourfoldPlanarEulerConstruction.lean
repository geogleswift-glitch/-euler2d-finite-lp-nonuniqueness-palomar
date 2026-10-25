module

public import RequestProject.Euler.PlanarMaterialParticleSymmetry
public import RequestProject.Euler.PlanarSmoothedKernelSymmetry
public import RequestProject.Euler.GlobalPlanarEulerTranslation

/-! Actual fourfold planar Euler continuations. Symmetry is proved for
the genuine regularized particles, retained by their common forward and
inverse compact limits, and then retained on expanding time windows. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem planarKernelVelocity_torusQuarterTurn {K : R2 → R2} {w : R2 → ℝ}
    (hK : ∀ x, K (perpJ x) = perpJ (K x))
    (hw : ∀ x, w (torusQuarterTurn x) = w x) (x : R2) :
    planarKernelVelocity K w (torusQuarterTurn x) = perpJ (planarKernelVelocity K w x) := by
  unfold planarKernelVelocity
  calc
    _ = ∫ z, w (torusQuarterTurn z) • K (torusQuarterTurn x - torusQuarterTurn z) :=
      (integral_comp_torusQuarterTurn_unconditional _).symm
    _ = ∫ z, perpJ (w z • K (x - z)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        dsimp only
        have he : torusQuarterTurn x - torusQuarterTurn z = perpJ (x - z) := by
          ext i
          fin_cases i <;> simp [torusQuarterTurn, perpJ] <;> ring
        rw [hw z, he, hK, perpJ_smul])
    _ = _ := perpJLinearIsometryEquiv.toLinearIsometry.integral_comp_comm _

namespace PlanarRegularizedFlowLimit

variable {w : R2 → ℝ} {T : ℝ} (S : PlanarRegularizedFlowLimit w T)

theorem forward_quarterTurn (hw : Integrable w μT)
    (hwrot : ∀ x, planarBoxSource w (torusQuarterTurn x) = planarBoxSource w x)
    (t : Icc (0 : ℝ) T) (a : R2) :
    planarPairForwardAt S.limit.maps t (torusQuarterTurn a) =
      torusQuarterTurn (planarPairForwardAt S.limit.maps t a) := by
  obtain ⟨L, M, hK⟩ := exists_planarSmoothedBiotSavartKernel_bounds
  have hT : 0 ≤ T := t.property.1.trans t.property.2
  have hrot (n : ℕ) := (S.system n).forward_quarterTurn hw (hK n).2.1
    (hK n).2.2.1 (planarSmoothedBiotSavartKernel_perpJ n) hwrot hT t t.property a
  have hr := (torusQuarterTurn_smooth.continuous.tendsto
    (planarPairForwardAt S.limit.maps t a)).comp (S.forward_tendsto t a)
  exact tendsto_nhds_unique (S.forward_tendsto t (torusQuarterTurn a))
    (hr.congr' (Eventually.of_forall fun n => (hrot (S.indices n)).symm))

theorem backward_quarterTurn (hw : Integrable w μT)
    (hwrot : ∀ x, planarBoxSource w (torusQuarterTurn x) = planarBoxSource w x)
    (t : Icc (0 : ℝ) T) (a : R2) :
    planarPairBackwardAt S.limit.maps t (torusQuarterTurn a) =
      torusQuarterTurn (planarPairBackwardAt S.limit.maps t a) := by
  obtain ⟨L, M, hK⟩ := exists_planarSmoothedBiotSavartKernel_bounds
  have hT : 0 ≤ T := t.property.1.trans t.property.2
  have hrot (n : ℕ) := (S.system n).backward_quarterTurn hw (hK n).2.1
    (hK n).2.2.1 (planarSmoothedBiotSavartKernel_perpJ n) hwrot hT t t.property a
  have hb (x : R2) : Tendsto (fun n => (S.system (S.indices n)).particles.backward t x)
      atTop (𝓝 (planarPairBackwardAt S.limit.maps t x)) :=
    (((continuous_eval_const (t, x)).tendsto S.limit.maps).comp S.converges).snd_nhds
  have hr := (torusQuarterTurn_smooth.continuous.tendsto
    (planarPairBackwardAt S.limit.maps t a)).comp (hb a)
  exact tendsto_nhds_unique (hb (torusQuarterTurn a))
    (hr.congr' (Eventually.of_forall fun n => (hrot (S.indices n)).symm))

end PlanarRegularizedFlowLimit

structure IsFourfoldPlanarEulerParticleSystem {w : R2 → ℝ} {T : ℝ}
    (S : PlanarEulerParticleSystem w T) : Prop where
  forward : ∀ t ∈ Icc (0 : ℝ) T, ∀ a,
    S.particles.forward t (torusQuarterTurn a) = torusQuarterTurn (S.particles.forward t a)
  backward : ∀ t a,
    S.particles.backward t (torusQuarterTurn a) = torusQuarterTurn (S.particles.backward t a)

theorem exists_fourfoldPlanarEulerParticleSystem {w : R2 → ℝ} {B : ℝ}
    (hw : Integrable w μT) (hB : 0 ≤ B) (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B)
    (hwrot : ∀ x, planarBoxSource w (torusQuarterTurn x) = planarBoxSource w x)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ E : PlanarEulerParticleSystem (planarBoxSource w) T, IsFourfoldPlanarEulerParticleSystem E := by
  obtain ⟨S⟩ := exists_planarRegularizedFlowLimit hw hB hwB hT
  let F : Icc (0 : ℝ) T → R2 → R2 := fun t a => planarPairForwardAt S.limit.maps t a
  let v := S.limit.velocity
  have hFc : Continuous (Function.uncurry F) := S.limit.maps.continuous.fst
  have hvc : Continuous (Function.uncurry v) :=
    S.limit.continuous_velocity (integrable_planarBoxSource hw) (norm_planarBoxSource_le hB hwB)
  have hInt : ∀ (t : Icc (0 : ℝ) T) a,
      F t a = a + ∫ s in (0 : ℝ)..(t : ℝ), clampedParticleDerivative hT v F s a :=
    S.particle_integral_eq hw hB hwB hT
  let X := particleIntegralExtension hT v F
  let Y : ℝ → R2 → R2 := fun t a => planarPairBackwardAt S.limit.maps (projIcc 0 T hT t) a
  have hXeq (t : Icc (0 : ℝ) T) (a : R2) : X t a = F t a :=
    particleIntegralExtension_eq hT hInt t a
  have hYeq (t : Icc (0 : ℝ) T) (a : R2) : Y t a = planarPairBackwardAt S.limit.maps t a := by
    dsimp only [Y]
    rw [projIcc_val]
  let P : PlanarLogParticleFlow (particleVelocityExtension hT v) T := {
    forward := X
    backward := Y
    continuous_forward := continuous_particleIntegralExtension hT hvc hFc
    continuous_backward := S.limit.maps.continuous.snd.comp
      (((continuous_projIcc (h := hT)).comp continuous_fst).prodMk continuous_snd)
    initial := particleIntegralExtension_zero hT v F
    derivative := fun t ht a => particleIntegralExtension_hasDerivAt_on_Icc hT hvc hFc hInt ht a
    left_inv := by
      intro t ht a
      rw [hXeq ⟨t, ht⟩, hYeq ⟨t, ht⟩]
      exact S.limit.left_inv _ a
    right_inv := by
      intro t ht a
      rw [hYeq ⟨t, ht⟩, hXeq ⟨t, ht⟩]
      exact S.limit.right_inv _ a
  }
  let E : PlanarEulerParticleSystem (planarBoxSource w) T := {
    velocity := particleVelocityExtension hT v
    particles := P
    continuous_velocity := continuous_particleVelocityExtension hT hvc
    forward_area := by
      intro t ht
      change MeasurePreserving (X t) volume volume
      have he : X t = F ⟨t, ht⟩ := funext (hXeq ⟨t, ht⟩)
      rw [he]
      exact S.limit.forward_area _
    backward_area := fun t => S.limit.backward_area (projIcc 0 T hT t)
    selfconsistent := fun t x => rfl
  }
  refine ⟨E, { forward := ?_, backward := ?_ }⟩
  · intro t ht a
    change X t (torusQuarterTurn a) = torusQuarterTurn (X t a)
    rw [hXeq ⟨t, ht⟩, hXeq ⟨t, ht⟩]
    exact S.forward_quarterTurn hw hwrot ⟨t, ht⟩ a
  · intro t a
    exact S.backward_quarterTurn hw hwrot (projIcc 0 T hT t) a

theorem IsFourfoldPlanarEulerParticleSystem.velocity
    {w : R2 → ℝ} {T : ℝ} {S : PlanarEulerParticleSystem w T}
    (hS : IsFourfoldPlanarEulerParticleSystem S)
    (hwrot : ∀ x, w (torusQuarterTurn x) = w x) (t : ℝ) (x : R2) :
    S.velocity t (torusQuarterTurn x) = perpJ (S.velocity t x) := by
  rw [S.selfconsistent, S.selfconsistent]
  apply planarKernelVelocity_torusQuarterTurn kernelK_perpJ
  intro y
  rw [hS.backward, hwrot]

theorem exists_fourfoldExpandingPlanarEulerLimit {w : R2 → ℝ} {B : ℝ}
    (hw : Integrable w μT) (hB : 0 ≤ B) (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B)
    (hwrot : ∀ x, planarBoxSource w (torusQuarterTurn x) = planarBoxSource w x) :
    ∃ S : ExpandingPlanarEulerLimit (planarBoxSource w), ∀ (t : ℝ≥0) a,
      positivePairForwardAt S.limit.maps t (torusQuarterTurn a) =
        torusQuarterTurn (positivePairForwardAt S.limit.maps t a) ∧
      positivePairBackwardAt S.limit.maps t (torusQuarterTurn a) =
        torusQuarterTurn (positivePairBackwardAt S.limit.maps t a) := by
  have hex (n : ℕ) := exists_fourfoldPlanarEulerParticleSystem hw hB hwB hwrot
    (by positivity : 0 ≤ (n : ℝ) + 1)
  choose A hA using hex
  let V := planarBiotSavartMassBound B (∫ y, ‖planarBoxSource w y‖)
  let C : ℝ := 8 * (B + ∫ y, ‖planarBoxSource w y‖)
  have hV : 0 ≤ V := by unfold V planarBiotSavartMassBound; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hspeed (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1)) (x : R2) :
      ‖(A n).velocity t x‖ ≤ V :=
    (A n).norm_velocity_le (integrable_planarBoxSource hw) (norm_planarBoxSource_le hB hwB) ht x
  have hlog (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1)) (x y : R2)
      (hxy : ‖x - y‖ ≤ 1 / 2) : ‖(A n).velocity t x - (A n).velocity t y‖ ≤
      C * logFlowModulus ‖x - y‖ :=
    (A n).velocity_logFlowModulus_le (integrable_planarBoxSource hw)
      (norm_planarBoxSource_le hB hwB) ht hxy
  obtain ⟨H, φ, hφ, hlim⟩ := exists_compactOpen_expandingPlanarFlow_subseq hC hV
    (fun n => (A n).particles) hspeed hlog
  obtain ⟨hleft, hright, harea, hinit⟩ := positivePlanarFlow_limit_inverse_area
    (fun n => (A n).particles) (fun n => (A n).forward_area)
    (fun n t _ => (A n).backward_area t) hφ hlim
  let S : ExpandingPlanarEulerLimit (planarBoxSource w) := {
    system := A
    V := V
    C := C
    speed_nonneg := hV
    modulus_nonneg := hC
    speed := hspeed
    modulus := hlog
    limit := ⟨H, hleft, hright, fun t => (harea t).1, fun t => (harea t).2, hinit⟩
    indices := φ
    indices_strictMono := hφ
    converges := hlim
  }
  refine ⟨S, ?_⟩
  intro t a
  have hf (x : R2) : Tendsto (fun n => (A (φ n)).particles.forward t x)
      atTop (𝓝 (positivePairForwardAt H t x)) :=
    (((continuous_eval_const (t, x)).tendsto H).comp hlim).fst_nhds
  have hb (x : R2) : Tendsto (fun n => (A (φ n)).particles.backward t x)
      atTop (𝓝 (positivePairBackwardAt H t x)) :=
    (((continuous_eval_const (t, x)).tendsto H).comp hlim).snd_nhds
  constructor
  · have htime : ∀ᶠ n : ℕ in atTop, (t : ℝ) ≤ (φ n : ℝ) + 1 := by
      filter_upwards [eventually_ge_atTop (⌈(t : ℝ)⌉₊)] with n hn
      have he : (⌈(t : ℝ)⌉₊ : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hn.trans (hφ.id_le n)
      have hc : (t : ℝ) ≤ (⌈(t : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      linarith
    have hr := (torusQuarterTurn_smooth.continuous.tendsto
      (positivePairForwardAt H t a)).comp (hf a)
    exact tendsto_nhds_unique (hf (torusQuarterTurn a))
      (hr.congr' (htime.mono fun n hn => ((hA (φ n)).forward t ⟨t.coe_nonneg, hn⟩ a).symm))
  · have hr := (torusQuarterTurn_smooth.continuous.tendsto
      (positivePairBackwardAt H t a)).comp (hb a)
    exact tendsto_nhds_unique (hb (torusQuarterTurn a))
      (hr.congr' (Eventually.of_forall fun n => ((hA (φ n)).backward t a).symm))

structure IsFourfoldGlobalPlanarEulerParticleSystem {w : R2 → ℝ}
    (S : GlobalPlanarEulerParticleSystem w) : Prop where
  forward : ∀ t, 0 ≤ t → ∀ a, S.forward t (torusQuarterTurn a) = torusQuarterTurn (S.forward t a)
  backward : ∀ t a, S.backward t (torusQuarterTurn a) = torusQuarterTurn (S.backward t a)

theorem exists_fourfoldGlobalPlanarEulerParticleSystem {w : R2 → ℝ} {B : ℝ}
    (hw : Integrable w μT) (hB : 0 ≤ B) (hwB : ∀ x ∈ torusBox, ‖w x‖ ≤ B)
    (hwrot : ∀ x, planarBoxSource w (torusQuarterTurn x) = planarBoxSource w x) :
    ∃ E : GlobalPlanarEulerParticleSystem (planarBoxSource w),
      IsFourfoldGlobalPlanarEulerParticleSystem E := by
  obtain ⟨S, hrot⟩ := exists_fourfoldExpandingPlanarEulerLimit hw hB hwB hwrot
  let F : ℝ≥0 → R2 → R2 := fun t a => positivePairForwardAt S.limit.maps t a
  let v := S.limit.velocity
  have hFc : Continuous (Function.uncurry F) := S.limit.maps.continuous.fst
  have hvc : Continuous (Function.uncurry v) :=
    S.limit.continuous_velocity (integrable_planarBoxSource hw) (norm_planarBoxSource_le hB hwB)
  have hInt : ∀ (t : ℝ≥0) a,
      F t a = a + ∫ s in (0 : ℝ)..(t : ℝ), positiveParticleDerivative v F s a :=
    S.particle_integral_eq (integrable_planarBoxSource hw) (norm_planarBoxSource_le hB hwB)
  let X := positiveParticleIntegralExtension v F
  let Y : ℝ → R2 → R2 := fun t a => positivePairBackwardAt S.limit.maps t.toNNReal a
  have hXeq (t : ℝ) (ht : 0 ≤ t) (a : R2) : X t a = F t.toNNReal a := by
    simpa only [Real.coe_toNNReal t ht] using positiveParticleIntegralExtension_eq hInt t.toNNReal a
  let E : GlobalPlanarEulerParticleSystem (planarBoxSource w) := {
    velocity := positiveParticleVelocityExtension v
    forward := X
    backward := Y
    continuous_velocity := continuous_positiveParticleVelocityExtension hvc
    continuous_forward := continuous_positiveParticleIntegralExtension hvc hFc
    continuous_backward := S.limit.maps.continuous.snd.comp
      ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
    initial := positiveParticleIntegralExtension_zero v F
    derivative := fun t ht a => positiveParticleIntegralExtension_hasDerivAt_nonneg hvc hFc hInt ht a
    left_inv := by
      intro t ht a
      rw [hXeq t ht a]
      exact S.limit.left_inv t.toNNReal a
    right_inv := by
      intro t ht a
      rw [hXeq t ht (Y t a)]
      exact S.limit.right_inv t.toNNReal a
    forward_area := by
      intro t ht
      have he : X t = F t.toNNReal := funext (hXeq t ht)
      rw [he]
      exact S.limit.forward_area t.toNNReal
    backward_area := fun t => S.limit.backward_area t.toNNReal
    selfconsistent := fun t x => rfl
  }
  refine ⟨E, { forward := ?_, backward := ?_ }⟩
  · intro t ht a
    change X t (torusQuarterTurn a) = torusQuarterTurn (X t a)
    rw [hXeq t ht, hXeq t ht]
    exact (hrot t.toNNReal a).1
  · intro t a
    exact (hrot t.toNNReal a).2

theorem IsFourfoldGlobalPlanarEulerParticleSystem.velocity
    {w : R2 → ℝ} {S : GlobalPlanarEulerParticleSystem w}
    (hS : IsFourfoldGlobalPlanarEulerParticleSystem S)
    (hwrot : ∀ x, w (torusQuarterTurn x) = w x) (t : ℝ) (x : R2) :
    S.velocity t (torusQuarterTurn x) = perpJ (S.velocity t x) := by
  rw [S.selfconsistent, S.selfconsistent]
  apply planarKernelVelocity_torusQuarterTurn kernelK_perpJ
  intro y
  rw [hS.backward, hwrot]

end Euler2D

end
