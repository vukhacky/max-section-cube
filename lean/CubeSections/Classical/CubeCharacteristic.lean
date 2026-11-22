import CubeSections.Classical.IntervalFourier
import CubeSections.Analysis.CouplingLift
import Mathlib.MeasureTheory.Constructions.Pi

/-! The actual cube probability law and its projected characteristic function.
These identities establish the π and volume normalization before Fourier
inversion. They do not identify a pointwise section density at zero.
-/
noncomputable section
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace CubeSections

def cubeUniformMeasure (n : ℕ) : Measure (E n) :=
  (Measure.pi (fun _ : Fin n => unitIntervalMeasure)).map (WithLp.toLp 2)

instance cubeUniformMeasure_probability (n : ℕ) : IsProbabilityMeasure (cubeUniformMeasure n) := by
  unfold cubeUniformMeasure
  infer_instance

theorem cubeUniformMeasure_eq_restrict (n : ℕ) :
    cubeUniformMeasure n = volume.restrict (cube n) := by
  have hpre : (WithLp.toLp 2 : (Fin n → ℝ) → E n) ⁻¹' cube n =
      Set.univ.pi (fun _ : Fin n => Icc (-(1/2 : ℝ)) (1/2 : ℝ)) := by
    ext x
    simp only [mem_preimage, cube, mem_setOf_eq, mem_pi, mem_univ, forall_const,
      mem_Icc, abs_le]
  have hpres := (PiLp.volume_preserving_toLp (Fin n)).restrict_preimage (cube_compact n).measurableSet
  rw [hpre] at hpres
  have hpi : (volume : Measure (Fin n → ℝ)).restrict
      (Set.univ.pi (fun _ : Fin n => Icc (-(1/2 : ℝ)) (1/2 : ℝ))) =
      Measure.pi (fun _ : Fin n => unitIntervalMeasure) := by
    change (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict _ = _
    rw [Measure.restrict_pi_pi]
    rfl
  rw [hpi] at hpres
  exact hpres.map_eq

theorem charFun_cubeUniformMeasure (n : ℕ) (t : E n) :
    charFun (cubeUniformMeasure n) t = ∏ i : Fin n, (Real.sinc (t i/2) : ℂ) := by
  rw [cubeUniformMeasure, charFun_pi]
  simp_rw [charFun_unitIntervalMeasure]

theorem charFun_cubeUniformMeasure_two_pi (n : ℕ) (t : E n) :
    charFun (cubeUniformMeasure n) ((2*Real.pi) • t) =
      ∏ i : Fin n, (Real.sinc (Real.pi*t i) : ℂ) := by
  rw [charFun_cubeUniformMeasure]
  apply Finset.prod_congr rfl
  intro i hi
  congr 2
  change 2*Real.pi*t i/2 = Real.pi*t i
  ring

theorem charFun_frameAdjoint_cube (U : Frame n k) (t : E k) :
    charFun ((cubeUniformMeasure n).map (frameAdjoint U)) t =
      charFun (cubeUniformMeasure n) (U t) := by
  rw [charFun_apply, charFun_apply, integral_map]
  · apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      dsimp only
      rw [frameAdjoint, ContinuousLinearMap.adjoint_inner_left]
      rfl)
  · exact (frameAdjoint U).measurable.aemeasurable
  · fun_prop

theorem charFun_projectedCube_two_pi (U : Frame n k) (t : E k) :
    charFun ((cubeUniformMeasure n).map (frameAdjoint U)) ((2*Real.pi) • t) =
      ∏ i : Fin n, (Real.sinc (Real.pi*(U t) i) : ℂ) := by
  rw [charFun_frameAdjoint_cube, U.map_smul]
  exact charFun_cubeUniformMeasure_two_pi n (U t)

theorem charFun_projectedCube_neg_two_pi (U : Frame n k) (t : E k) :
    charFun ((cubeUniformMeasure n).map (frameAdjoint U)) ((-2*Real.pi) • t) =
      ∏ i : Fin n, (Real.sinc (Real.pi*(U t) i) : ℂ) := by
  have hvec : (-2*Real.pi) • t = (2*Real.pi) • (-t) := by module
  rw [hvec, charFun_projectedCube_two_pi, U.map_neg]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [PiLp.neg_apply, mul_neg, Real.sinc_neg]

#print axioms cubeUniformMeasure_eq_restrict
#print axioms charFun_projectedCube_two_pi
end CubeSections
