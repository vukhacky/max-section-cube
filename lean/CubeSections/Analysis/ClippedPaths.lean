import CubeSections.Analysis.ClippedDeterminantDerivative
import CubeSections.Analysis.ScalarProduction
import CubeSections.Analysis.FiniteSwitches

/-! Continuous clipped paths and their scalar pair-production derivatives. -/

noncomputable section
open Set Filter
open scoped BigOperators Matrix MatrixOrder Topology

namespace CubeSections

def clippedPotential {n : ℕ} (z : Fin n → ℝ) (t : ℝ) (i : Fin n) : ℝ := min (z i) t

def cutoffActivity {n : ℕ} (z : Fin n → ℝ) (t : ℝ) (i : Fin n) : ℝ :=
  if t < z i then 1 else 0

def cutoffMatrix {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  weightedGram (frameMatrix U) (fun i => Real.exp (clippedPotential z t i - t))

def cutoffActiveMatrix {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin k) (Fin k) ℝ := weightedGram (frameMatrix U) (cutoffActivity z t)

def gramPairProduction {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, gramProjection U i j ^ 2 * phi |z i - z j|

def clippedPairSlope (a b t : ℝ) : ℝ :=
  (if t < a then 1 else 0) * (1 - Real.exp (min b t - t)) +
    (if t < b then 1 else 0) * (1 - Real.exp (min a t - t))

theorem hasDerivAt_clippedPotential {n : ℕ} (z : Fin n → ℝ) (t : ℝ) (i : Fin n)
    (hi : z i ≠ t) :
    HasDerivAt (fun s => clippedPotential z s i) (cutoffActivity z t i) t := by
  by_cases h : t < z i
  · have heq : (fun s : ℝ => min (z i) s) =ᶠ[𝓝 t] (fun s => s) := by
      filter_upwards [eventually_lt_nhds h] with s hs
      exact min_eq_right hs.le
    simpa only [clippedPotential, cutoffActivity, if_pos h] using
      (hasDerivAt_id t).congr_of_eventuallyEq heq
  · have h' : z i < t := lt_of_le_of_ne (le_of_not_gt h) hi
    have heq : (fun s : ℝ => min (z i) s) =ᶠ[𝓝 t] (fun _ => z i) := by
      filter_upwards [eventually_gt_nhds h'] with s hs
      exact min_eq_left hs.le
    simpa only [clippedPotential, cutoffActivity, if_neg h] using
      (hasDerivAt_const t (z i)).congr_of_eventuallyEq heq

theorem hasDerivAt_phi (x : ℝ) : HasDerivAt phi (1 - Real.exp (-x)) x := by
  have h := ((hasDerivAt_id x).sub_const 1).add (hasDerivAt_id x).neg.exp
  convert h using 1
  · rfl
  · dsimp
    ring

theorem hasDerivAt_phi_sub_const (b t : ℝ) :
    HasDerivAt (fun s => phi (s - b)) (1 - Real.exp (b - t)) t := by
  have h := (hasDerivAt_phi (t - b)).comp t ((hasDerivAt_id t).sub_const b)
  simpa only [Function.comp_def, id_eq, neg_sub, mul_one] using h

theorem hasDerivAt_clipped_pair (a b t : ℝ) (ha : a ≠ t) (hb : b ≠ t) :
    HasDerivAt (fun s => phi |min a s - min b s|) (clippedPairSlope a b t) t := by
  by_cases hA : t < a
  · by_cases hB : t < b
    · have heq : (fun s : ℝ => phi |min a s - min b s|) =ᶠ[𝓝 t] (fun _ => phi 0) := by
        filter_upwards [eventually_lt_nhds hA, eventually_lt_nhds hB] with s hsA hsB
        simp only [min_eq_right hsA.le, min_eq_right hsB.le, sub_self, abs_zero]
      have h := (hasDerivAt_const t (phi 0)).congr_of_eventuallyEq heq
      simpa only [clippedPairSlope, if_pos hA, if_pos hB,
        min_eq_right hA.le, min_eq_right hB.le, sub_self, Real.exp_zero,
        sub_self, mul_zero, add_zero] using h
    · have hB' : b < t := lt_of_le_of_ne (le_of_not_gt hB) hb
      have heq : (fun s : ℝ => phi |min a s - min b s|) =ᶠ[𝓝 t] (fun s => phi (s - b)) := by
        filter_upwards [eventually_lt_nhds hA, eventually_gt_nhds hB'] with s hsA hsB
        simp only [min_eq_right hsA.le, min_eq_left hsB.le, abs_of_pos (sub_pos.mpr hsB)]
      have h := (hasDerivAt_phi_sub_const b t).congr_of_eventuallyEq heq
      simpa only [clippedPairSlope, if_pos hA, if_neg hB, min_eq_left hB'.le,
        one_mul, zero_mul, add_zero] using h
  · have hA' : a < t := lt_of_le_of_ne (le_of_not_gt hA) ha
    by_cases hB : t < b
    · have heq : (fun s : ℝ => phi |min a s - min b s|) =ᶠ[𝓝 t] (fun s => phi (s - a)) := by
        filter_upwards [eventually_gt_nhds hA', eventually_lt_nhds hB] with s hsA hsB
        simp only [min_eq_left hsA.le, min_eq_right hsB.le, abs_of_neg (sub_neg.mpr hsA), neg_sub]
      have h := (hasDerivAt_phi_sub_const a t).congr_of_eventuallyEq heq
      simpa only [clippedPairSlope, if_neg hA, if_pos hB, min_eq_left hA'.le,
        one_mul, zero_mul, zero_add] using h
    · have hB' : b < t := lt_of_le_of_ne (le_of_not_gt hB) hb
      have heq : (fun s : ℝ => phi |min a s - min b s|) =ᶠ[𝓝 t]
          (fun _ => phi |a - b|) := by
        filter_upwards [eventually_gt_nhds hA', eventually_gt_nhds hB'] with s hsA hsB
        simp only [min_eq_left hsA.le, min_eq_left hsB.le]
      have h := (hasDerivAt_const t (phi |a - b|)).congr_of_eventuallyEq heq
      simpa only [clippedPairSlope, if_neg hA, if_neg hB, zero_mul, zero_add] using h

theorem hasDerivAt_gramPairProduction_clipped {n k : ℕ} (U : Frame n k)
    (z : Fin n → ℝ) (t : ℝ) (hz : ∀ i, z i ≠ t) :
    HasDerivAt (fun s => gramPairProduction U (clippedPotential z s))
      ((1 / 2 : ℝ) * ∑ i, ∑ j, gramProjection U i j ^ 2 * clippedPairSlope (z i) (z j) t) t := by
  exact (HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun j _ =>
    (hasDerivAt_clipped_pair (z i) (z j) t (hz i) (hz j)).const_mul
      (gramProjection U i j ^ 2)))).const_mul (1 / 2 : ℝ)

theorem cutoffMatrix_posDef {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) (t : ℝ) :
    (cutoffMatrix U z t).PosDef :=
  frame_weightedGram_posDef U _ (fun i => Real.exp_pos _)

theorem cutoffMatrix_le_one {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) (t : ℝ) :
    cutoffMatrix U z t ≤ 1 := by
  apply frame_weightedGram_le_one
  intro i
  exact Real.exp_le_one_iff.mpr (sub_nonpos.mpr (min_le_right (z i) t))

theorem cutoffActiveMatrix_posSemidef {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) (t : ℝ) :
    (cutoffActiveMatrix U z t).PosSemidef := by
  apply weightedGram_posSemidef
  intro i
  unfold cutoffActivity
  split_ifs <;> norm_num

theorem continuous_clipped_determinantRemainder {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) :
    Continuous (fun t => determinantRemainder U (clippedPotential z t)) := by
  have hdet : Continuous (fun t =>
      Matrix.det (weightedGram (frameMatrix U) (fun i => Real.exp (clippedPotential z t i)))) := by
    have heq : (fun t => Matrix.det (weightedGram (frameMatrix U)
        (fun i => Real.exp (clippedPotential z t i)))) =
        (fun t => ∑ f : Fin k → Fin n,
          tupleMinorMass (frameMatrix U) f * Real.exp (tuplePotential f (clippedPotential z t))) := by
      funext t
      exact (frame_exp_tuplePotential_mean U (clippedPotential z t)).symm
    rw [heq]
    unfold tuplePotential clippedPotential
    fun_prop
  unfold determinantRemainder
  apply Continuous.sub
  · exact hdet.log (fun t => ne_of_gt (det_weightedGram_exp_pos U (clippedPotential z t)))
  · change Continuous (fun t : ℝ => ∑ i, leverage U i * min (z i) t)
    fun_prop

theorem continuous_clipped_gramPairProduction {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) :
    Continuous (fun t => gramPairProduction U (clippedPotential z t)) := by
  unfold gramPairProduction clippedPotential phi
  fun_prop

end CubeSections
