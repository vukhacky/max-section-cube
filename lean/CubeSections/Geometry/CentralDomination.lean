import CubeSections.Geometry.AffineSections
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Central domination from midpoint Brunn--Minkowski.
The root-volume inequality is an explicit premise of this geometric implication;
`Geometry.BrunnMinkowski` supplies its proof. Empty fibers and dimension zero
are included.
-/
noncomputable section
open Set MeasureTheory

namespace CubeSections

def midpointMinkowski {k : ℕ} (A B : Set (E k)) : Set (E k) :=
  (fun p : E k × E k => (1/2 : ℝ) • (p.1+p.2)) '' (A ×ˢ B)

theorem midpointMinkowski_compact {k : ℕ} {A B : Set (E k)}
    (hA : IsCompact A) (hB : IsCompact B) : IsCompact (midpointMinkowski A B) := by
  apply (hA.prod hB).image
  fun_prop

/-- The midpoint root-volume Brunn--Minkowski statement for compact convex sets. -/
def MidpointBrunnMinkowski (k : ℕ) : Prop :=
  ∀ A B : Set (E k), IsCompact A → IsCompact B → Convex ℝ A → Convex ℝ B →
    A.Nonempty → B.Nonempty →
    (((volume A).toReal)^((1 : ℝ)/(k : ℝ)) +
      ((volume B).toReal)^((1 : ℝ)/(k : ℝ))) / 2 ≤
      ((volume (midpointMinkowski A B)).toReal)^((1 : ℝ)/(k : ℝ))

theorem midpoint_opposite_affineSlabs_subset {n k : ℕ} (U : Frame n k) (y : E n) :
    midpointMinkowski (affineSlab U y) (affineSlab U (-y)) ⊆ U ⁻¹' cube n := by
  rintro z ⟨⟨x,w⟩,⟨hx,hw⟩,rfl⟩
  exact midpoint_opposite_affineSlabs_mem U y hx hw

/-- Pointwise central domination follows from the genuine root-volume BM
inequality. The reflection and midpoint inclusion are proved for actual fibers. -/
theorem affineVolume_le_sectionVolume_of_midpointBM {n k : ℕ} (U : Frame n k)
    (hBM : MidpointBrunnMinkowski k) (y : E n) :
    affineVolume U y ≤ sectionVolume U := by
  by_cases hk : k = 0
  · subst k
    rw [affineVolume_zeroDimension, zeroDimension_sectionVolume]
    split_ifs <;> norm_num
  have hkR : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk)
  by_cases hA : (affineSlab U y).Nonempty
  · have hB : (affineSlab U (-y)).Nonempty := by
      obtain ⟨x,hx⟩ := hA
      refine ⟨-x,?_⟩
      rw [affineSlab_neg]
      simpa only [mem_preimage, neg_neg] using hx
    have h := hBM (affineSlab U y) (affineSlab U (-y))
      (affineSlab_compact U y) (affineSlab_compact U (-y))
      (affineSlab_convex U y) (affineSlab_convex U (-y)) hA hB
    change ((affineVolume U y)^((1 : ℝ)/(k : ℝ)) +
      (affineVolume U (-y))^((1 : ℝ)/(k : ℝ))) / 2 ≤ _ at h
    rw [affineVolume_neg] at h
    have hroot : (affineVolume U y)^((1 : ℝ)/(k : ℝ)) ≤
        ((volume (midpointMinkowski (affineSlab U y) (affineSlab U (-y)))).toReal)^
          ((1 : ℝ)/(k : ℝ)) := by linarith
    have hvol := (Real.rpow_le_rpow_iff (affineVolume_nonneg U y)
      ENNReal.toReal_nonneg (by positivity : (0 : ℝ) < 1/(k : ℝ))).mp hroot
    exact hvol.trans (ENNReal.toReal_mono (sectionMass_ne_top U)
      (measure_mono (midpoint_opposite_affineSlabs_subset U y)))
  · have hempty : affineSlab U y = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    have hz : affineVolume U y = 0 := by simp [affineVolume,affineMass,hempty]
    rw [hz]
    exact (sectionVolume_pos U).le

theorem affineMass_le_sectionMass_of_midpointBM {n k : ℕ} (U : Frame n k)
    (hBM : MidpointBrunnMinkowski k) (y : E n) : affineMass U y ≤ sectionMass U :=
  (ENNReal.toReal_le_toReal (affineMass_ne_top U y) (sectionMass_ne_top U)).mp
    (affineVolume_le_sectionVolume_of_midpointBM U hBM y)

#print axioms midpoint_opposite_affineSlabs_subset
#print axioms affineVolume_le_sectionVolume_of_midpointBM
#print axioms affineMass_le_sectionMass_of_midpointBM
end CubeSections
