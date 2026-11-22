import CubeSections.Integer.Target
import CubeSections.Geometry.Blocks
import Mathlib.Algebra.BigOperators.Fin

/-! Finite balanced partitions with the exact quotient/remainder multiplicities. -/
noncomputable section
open scoped BigOperators
namespace CubeSections

/-- The first r blocks have size q+1; the remaining blocks have size q. -/
def balancedSizes (n k : ℕ) (j : Fin k) : ℕ :=
  n / k + if (j : ℕ) < n % k then 1 else 0

theorem balancedSizes_pos {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (j : Fin k) :
    0 < balancedSizes n k j := by
  have hq := quotient_pos hk hkn
  unfold balancedSizes
  omega

theorem balancedSizes_balanced (n k : ℕ) (j : Fin k) :
    balancedSizes n k j = n / k ∨ balancedSizes n k j = n / k + 1 := by
  unfold balancedSizes
  split <;> simp_all

theorem sum_balancedSizes {n k : ℕ} (hk : 1 ≤ k) :
    ∑ j : Fin k, balancedSizes n k j = n := by
  have hr := remainder_lt (n := n) hk
  simp only [balancedSizes, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_boole, Fin.card_filter_val_lt, min_eq_right (Nat.le_of_lt hr)]
  simpa [Nat.add_comm] using (Nat.mod_add_div n k)

namespace BlockData

/-- A canonical finite equivalence enumerating blocks of the prescribed sizes. -/
def sizesEquiv {n k : ℕ} (s : Fin k → ℕ) (hsum : ∑ j, s j = n) :
    (Σ j : Fin k, Fin (s j)) ≃ Fin n :=
  finSigmaFinEquiv.trans (finCongr hsum)

/-- Construct a surjective block assignment with any prescribed positive sizes. -/
def ofSizes {n k : ℕ} (s : Fin k → ℕ) (hpos : ∀ j, 0 < s j)
    (hsum : ∑ j, s j = n) : BlockData n k where
  block i := ((sizesEquiv s hsum).symm i).1
  onto j := ⟨sizesEquiv s hsum ⟨j, ⟨0, hpos j⟩⟩, by simp⟩
  negative _ := false

theorem blockSize_ofSizes {n k : ℕ} (s : Fin k → ℕ) (hpos : ∀ j, 0 < s j)
    (hsum : ∑ j, s j = n) (j : Fin k) :
    (ofSizes s hpos hsum).blockSize j = s j := by
  let e := sizesEquiv s hsum
  have hc : (Finset.univ : Finset (Fin (s j))).card =
      (Finset.univ.filter (fun i : Fin n => (e.symm i).1 = j)).card := by
    apply Finset.card_bij (fun a _ => e ⟨j, a⟩)
    · intro a ha
      simp
    · intro a₁ ha₁ a₂ ha₂ h
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using e.injective h
    · intro b hb
      have hb' : (e.symm b).1 = j := by simpa using hb
      rcases h : e.symm b with ⟨j', a⟩
      have hj : j' = j := by simpa [h] using hb'
      subst j'
      refine ⟨a, by simp, ?_⟩
      simpa using (congrArg e h).symm
  unfold blockSize
  have hf : Finset.univ.filter (fun i => (ofSizes s hpos hsum).block i = j) =
      Finset.univ.filter (fun i : Fin n => (e.symm i).1 = j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hf]
  simpa only [Finset.card_univ, Fintype.card_fin] using hc.symm

theorem card_large_of_balanced {n k : ℕ} (d : BlockData n k) (h : d.IsBalanced) :
    (Finset.univ.filter (fun j => d.blockSize j = n / k + 1)).card = n % k :=
  CubeSections.card_large_of_balanced d.blockSize d.sum_blockSize h

theorem prod_blockSize_of_balanced {n k : ℕ} (d : BlockData n k) (h : d.IsBalanced) :
    (∏ j, d.blockSize j) = (n / k) ^ (k - n % k) * (n / k + 1) ^ (n % k) :=
  prod_of_balanced d.blockSize d.sum_blockSize h

end BlockData

/-- An explicit finite construction of balanced block data in every admissible dimension. -/
def balancedBlockData {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : BlockData n k :=
  BlockData.ofSizes (balancedSizes n k) (balancedSizes_pos hk hkn) (sum_balancedSizes hk)

theorem balancedBlockData_isBalanced {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (balancedBlockData hk hkn).IsBalanced := by
  intro j
  change (BlockData.ofSizes _ _ _).blockSize j = n / k ∨
    (BlockData.ofSizes _ _ _).blockSize j = n / k + 1
  rw [BlockData.blockSize_ofSizes]
  exact balancedSizes_balanced n k j

theorem exists_balancedBlockData {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ d : BlockData n k, d.IsBalanced :=
  ⟨balancedBlockData hk hkn, balancedBlockData_isBalanced hk hkn⟩

end CubeSections
