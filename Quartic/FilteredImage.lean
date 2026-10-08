import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# Finite filtered subspaces and their initial multiplication images

Successive quotients of a finite flag preserve total dimension. A compatible
linear map induces maps on these quotients, whose total image dimension is at
most the original image dimension. This is finite-dimensional linear algebra;
no parameter space, degeneration family, or geometric properness is assumed.
-/

noncomputable section
namespace Quartic.FilteredImage
open Module
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The previous flag piece, regarded inside the next piece. -/
def previousIn (A B : Submodule K V) : Submodule K B := A.comap B.subtype

/-- An actual successive quotient. -/
abbrev Layer (A B : Submodule K V) := B ⧸ previousIn A B

/-- Rank-nullity for the quotient layer before using an inclusion of flag steps. -/
theorem layer_finrank_add_previous [FiniteDimensional K V] (A B : Submodule K V) :
    finrank K (Layer A B) + finrank K (previousIn A B) = finrank K B := by
  exact (previousIn A B).finrank_quotient_add_finrank

/-- Exact dimension accounting for one step of a flag. -/
theorem layer_finrank_add [FiniteDimensional K V] (A B : Submodule K V) (hAB : A ≤ B) :
    finrank K (Layer A B) + finrank K A = finrank K B := by
  have h := layer_finrank_add_previous A B
  have he : finrank K (previousIn A B) = finrank K A :=
    (Submodule.comapSubtypeEquivOfLe hAB).finrank_eq
  rwa [he] at h

/-- A map which takes the old source piece into `P` descends to the next quotient.
The codomain is the ambient quotient; when `f(B)≤Q`, its image lies in `Q/P`. -/
def layerMap (f : V →ₗ[K] W) (A B : Submodule K V) (P : Submodule K W)
    (hf : A.map f ≤ P) : Layer A B →ₗ[K] W ⧸ P :=
  (previousIn A B).liftQ (P.mkQ.comp (f.comp B.subtype)) (by
    intro x hx
    change P.mkQ (f x.val) = 0
    exact (Submodule.Quotient.mk_eq_zero P).mpr (hf ⟨x.val, hx, rfl⟩))

@[simp] theorem layerMap_mk (f : V →ₗ[K] W) (A B : Submodule K V) (P : Submodule K W)
    (hf : A.map f ≤ P) (x : B) :
    layerMap f A B P hf (Submodule.Quotient.mk x) = P.mkQ (f x.val) := rfl

/-- The induced layer map has exactly the expected quotient image. -/
theorem range_layerMap (f : V →ₗ[K] W) (A B : Submodule K V) (P : Submodule K W)
    (hf : A.map f ≤ P) :
    LinearMap.range (layerMap f A B P hf) = (B.map f).map P.mkQ := by
  rw [layerMap, Submodule.range_liftQ, LinearMap.range_comp, LinearMap.range_comp]
  simp

/-- Compatibility with a next target step puts the initial image in that step. -/
theorem range_layerMap_le (f : V →ₗ[K] W) (A B : Submodule K V) (P Q : Submodule K W)
    (hfA : A.map f ≤ P) (hfB : B.map f ≤ Q) :
    LinearMap.range (layerMap f A B P hfA) ≤ Q.map P.mkQ := by
  rw [range_layerMap]
  exact Submodule.map_mono hfB

/-- Quotienting an image by a subspace containing `A` loses at least `dim A`. -/
theorem quotient_image_finrank_add_le [FiniteDimensional K W]
    (A B P : Submodule K W) (hAB : A ≤ B) (hAP : A ≤ P) :
    finrank K (B.map P.mkQ) + finrank K A ≤ finrank K B := by
  let q := layerMap (LinearMap.id : W →ₗ[K] W) A B P (by simpa using hAP)
  have hq := q.finrank_range_le
  have hr : LinearMap.range q = B.map P.mkQ := by simp [q, range_layerMap]
  rw [hr] at hq
  have hd := layer_finrank_add A B hAB
  omega

/-- The rank budget for one actual associated-graded map. -/
theorem layerMap_finrank_add_le [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (A B : Submodule K V) (P : Submodule K W)
    (hAB : A ≤ B) (hfA : A.map f ≤ P) :
    finrank K (LinearMap.range (layerMap f A B P hfA)) + finrank K (A.map f) ≤
      finrank K (B.map f) := by
  rw [range_layerMap]
  exact quotient_image_finrank_add_le (A.map f) (B.map f) P (Submodule.map_mono hAB) hfA

/-- Dimension telescopes along any finite initial segment of an increasing flag. -/
theorem sum_layer_finrank [FiniteDimensional K V]
    (F : ℕ → Submodule K V) (hF : Monotone F) (n : ℕ) :
    (∑ i ∈ Finset.range n, finrank K (Layer (F i) (F (i + 1)))) + finrank K (F 0) =
      finrank K (F n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := layer_finrank_add (F n) (F (n + 1)) (hF (Nat.le_succ n))
    omega

section ProductMaps
variable {ι : Type*} {U Z : ι → Type*}
  [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
  [∀ i, AddCommGroup (Z i)] [∀ i, Module K (Z i)]

/-- The image of a block-diagonal map is the product of its block images. -/
def rangePiMapEquiv (f : ∀ i, U i →ₗ[K] Z i) :
    LinearMap.range (LinearMap.piMap f) ≃ₗ[K] ((i : ι) → LinearMap.range (f i)) where
  toFun x i := ⟨x.val i, by
    obtain ⟨u, hu⟩ := x.property
    exact ⟨u i, congrFun hu i⟩⟩
  invFun y := ⟨fun i => (y i).val, by
    choose u hu using fun i => (y i).property
    exact ⟨u, funext hu⟩⟩
  left_inv x := Subtype.ext rfl
  right_inv y := funext fun _ => Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_range_piMap [Fintype ι] [∀ i, FiniteDimensional K (U i)]
    (f : ∀ i, U i →ₗ[K] Z i) :
    finrank K (LinearMap.range (LinearMap.piMap f)) = ∑ i, finrank K (LinearMap.range (f i)) := by
  rw [(rangePiMapEquiv f).finrank_eq, Module.finrank_pi_fintype]

end ProductMaps

/-- The finite direct sum of actual associated-graded source pieces. -/
abbrev AssociatedGraded (F : ℕ → Submodule K V) (n : ℕ) :=
  (i : Fin n) → Layer (F i.val) (F (i.val + 1))

theorem associatedGraded_finrank_add [FiniteDimensional K V]
    (F : ℕ → Submodule K V) (hF : Monotone F) (n : ℕ) :
    finrank K (AssociatedGraded F n) + finrank K (F 0) = finrank K (F n) := by
  rw [Module.finrank_pi_fintype]
  have hs := Fin.sum_univ_eq_sum_range
    (fun i => finrank K (Layer (F i) (F (i + 1)))) n
  rw [hs]
  exact sum_layer_finrank F hF n

/-- A flag beginning at zero and ending at `S` preserves the dimension of `S`. -/
theorem associatedGraded_finrank [FiniteDimensional K V]
    (F : ℕ → Submodule K V) (hF : Monotone F) (n : ℕ) (S : Submodule K V)
    (hzero : F 0 = ⊥) (hend : F n = S) : finrank K (AssociatedGraded F n) = finrank K S := by
  have h := associatedGraded_finrank_add F hF n
  rw [hzero, hend, finrank_bot, add_zero] at h
  exact h

/-- Compatible filtered images obey the telescoped rank budget. -/
theorem sum_layerMap_finrank [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (F : ℕ → Submodule K V) (G : ℕ → Submodule K W)
    (hF : Monotone F) (hf : ∀ i, (F i).map f ≤ G i) (n : ℕ) :
    (∑ i ∈ Finset.range n,
      finrank K (LinearMap.range (layerMap f (F i) (F (i + 1)) (G i) (hf i)))) +
        finrank K ((F 0).map f) ≤ finrank K ((F n).map f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := layerMap_finrank_add_le f (F n) (F (n + 1)) (G n)
      (hF (Nat.le_succ n)) (hf n)
    omega

/-- In particular, the sum of ranks after passing to initial pieces cannot
exceed the image dimension of the original map. -/
theorem sum_layerMap_finrank_le [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (F : ℕ → Submodule K V) (G : ℕ → Submodule K W)
    (hF : Monotone F) (hf : ∀ i, (F i).map f ≤ G i) (n : ℕ)
    (S : Submodule K V) (hend : F n = S) :
    (∑ i ∈ Finset.range n,
      finrank K (LinearMap.range (layerMap f (F i) (F (i + 1)) (G i) (hf i)))) ≤
        finrank K (S.map f) := by
  have h := sum_layerMap_finrank f F G hF hf n
  rw [hend] at h
  omega

/-- Restrict an ambient flag to a subspace. -/
def subspaceFlag (S : Submodule K V) (F : ℕ → Submodule K V) : ℕ → Submodule K V :=
  fun i => S ⊓ F i

theorem subspaceFlag_monotone (S : Submodule K V) (F : ℕ → Submodule K V)
    (hF : Monotone F) : Monotone (subspaceFlag S F) :=
  fun _ _ hij => inf_le_inf_left S (hF hij)

/-- The associated initial pieces of an arbitrary subspace have its exact dimension. -/
theorem subspace_associatedGraded_finrank [FiniteDimensional K V]
    (S : Submodule K V) (F : ℕ → Submodule K V) (hF : Monotone F) (n : ℕ)
    (hzero : F 0 = ⊥) (htop : F n = ⊤) :
    finrank K (AssociatedGraded (subspaceFlag S F) n) = finrank K S :=
  associatedGraded_finrank _ (subspaceFlag_monotone S F hF) n S
    (by simp [subspaceFlag, hzero]) (by simp [subspaceFlag, htop])

/-- Initial pieces of the restricted map have no larger total image dimension. -/
theorem subspace_initial_image_bound [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (S : Submodule K V) (F : ℕ → Submodule K V) (G : ℕ → Submodule K W)
    (hF : Monotone F) (hf : ∀ i, (F i).map f ≤ G i) (n : ℕ) (htop : F n = ⊤) :
    (∑ i ∈ Finset.range n, finrank K (LinearMap.range
      (layerMap f (S ⊓ F i) (S ⊓ F (i + 1)) (G i)
        ((Submodule.map_mono inf_le_right).trans (hf i))))) ≤ finrank K (S.map f) := by
  apply sum_layerMap_finrank_le f (subspaceFlag S F) G
    (subspaceFlag_monotone S F hF) _ n S
  simp [subspaceFlag, htop]

/-- The actual block-diagonal map on all successive quotients. -/
def associatedMap (f : V →ₗ[K] W) (F : ℕ → Submodule K V) (G : ℕ → Submodule K W)
    (hf : ∀ i, (F i).map f ≤ G i) (n : ℕ) :
    AssociatedGraded F n →ₗ[K] ((i : Fin n) → W ⧸ G i.val) :=
  LinearMap.piMap fun i => layerMap f (F i.val) (F (i.val + 1)) (G i.val) (hf i.val)

theorem associatedMap_range_finrank [FiniteDimensional K V]
    (f : V →ₗ[K] W) (F : ℕ → Submodule K V) (G : ℕ → Submodule K W)
    (hf : ∀ i, (F i).map f ≤ G i) (n : ℕ) :
    finrank K (LinearMap.range (associatedMap f F G hf n)) =
      ∑ i ∈ Finset.range n,
        finrank K (LinearMap.range (layerMap f (F i) (F (i + 1)) (G i) (hf i))) := by
  rw [associatedMap, finrank_range_piMap]
  exact Fin.sum_univ_eq_sum_range (fun i =>
    finrank K (LinearMap.range (layerMap f (F i) (F (i + 1)) (G i) (hf i)))) n

/-- Passing a filtered linear map to its initial pieces cannot increase rank. -/
theorem associatedMap_rank_le [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (F : ℕ → Submodule K V) (G : ℕ → Submodule K W)
    (hF : Monotone F) (hf : ∀ i, (F i).map f ≤ G i) (n : ℕ)
    (S : Submodule K V) (hend : F n = S) :
    finrank K (LinearMap.range (associatedMap f F G hf n)) ≤ finrank K (S.map f) := by
  rw [associatedMap_range_finrank]
  exact sum_layerMap_finrank_le f F G hF hf n S hend

section OrderedCoordinates
variable {n : ℕ} (E : Fin n → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

/-- The first `k` components in an ordered finite direct sum. -/
def coordinateFlag (k : ℕ) : Submodule K ((i : Fin n) → E i) where
  carrier := {x | ∀ i, k ≤ i.val → x i = 0}
  zero_mem' _ _ := rfl
  add_mem' hx hy i hi := by simp [hx i hi, hy i hi]
  smul_mem' c _ hx i hi := by simp [hx i hi]

theorem coordinateFlag_monotone : Monotone (coordinateFlag (K := K) E) := by
  intro a b hab x hx i hi
  exact hx i (hab.trans hi)

@[simp] theorem coordinateFlag_zero : coordinateFlag (K := K) E 0 = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  funext i
  exact hx i (Nat.zero_le _)

@[simp] theorem coordinateFlag_end : coordinateFlag (K := K) E n = ⊤ := by
  apply top_unique
  intro x _ i hi
  exact False.elim (Nat.not_le_of_lt i.isLt hi)

/-- The actual initial component of a subspace in a chosen coordinate. -/
def initialPiece (S : Submodule K ((i : Fin n) → E i)) (i : Fin n) : Submodule K (E i) :=
  (S ⊓ coordinateFlag E (i.val + 1)).map (LinearMap.proj i)

/-- Projection to the newly appearing coordinate on a filtered subspace. -/
def initialProjection (S : Submodule K ((i : Fin n) → E i)) (i : Fin n) :
    ↥(S ⊓ coordinateFlag E (i.val + 1)) →ₗ[K] E i :=
  (LinearMap.proj i).comp (S ⊓ coordinateFlag E (i.val + 1)).subtype

theorem initialProjection_range (S : Submodule K ((i : Fin n) → E i)) (i : Fin n) :
    LinearMap.range (initialProjection E S i) = initialPiece E S i := by
  rw [initialProjection, LinearMap.range_comp]
  simp [initialPiece]

/-- Killing the new coordinate is exactly returning to the preceding flag step. -/
theorem initialProjection_ker (S : Submodule K ((i : Fin n) → E i)) (i : Fin n) :
    LinearMap.ker (initialProjection E S i) =
      previousIn (S ⊓ coordinateFlag E i.val) (S ⊓ coordinateFlag E (i.val + 1)) := by
  ext x
  change x.val i = 0 ↔ x.val ∈ S ∧ ∀ j, i.val ≤ j.val → x.val j = 0
  constructor
  · intro hx
    refine ⟨x.property.1, ?_⟩
    intro j hj
    by_cases hij : i.val = j.val
    · have he : i = j := Fin.ext hij
      subst j
      exact hx
    · exact x.property.2 j (by omega)
  · intro hx
    exact hx.2 i le_rfl

/-- Each concrete initial component has the dimension of the corresponding quotient layer. -/
theorem initialPiece_finrank [∀ i, FiniteDimensional K (E i)]
    (S : Submodule K ((i : Fin n) → E i)) (i : Fin n) :
    finrank K (initialPiece E S i) =
      finrank K (Layer (S ⊓ coordinateFlag E i.val) (S ⊓ coordinateFlag E (i.val + 1))) := by
  have h := (initialProjection E S i).finrank_range_add_finrank_ker
  rw [initialProjection_range, initialProjection_ker] at h
  have hq := layer_finrank_add_previous (S ⊓ coordinateFlag E i.val)
    (S ⊓ coordinateFlag E (i.val + 1))
  omega

/-- The initial components of every subspace preserve its total dimension. -/
theorem sum_initialPiece_finrank [∀ i, FiniteDimensional K (E i)]
    (S : Submodule K ((i : Fin n) → E i)) :
    (∑ i : Fin n, finrank K (initialPiece E S i)) = finrank K S := by
  have h := subspace_associatedGraded_finrank S (coordinateFlag E)
    (coordinateFlag_monotone E) n (coordinateFlag_zero E) (coordinateFlag_end E)
  rw [Module.finrank_pi_fintype] at h
  simp_rw [initialPiece_finrank]
  exact h

end OrderedCoordinates

end Quartic.FilteredImage
