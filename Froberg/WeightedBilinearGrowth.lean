module

public import Quartic.WeightedInitialImage
public import Quartic.BilinearImage
public import Froberg.WeightedExpansion

@[expose] public section

/-! A dimension inequality tensorizes over any ordered, biregular
multiplication table. The proof uses actual initial subspaces and weighted
incidence, without a genericity hypothesis. -/
noncomputable section
namespace Froberg
open Module Quartic.FilteredImage Quartic.WeightedInitialImage
variable {K B V W I : Type*} [Field K]
  [AddCommGroup B] [Module K B] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W]
  [Fintype I] [DecidableEq I] {n q : ℕ}

/-- Each incident source initial fiber satisfies the original image bound
inside the corresponding target initial fiber. -/
theorem initial_fiber_growth
    (μ : B →ₗ[K] V →ₗ[K] W)
    (ν : (I → B) →ₗ[K] (Fin n → V) →ₗ[K] (Fin q → W))
    (shift : I → Fin n → Fin q) (hshift : ∀ i, StrictMono (shift i))
    (hν : ∀ i j b v, ν (Pi.single i b) (Pi.single j v) =
      Pi.single (shift i j) (μ b v))
    (a b : ℕ) (hμ : ∀ S : Submodule K V,
      b * finrank K S ≤ a * finrank K (Quartic.BilinearImage.image μ S))
    (L : Submodule K (Fin n → V)) (i : I) (j : Fin n) :
    b * finrank K (initialPiece (fun _ : Fin n => V) L j) ≤
      a * finrank K (initialPiece (fun _ : Fin q => W)
        (multiplicationImage ν L) (shift i j)) := by
  have hgrade : ∀ i j (u : B) (v : V) k, k ≠ shift i j →
      ν (Pi.single i u) (Pi.single j v) k = 0 := by
    intro i j u v k hk
    rw [hν]
    simp [hk]
  have hincl : Quartic.BilinearImage.image μ
      (initialPiece (fun _ : Fin n => V) L j) ≤
      initialPiece (fun _ : Fin q => W) (multiplicationImage ν L) (shift i j) := by
    apply iSup_le
    intro u
    rintro _ ⟨v,hv,rfl⟩
    have hp := homogeneous_initial_product_mem ν shift hshift hgrade L i j u v hv
    rw [hν] at hp
    have hh := (mem_initialSubspace _ _ _).mp hp (shift i j)
    simpa [Nat.mul_comm] using hh
  exact (hμ _).trans (Nat.mul_le_mul_left a (Submodule.finrank_mono hincl))

/-- Biregular weighted incidence transfers the original dimension ratio to
all subspaces of the coefficient direct sum. -/
theorem weighted_bilinear_growth
    (μ : B →ₗ[K] V →ₗ[K] W)
    (ν : (I → B) →ₗ[K] (Fin n → V) →ₗ[K] (Fin q → W))
    (shift : I → Fin n → Fin q) (hshift : ∀ i, StrictMono (shift i))
    (hν : ∀ i j b v, ν (Pi.single i b) (Pi.single j v) =
      Pi.single (shift i j) (μ b v))
    (weight : Fin q → Fin n → ℕ) (C D : ℕ)
    (hrow : ∀ k, ∑ j, weight k j = C)
    (hcol : ∀ j, ∑ k, weight k j = D)
    (hC : 0 < C)
    (hsupport : ∀ k j, 0 < weight k j → ∃ i, shift i j = k)
    (a b : ℕ) (hμ : ∀ S : Submodule K V,
      b * finrank K S ≤ a * finrank K (Quartic.BilinearImage.image μ S))
    (L : Submodule K (Fin n → V)) :
    b * q * finrank K L ≤ a * n * finrank K (multiplicationImage ν L) := by
  classical
  let x (j : Fin n) := finrank K (initialPiece (fun _ : Fin n => V) L j)
  let y (k : Fin q) := finrank K (initialPiece (fun _ : Fin q => W)
    (multiplicationImage ν L) k)
  have hxy (k : Fin q) (j : Fin n) :
      weight k j * (b * x j) ≤ weight k j * (a * y k) := by
    by_cases hw : weight k j = 0
    · simp [hw]
    · obtain ⟨i,hi⟩ := hsupport k j (Nat.pos_of_ne_zero hw)
      have hg := initial_fiber_growth μ ν shift hshift hν a b hμ L i j
      rw [hi] at hg
      exact Nat.mul_le_mul_left (weight k j) hg
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hxy k j))
  have hleft : (∑ k, ∑ j, weight k j * (b * x j)) = D*b*finrank K L := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,hcol]
    simp_rw [← Nat.mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    exact sum_initialPiece_finrank _ _
  have hright : (∑ k, ∑ j, weight k j * (a * y k)) =
      C*a*finrank K (multiplicationImage ν L) := by
    simp_rw [← Finset.sum_mul,hrow]
    simp_rw [← Nat.mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    exact sum_initialPiece_finrank _ _
  rw [hleft,hright] at hsum
  have htotal : D*n=C*q := by
    have h := weighted_total weight C D hrow hcol
    simpa [Nat.mul_comm] using h
  apply Nat.le_of_mul_le_mul_left (c := C)
  · calc
      C*(b*q*finrank K L) = n*(D*b*finrank K L) := by
        calc
          _ = (C*q)*(b*finrank K L) := by ring
          _ = (D*n)*(b*finrank K L) := by rw [htotal]
          _ = _ := by ring
      _ ≤ n*(C*a*finrank K (multiplicationImage ν L)) := Nat.mul_le_mul_left n hsum
      _ = C*(a*n*finrank K (multiplicationImage ν L)) := by ring
  · exact hC

end Froberg
