module

public import Froberg.PreparedPrivateCommonOpen
public import Froberg.IntrinsicPrivateBoundary

@[expose] public section

/-! The row-two private boundary and zero later boundaries are one fixed
finite complex. Its exactness yields both ordinary row exactness and the
private separation used by coefficient elimination. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K]
theorem addRow_private_mem_of_exact
    {A B U Z V : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] [AddCommGroup Z] [Module K Z] [AddCommGroup V] [Module K V]
    (F : A →ₗ[K] V) (P : B →ₗ[K] V) (C : U →ₗ[K] A) (D : Z →ₗ[K] B)
    (h : (addRow F P).ker=(C.prodMap D).range)
    (a : A) (b : B) (hab : F a+P b=0) : b∈D.range := by
  have hx : (a,b)∈(addRow F P).ker := hab
  rw [h] at hx
  obtain ⟨⟨c,z⟩,hz⟩ := hx
  exact ⟨z,congrArg Prod.snd hz⟩

theorem addRow_ordinary_exact
    {A B U Z V : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] [AddCommGroup Z] [Module K Z] [AddCommGroup V] [Module K V]
    (F : A →ₗ[K] V) (P : B →ₗ[K] V) (C : U →ₗ[K] A) (D : Z →ₗ[K] B)
    (h : (addRow F P).ker=(C.prodMap D).range) : F.ker=C.range := by
  apply le_antisymm
  · intro a ha
    have hx : (a,0)∈(addRow F P).ker := by
      change F a+P 0=0
      rw [map_zero,add_zero]
      exact ha
    rw [h] at hx
    obtain ⟨⟨c,z⟩,hc⟩ := hx
    exact ⟨c,congrArg Prod.fst hc⟩
  · rintro _ ⟨c,rfl⟩
    have hx : (C c,0)∈(addRow F P).ker := by
      rw [h]
      exact ⟨(c,0),by simp only [LinearMap.prodMap_apply,map_zero]⟩
    change F (C c)+P 0=0 at hx
    change F (C c)=0
    simpa only [map_zero,add_zero] using hx

theorem range_prodMap_zero_eq_inl
    {A B U Z : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] [AddCommGroup Z] [Module K Z]
    (C : U →ₗ[K] A) : (C.prodMap (0 : Z →ₗ[K] B)).range=
      ((LinearMap.inl K A B).comp C).range := by
  ext x
  constructor
  · rintro ⟨⟨c,z⟩,rfl⟩
    exact ⟨c,rfl⟩
  · rintro ⟨c,rfl⟩
    exact ⟨(c,0),rfl⟩

namespace PreparedParameters
variable [Infinite K] {σ : Type*} [Fintype σ] {n d q b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

def privateBoundaryAt (P : Fin b → FullBiform K σ n 1 (d-1)) (R : ℕ) :
    (Fin b → Fin b → K) →ₗ[K] PrivateRowSource (K := K) (σ := σ) (n := n) (d := d) (b := b) R := by
  classical
  by_cases hR : R=2
  · subst R
    exact intrinsicPrivateBoundary P
  · exact 0

@[simp] theorem privateBoundaryAt_two (P : Fin b → FullBiform K σ n 1 (d-1)) :
    privateBoundaryAt P 2=intrinsicPrivateBoundary P := by
  simp [privateBoundaryAt]

theorem privateBoundaryAt_ne (P : Fin b → FullBiform K σ n 1 (d-1))
    {R : ℕ} (hR : R≠2) : privateBoundaryAt P R=0 := by
  simp only [privateBoundaryAt,dif_neg hR]

theorem privateBoundaryAt_cycle (P : Fin b → FullBiform K σ n 1 (d-1)) (R : ℕ) :
    (privateRowMap (d := d) (fun i => (P i).val) R).comp (privateBoundaryAt P R)=0 := by
  by_cases hR : R=2
  · subst R
    rw [privateBoundaryAt_two]
    exact intrinsicPrivateBoundary_cycle P
  · rw [privateBoundaryAt_ne P hR,LinearMap.comp_zero]

theorem private_row_ordinary_exact
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (R : J) (p : Space n d q J counts O)
    (P : Fin b → FullBiform K σ n 1 (d-1))
    (h : (privateAugmentedRow hO R p (fun i => (P i).val)).ker=
      ((rowConstants hO R p).prodMap (privateBoundaryAt P R.val)).range) :
    (row hO R p).ker=(rowConstants hO R p).range :=
  addRow_ordinary_exact _ _ _ _ h

theorem private_row_separated
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (R : J) (hR : R.val≠2) (p : Space n d q J counts O)
    (P : Fin b → FullBiform K σ n 1 (d-1))
    (h : (privateAugmentedRow hO R p (fun i => (P i).val)).ker=
      ((rowConstants hO R p).prodMap (privateBoundaryAt P R.val)).range) :
    ∀ x u,row hO R p x+privateRowMap (d := d) (fun i => (P i).val) R.val u=0 → u=0 := by
  intro x u hu
  have hh := addRow_private_mem_of_exact _ _ _ _ h x u hu
  simpa only [privateBoundaryAt_ne P hR,LinearMap.range_zero,Submodule.mem_bot] using hh

end PreparedParameters
end Froberg
