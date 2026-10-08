import Quartic.FilteredImage

/-! # Prefix initial pieces under ordered blockwise coordinate equivalences -/
noncomputable section
namespace Quartic.FilteredCoordinates
open Module FilteredImage
variable {K : Type*} [Field K] {n m : ℕ}
variable {E : Fin n → Type*} {F : Fin m → Type*}
  [∀ i,AddCommGroup (E i)] [∀ i,Module K (E i)]
  [∀ i,AddCommGroup (F i)] [∀ i,Module K (F i)]

/-- Membership in a leading coefficient space uses exactly the later zero coordinates. -/
theorem mem_initialPiece_iff (S : Submodule K ((i : Fin n) → E i))
    (i : Fin n) (v : E i) :
    v ∈ initialPiece E S i ↔ ∃ x,x ∈ S ∧ (∀ j,i<j → x j=0) ∧ x i=v := by
  constructor
  · rintro ⟨x,⟨hx,hflag⟩,he⟩
    exact ⟨x,hx,fun j hj => hflag j (by omega),he⟩
  · rintro ⟨x,hx,hzero,he⟩
    exact ⟨x,⟨hx,fun j hj => hzero j (by omega)⟩,he⟩

/-- Ordered blockwise equivalences preserve the actual leading coefficient spaces. -/
theorem initialPiece_map (σ : Fin m ≃o Fin n)
    (e : ((i : Fin n) → E i) ≃ₗ[K] ((j : Fin m) → F j))
    (c : ∀ j,E (σ j) ≃ₗ[K] F j)
    (he : ∀ x j,e x j=c j (x (σ j)))
    (S : Submodule K ((i : Fin n) → E i)) (j : Fin m) :
    initialPiece F (S.map e.toLinearMap) j=(initialPiece E S (σ j)).map (c j).toLinearMap := by
  ext v
  rw [mem_initialPiece_iff]
  constructor
  · rintro ⟨y,⟨x,hx,rfl⟩,hzero,hy⟩
    refine ⟨x (σ j),?_,?_⟩
    · change x (σ j) ∈ initialPiece E S (σ j)
      rw [mem_initialPiece_iff]
      refine ⟨x,hx,?_,rfl⟩
      intro k hk
      have hz := hzero (σ.symm k) (by
        apply σ.lt_iff_lt.mp
        simpa using hk)
      change e x (σ.symm k)=0 at hz
      rw [he] at hz
      have hz' := (c (σ.symm k)).injective (hz.trans (c (σ.symm k)).map_zero.symm)
      have transport (l : Fin n) (h : l=k) (hz : x l=0) : x k=0 := by
        subst l
        exact hz
      exact transport _ (σ.apply_symm_apply k) hz'
    · change e x j=v at hy
      rw [he] at hy
      exact hy
  · rintro ⟨v,hv,rfl⟩
    change v ∈ initialPiece E S (σ j) at hv
    rw [mem_initialPiece_iff] at hv
    obtain ⟨x,hx,hzero,rfl⟩ := hv
    refine ⟨e x,⟨x,hx,rfl⟩,?_,he x j⟩
    intro k hk
    rw [he,hzero (σ k) (σ.strictMono hk),map_zero]

/-- In particular the prefix profile is preserved, with the same ordered indices. -/
theorem initialPiece_finrank_map
    (σ : Fin m ≃o Fin n)
    (e : ((i : Fin n) → E i) ≃ₗ[K] ((j : Fin m) → F j))
    (c : ∀ j,E (σ j) ≃ₗ[K] F j)
    (he : ∀ x j,e x j=c j (x (σ j)))
    (S : Submodule K ((i : Fin n) → E i)) (j : Fin m) :
    finrank K (initialPiece F (S.map e.toLinearMap) j)=
      finrank K (initialPiece E S (σ j)) := by
  rw [initialPiece_map σ e c he,(c j).finrank_map_eq]

end Quartic.FilteredCoordinates
