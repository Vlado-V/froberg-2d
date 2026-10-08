import Quartic.BilinearCoefficientKernel

/-!
# Rank contributed by coefficient injections

A coordinatewise relation map has c times its original kernel dimension.
On any injected coefficient space of dimension h, its restriction therefore
has rank at least h-c*d. These are the actual linear-algebra codimensions
used for the four pure motions and the c mixed motions, once their proved
coefficient injections are supplied.
-/
noncomputable section
namespace Quartic.CoefficientConstraintRank
open Module
variable {K V W T : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]
  [AddCommGroup T] [Module K T] [FiniteDimensional K T] {c : ℕ}

/-- Apply the same actual relation map to every coefficient component. -/
def repeated (L : V →ₗ[K] W) : (Fin c → V) →ₗ[K] (Fin c → W) :=
  LinearMap.pi fun i => L.comp (LinearMap.proj i)

omit [FiniteDimensional K V] in
@[simp] theorem repeated_apply (L : V →ₗ[K] W) (x : Fin c → V) (i : Fin c) :
    repeated L x i = L (x i) := rfl

/-- The repeated kernel is exactly the product of the original kernels. -/
def kernelEquiv (L : V →ₗ[K] W) : LinearMap.ker (repeated (c := c) L) ≃ₗ[K] (Fin c → LinearMap.ker L) where
  toFun x i := ⟨x.val i,congrFun x.property i⟩
  invFun x := ⟨fun i => (x i).val, by ext i; exact (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_kernel (L : V →ₗ[K] W) :
    finrank K (LinearMap.ker (repeated (c := c) L)) = c * finrank K (LinearMap.ker L) := by
  rw [(kernelEquiv (c := c) L).finrank_eq]
  rw [Module.finrank_pi_fintype]
  simp

/-- Repetition multiplies the actual relation rank by the number of components. -/
theorem finrank_range (L : V →ₗ[K] W) :
    finrank K (LinearMap.range (repeated (c := c) L)) = c * finrank K (LinearMap.range L) := by
  have h := (repeated (c := c) L).finrank_range_add_finrank_ker
  rw [finrank_kernel,Module.finrank_pi_fintype] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  have hL := L.finrank_range_add_finrank_ker
  rw [← hL,Nat.mul_add] at h
  omega

omit [FiniteDimensional K T] in
/-- A coefficient injection restricts the ambient relation kernel without
increasing its dimension. -/
theorem kernel_bound (L : V →ₗ[K] W) (ι : T →ₗ[K] (Fin c → V)) (hι : Function.Injective ι) :
    finrank K (LinearMap.ker ((repeated L).comp ι)) ≤ c * finrank K (LinearMap.ker L) := by
  let f : LinearMap.ker ((repeated L).comp ι) →ₗ[K] LinearMap.ker (repeated L) :=
    { toFun := fun x => ⟨ι x.val,x.property⟩
      map_add' := fun x y => Subtype.ext (ι.map_add _ _)
      map_smul' := fun s x => Subtype.ext (ι.map_smul _ _) }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply hι
    exact congrArg Subtype.val h
  have hb := LinearMap.finrank_le_finrank_of_injective hf
  rw [finrank_kernel] at hb
  exact hb

/-- The restriction to an injected h-dimensional coefficient space imposes
at least h-c*d independent linear conditions. -/
theorem rank_bound (L : V →ₗ[K] W) (ι : T →ₗ[K] (Fin c → V)) (hι : Function.Injective ι) :
    finrank K T - c * finrank K (LinearMap.ker L) ≤
      finrank K (LinearMap.range ((repeated L).comp ι)) := by
  have hk := kernel_bound L ι hι
  have hn := ((repeated L).comp ι).finrank_range_add_finrank_ker
  omega

/-- Additive form avoids truncated subtraction in subsequent integer counts. -/
theorem dimension_le_rank_add (L : V →ₗ[K] W) (ι : T →ₗ[K] (Fin c → V)) (hι : Function.Injective ι) :
    finrank K T ≤ finrank K (LinearMap.range ((repeated L).comp ι)) + c * finrank K (LinearMap.ker L) := by
  have hk := kernel_bound L ι hι
  have hn := ((repeated L).comp ι).finrank_range_add_finrank_ker
  omega

end Quartic.CoefficientConstraintRank
