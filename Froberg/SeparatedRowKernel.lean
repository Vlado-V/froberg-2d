module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic

@[expose] public section

/-! Exact row kernels after adjoining a separated formal-product block. -/
noncomputable section
namespace Froberg
variable {K A B C V : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup V] [Module K V]

/-- Add one more source block to an actual linear row. -/
def addRow (f : A →ₗ[K] V) (g : B →ₗ[K] V) : (A × B) →ₗ[K] V :=
  f.comp (LinearMap.fst K A B) + g.comp (LinearMap.snd K A B)

@[simp] theorem addRow_apply (f : A →ₗ[K] V) (g : B →ₗ[K] V) (x : A × B) :
    addRow f g x=f x.1+g x.2 := rfl

/-- A projection killing the new layer and fixing formal products permits the
scalar-product disjointness to remove every formal-product coefficient. -/
theorem addRow_kernel_separated
    (S : A →ₗ[K] V) (E : B →ₗ[K] V) (P : C →ₗ[K] V)
    (D : Submodule K V) (T : V →ₗ[K] V)
    (hSD : S.range≤D) (hTD : ∀ x∈D, T x∈D)
    (hTE : T.comp E=0) (hTP : T.comp P=P)
    (hDP : Disjoint D P.range) (hP : Function.Injective P) :
    (addRow (addRow S E) P).ker =
      (addRow S E).ker.map (LinearMap.inl K (A × B) C) := by
  apply le_antisymm
  · rintro ⟨⟨a,b⟩,c⟩ hx
    change S a+E b+P c=0 at hx
    have hTEb : T (E b)=0 := LinearMap.congr_fun hTE b
    have hTPc : T (P c)=P c := LinearMap.congr_fun hTP c
    have ht := congrArg T hx
    simp only [map_add,map_zero,hTEb,hTPc,add_zero] at ht
    have hSa : T (S a)∈D := hTD _ (hSD ⟨a,rfl⟩)
    have hPc : P c∈D := by
      have heq : P c= -T (S a) := eq_neg_of_add_eq_zero_right ht
      rw [heq]
      exact D.neg_mem hSa
    have hPc0 : P c=0 := Submodule.disjoint_def.mp hDP _ hPc ⟨c,rfl⟩
    have hc : c=0 := hP (hPc0.trans (map_zero _).symm)
    refine ⟨(a,b),?_,?_⟩
    · change S a+E b=0
      simpa only [hPc0,add_zero] using hx
    · simp only [LinearMap.inl_apply,hc]
  · rintro x ⟨y,hy,rfl⟩
    change addRow S E y=0 at hy
    change addRow S E y+P 0=0
    simpa only [map_zero,add_zero] using hy

/-- The preceding equality transports an exact mandatory kernel unchanged. -/
theorem addRow_kernel_eq_mandatory
    {U : Type*} [AddCommGroup U] [Module K U]
    (S : A →ₗ[K] V) (E : B →ₗ[K] V) (P : C →ₗ[K] V)
    (D : Submodule K V) (T : V →ₗ[K] V)
    (hSD : S.range≤D) (hTD : ∀ x∈D, T x∈D)
    (hTE : T.comp E=0) (hTP : T.comp P=P)
    (hDP : Disjoint D P.range) (hP : Function.Injective P)
    (Z : U →ₗ[K] (A × B)) (hZ : (addRow S E).ker=Z.range) :
    (addRow (addRow S E) P).ker =
      ((LinearMap.inl K (A × B) C).comp Z).range := by
  rw [addRow_kernel_separated S E P D T hSD hTD hTE hTP hDP hP,hZ]
  exact (LinearMap.range_comp _ _).symm

end Froberg
