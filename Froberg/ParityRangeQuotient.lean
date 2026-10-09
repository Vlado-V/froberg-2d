module

public import Froberg.OddQuotientProduct
public import Froberg.WeightedRename

@[expose] public section

/-! The actual odd part of an endpoint quotient is the quotient of the
odd homogeneous polynomial space by its actual product relations. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] {n d r : ℕ}

def parityPartForms (w : Fin n → ZMod 2) (p : ZMod 2) :
    Submodule K (Forms K n d) :=
  (weightedHomogeneousSubmodule K w p).comap (Forms K n d).subtype

instance parityPartFormsGroup (w : Fin n → ZMod 2) (p : ZMod 2) :
    AddCommGroup (parityPartForms (K := K) (d := d) w p) :=
  Submodule.addCommGroup _

instance parityPartFormsModule (w : Fin n → ZMod 2) (p : ZMod 2) :
    Module K (parityPartForms (K := K) (d := d) w p) :=
  Submodule.module _

theorem parityForm_range (w : Fin n → ZMod 2) (p : ZMod 2) :
    (parityForm (K := K) (d := d) w p).range=parityPartForms w p := by
  ext f
  constructor
  · rintro ⟨g,rfl⟩
    exact parityForm_homogeneous w p g
  · intro hf
    exact ⟨f,parityForm_same w p f hf⟩

def parityPartPolynomialEquiv (w : Fin n → ZMod 2) (p : ZMod 2) :
    parityPartForms (K := K) (d := d) w p ≃ₗ[K]
      homogeneousParitySpace K (Fin n) d w p where
  toFun f := ⟨f.val.val,⟨f.val.property,f.property⟩⟩
  invFun f := ⟨⟨f.val,f.property.1⟩,f.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The quotient equivalence is induced by inclusion of actual odd forms,
followed by the actual target quotient map. -/
def parityRangeQuotientEquiv (R : Submodule K (Forms K n d))
    (w : Fin n → ZMod 2) (p : ZMod 2) :
    (↥(parityPartForms (K := K) (d := d) w p) ⧸
      (R.comap (parityPartForms (K := K) (d := d) w p).subtype)) ≃ₗ[K]
      (R.mkQ.comp (parityForm w p)).range := by
  let S := parityPartForms (K := K) (d := d) w p
  let F := R.mkQ.comp S.subtype
  have hker : F.ker=R.comap S.subtype := by
    rw [LinearMap.ker_comp,Submodule.ker_mkQ]
  have hrange : F.range=(R.mkQ.comp (parityForm w p)).range := by
    rw [LinearMap.range_comp,Submodule.range_subtype,LinearMap.range_comp,parityForm_range]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (F.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

def endpointOddQuotientEquiv (w : Fin n → ZMod 2) (q : Fin r → Forms K n d) :
    (↥(parityPartForms (K := K) (d := 2*d) w 1) ⧸
      ((projectedEndpointMultiplication (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q).range).comap
        (parityPartForms (K := K) (d := 2*d) w 1).subtype) ≃ₗ[K] oddTargetSpace w q :=
  parityRangeQuotientEquiv _ w 1

end Froberg
