import Froberg.ParityRangeQuotient

/-! The coefficient quotient in each parity has exactly the projected
constant-generator relations, rather than all ideal relations. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} [Field K] {n d r : ℕ}

def parityProjectionToPart (w : Fin n → ZMod 2) (p : ZMod 2) :
    Forms K n d →ₗ[K] parityPartForms (K := K) (d := d) w p :=
  (parityForm w p).codRestrict _ (parityForm_homogeneous w p)

@[simp] theorem parityProjectionToPart_val (w : Fin n → ZMod 2) (p : ZMod 2)
    (v : Forms K n d) : (parityProjectionToPart w p v).val=parityForm w p v := rfl

theorem parity_source_relations_eq_span (w : Fin n → ZMod 2) (p : ZMod 2)
    (e : Fin r → ZMod 2) (q : Fin r → Forms K n d)
    (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i)) :
    (Submodule.span K (Set.range q)).comap (parityPartForms w p).subtype=
      Submodule.span K (Set.range (fun i => parityProjectionToPart w p (q i))) := by
  have hs : Submodule.span K (Set.range (fun i => parityProjectionToPart w p (q i)))=
      (Submodule.span K (Set.range q)).map (parityProjectionToPart w p) := by
    rw [Submodule.map_span,←Set.range_comp]
    rfl
  rw [hs]
  ext v
  constructor
  · intro hv
    refine ⟨v.val,hv,?_⟩
    apply Subtype.ext
    exact parityForm_same w p v.val v.property
  · rintro ⟨a,ha,rfl⟩
    exact parity_preserves_generator_span w e q hq p ha

def oddSourceQuotientEquiv (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i)) :
    (parityPartForms (K := K) (d := d) w 1 ⧸
      Submodule.span K (Set.range (fun i => parityProjectionToPart w 1 (q i)))) ≃ₗ[K]
      oddCoefficientSpace w q :=
  (Submodule.quotEquivOfEq _ _ (parity_source_relations_eq_span w 1 e q hq).symm).trans
    (parityRangeQuotientEquiv (Submodule.span K (Set.range q)) w 1)

end Froberg
