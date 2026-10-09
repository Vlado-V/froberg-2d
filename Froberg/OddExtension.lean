module

public import Froberg.OddQuotientProduct

@[expose] public section

/-! Adding even generators leaves the actual odd degree-d quotient unchanged. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The canonical map between the projected parts of two nested quotients. -/
def projectedRangeExtension (P : V →ₗ[K] V) (R E : Submodule K V) :
    (R.mkQ.comp P).range →ₗ[K] ((R ⊔ E).mkQ.comp P).range :=
  ((Submodule.mapQ R (R ⊔ E) LinearMap.id (by simpa using (le_sup_left : R≤R⊔E))).comp
    (R.mkQ.comp P).range.subtype).codRestrict _ (by
      rintro x
      obtain ⟨v,hv⟩ := x.property
      refine ⟨v,?_⟩
      simp only [LinearMap.comp_apply,Submodule.subtype_apply]
      rw [← hv]
      rfl)

/-- A projection kills newly added relations, so its quotient range does not change. -/
theorem projectedRangeExtension_bijective (P : V →ₗ[K] V) (R E : Submodule K V)
    (hP : ∀ v,P (P v)=P v)
    (hR : ∀ v∈R,P v∈R) (hE : E≤P.ker) :
    Function.Bijective (projectedRangeExtension P R E) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨v,hv⟩ := x.property
    have he : (R ⊔ E).mkQ (P v)=0 := by
      have hh := congrArg Subtype.val hx
      change (Submodule.mapQ R (R ⊔ E) LinearMap.id (by simpa using (le_sup_left : R≤R⊔E))) x.val=0 at hh
      rw [← hv] at hh
      exact hh
    have hm : P v∈R⊔E := (Submodule.Quotient.mk_eq_zero _).mp he
    obtain ⟨r,hr,e,he,hre⟩ := Submodule.mem_sup.mp hm
    have hpv : P v∈R := by
      have hpe : P e=0 := hE he
      have hh := congrArg P hre
      rw [map_add,hpe,add_zero,hP] at hh
      rw [← hh]
      exact hR r hr
    apply Subtype.ext
    rw [← hv]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hpv
  · intro x
    obtain ⟨v,hv⟩ := x.property
    refine ⟨⟨R.mkQ (P v),⟨v,rfl⟩⟩,?_⟩
    apply Subtype.ext
    exact hv

def projectedRangeExtensionEquiv (P : V →ₗ[K] V) (R E : Submodule K V)
    (hP : ∀ v,P (P v)=P v)
    (hR : ∀ v∈R,P v∈R) (hE : E≤P.ker) :
    (R.mkQ.comp P).range ≃ₗ[K] ((R ⊔ E).mkQ.comp P).range :=
  LinearEquiv.ofBijective (projectedRangeExtension P R E)
    (projectedRangeExtension_bijective P R E hP hR hE)

end Froberg
