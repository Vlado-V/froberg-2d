module

public import Froberg.BilinearKoszulRow
public import Froberg.BiformParitySpaces
public import Froberg.PolynomialComplexOpen

@[expose] public section

/-! The complete odd coefficient complex for any even/odd generator split.
Its exactness is a polynomial open condition on the actual two families. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

def evenOddProduct : biformParitySpace K h m d 0 →ₗ[K]
    biformParitySpace K h m d 1 →ₗ[K] biformParitySpace K h m (2*d) 1 :=
  LinearMap.mk₂ K (fun a b => ⟨a.val*b.val,by
    refine ⟨?_,?_⟩
    · change (a.val*b.val).IsHomogeneous (2*d)
      simpa only [two_mul] using a.property.1.mul b.property.1
    · change (a.val*b.val).IsWeightedHomogeneous (fun i => (blockWeight h m i : ZMod 2)) 1
      simpa only [zero_add] using a.property.2.mul b.property.2⟩)
    (fun _ _ _ => Subtype.ext (add_mul _ _ _))
    (fun _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ => Subtype.ext (mul_add _ _ _))
    (fun _ _ _ => Subtype.ext (mul_smul_comm _ _ _))

def OddSplitExact (Q : Fin q → biformParitySpace K h m d 0)
    (E : Fin f → biformParitySpace K h m d 1) : Prop :=
  ∀ (u : Fin q → biformParitySpace K h m d 1)
    (v : Fin f → biformParitySpace K h m d 0),
    (∑ i,(Q i).val*(u i).val)+(∑ j,(E j).val*(v j).val)=0 →
    ∃ C : Fin q → Fin f → K,
      (∀ i,(u i).val=∑ j,C i j • (E j).val) ∧
      (∀ j,(v j).val = -∑ i,C i j • (Q i).val)

theorem odd_split_exact_iff_kernel
    (Q : Fin q → biformParitySpace K h m d 0)
    (E : Fin f → biformParitySpace K h m d 1) :
    OddSplitExact Q E ↔
      (bilinearKoszulRow evenOddProduct Q E (0 : (Fin 0 → K) →ₗ[K] biformParitySpace K h m (2*d) 1)).ker=
        (bilinearKoszulConstants (W := Fin 0 → K) Q E).range := by
  classical
  constructor
  · intro hex
    apply le_antisymm
    · rintro ⟨⟨u,v⟩,w⟩ hw
      have hr : (∑ i,(Q i).val*(u i).val)+(∑ j,(E j).val*(v j).val)=0 := by
        have hv := congrArg Subtype.val hw
        simpa only [bilinearKoszulRow,LinearMap.coe_mk,AddHom.coe_mk,evenOddProduct,
          LinearMap.mk₂_apply,Submodule.coe_add,Submodule.coe_sum,LinearMap.zero_apply,
          Submodule.coe_zero,add_zero,mul_comm] using hv
      obtain ⟨C,hC,hC'⟩ := hex u v hr
      refine ⟨C,?_⟩
      apply Prod.ext
      · apply Prod.ext
        · funext i
          apply Subtype.ext
          simpa only [bilinearKoszulConstants,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_neg] using (hC i).symm
        · funext j
          apply Subtype.ext
          simpa only [bilinearKoszulConstants,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_neg] using (hC' j).symm
      · exact Subsingleton.elim _ _
    · rintro x ⟨C,rfl⟩
      exact LinearMap.congr_fun (bilinearKoszulRow_constants evenOddProduct Q E
        (0 : (Fin 0 → K) →ₗ[K] biformParitySpace K h m (2*d) 1)) C
  · intro hex u v hr
    have hw : ((u,v),(0 : Fin 0 → K))∈
        (bilinearKoszulRow evenOddProduct Q E (0 : (Fin 0 → K) →ₗ[K] biformParitySpace K h m (2*d) 1)).ker := by
      apply Subtype.ext
      simpa only [bilinearKoszulRow,LinearMap.coe_mk,AddHom.coe_mk,evenOddProduct,
        LinearMap.mk₂_apply,Submodule.coe_add,Submodule.coe_sum,LinearMap.zero_apply,
        Submodule.coe_zero,add_zero,mul_comm] using hr
    rw [hex] at hw
    obtain ⟨C,hC⟩ := hw
    refine ⟨C,?_,?_⟩
    · intro i
      simpa only [bilinearKoszulConstants,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_neg] using (congrArg (fun x => (x.1.1 i).val) hC).symm
    · intro j
      simpa only [bilinearKoszulConstants,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_neg] using (congrArg (fun x => (x.1.2 j).val) hC).symm

theorem odd_split_exact_principal_open {ι : Type*}
    (Q : Fin q → (ι → K) → biformParitySpace K h m d 0)
    (E : Fin f → (ι → K) → biformParitySpace K h m d 1)
    (hQ : ∀ i,IsPolynomialFamily (Q i)) (hE : ∀ j,IsPolynomialFamily (E j))
    (p₀ : ι → K) (hex : OddSplitExact (fun i => Q i p₀) (fun j => E j p₀)) :
    ∃ P : MvPolynomial ι K,eval p₀ P≠0 ∧
      ∀ p,eval p P≠0 → OddSplitExact (fun i => Q i p) (fun j => E j p) := by
  let Z := (0 : (Fin 0 → K) →ₗ[K] biformParitySpace K h m (2*d) 1)
  obtain ⟨P,hP,hgood⟩ := complex_exact_principal_open
    (fun p => bilinearKoszulRow evenOddProduct (fun i => Q i p) (fun j => E j p) Z)
    (fun p => bilinearKoszulConstants (W := Fin 0 → K) (fun i => Q i p) (fun j => E j p))
    (bilinearKoszulRow_polynomial evenOddProduct Q E (fun _ => Z) hQ hE (isPolynomialFamily_const Z))
    (bilinearKoszulConstants_polynomial Q E hQ hE)
    (fun p => bilinearKoszulRow_constants evenOddProduct _ _ Z) p₀
    ((odd_split_exact_iff_kernel _ _).mp hex)
  exact ⟨P,hP,fun p hp => (odd_split_exact_iff_kernel _ _).mpr (hgood p hp)⟩

end Froberg
