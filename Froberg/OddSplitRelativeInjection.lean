import Froberg.OddSplitComplex
import Froberg.OddEvenTargetExtension

/-! Exactness of the complete odd coefficient row forces injectivity of
the literal relative multiplication map after adjoining even generators. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

theorem odd_split_relative_injective
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0)
    (hex : OddSplitExact (Fin.append Q E) (Fin.append F G)) :
    Function.Injective (oddEvenRelativeMap Q F G E) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro a ha
  choose v hv using fun i => (oddBackgroundCoefficientRelations F G).mkQ_surjective (a i)
  have haeq : a=fun i => (oddBackgroundCoefficientRelations F G).mkQ (v i) := funext fun i => (hv i).symm
  rw [haeq,oddEvenRelativeMap_mk] at ha
  have hmem : evenScalarOddFamily E v∈fullOddRelations Q F G :=
    (Submodule.Quotient.mk_eq_zero _).mp ha
  obtain ⟨z,hz,w,hw,heq⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hz
  obtain ⟨c,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  obtain ⟨t,rfl⟩ := hw
  subst z
  have hpoly : (∑ i,(Q i).val*(c i).val)+
      (∑ i,(F i).val*(b i).val)+(∑ i,(G i).val*(t i).val)=
        ∑ i,(E i).val*(v i).val := by
    have hh := congrArg Subtype.val heq
    simpa only [Submodule.coe_add,privateEvenCoefficientMap_val,
      evenScalarOddFamily,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,
      Submodule.coe_sum,evenScalarOddProduct,LinearMap.coe_mk,AddHom.coe_mk] using hh
  have hcycle : (∑ i,(Fin.append Q E i).val*(Fin.append (-c) v i).val)+
      (∑ i,(Fin.append F G i).val*(Fin.append (-b) (-t) i).val)=0 := by
    simp only [Fin.sum_univ_add,Fin.append_left,Fin.append_right,Pi.neg_apply,
      Submodule.coe_neg,mul_neg,Finset.sum_neg_distrib]
    linear_combination -hpoly
  obtain ⟨C,hC,hC'⟩ := hex (Fin.append (-c) v) (Fin.append (-b) (-t)) hcycle
  rw [haeq]
  funext i
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have he : v i=∑ j,C (i.natAdd q) j • Fin.append F G j := by
    apply Subtype.ext
    simpa only [Fin.append_right,Submodule.coe_sum,Submodule.coe_smul] using hC (i.natAdd q)
  rw [he]
  apply (oddBackgroundCoefficientRelations F G).sum_mem
  intro j _
  apply (oddBackgroundCoefficientRelations F G).smul_mem
  refine Fin.addCases ?_ ?_ j
  · intro k
    rw [Fin.append_left]
    apply (show Submodule.span K (Set.range F)≤oddBackgroundCoefficientRelations F G from le_sup_left)
    exact Submodule.subset_span ⟨k,rfl⟩
  · intro k
    rw [Fin.append_right]
    apply (show Submodule.span K (Set.range G)≤oddBackgroundCoefficientRelations F G from le_sup_right)
    exact Submodule.subset_span ⟨k,rfl⟩

end Froberg
