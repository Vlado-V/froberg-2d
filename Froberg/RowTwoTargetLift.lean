module

public import Froberg.BiformTargetLift
public import Froberg.LowRowsCommonOpen

@[expose] public section

/-! The coupled F/E2 row gives a genuine degree-two target lift, with no
higher X-components, in the same actual polynomial product ideal. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] {h m d r q : ℕ}
attribute [local instance] tensorGroup

theorem ambientBiform_regrade_right {j e e' : ℕ} (he : e=e')
    (u : Forms K h j ⊗[K] Forms K m e) :
    ambientBiform (TensorProduct.map LinearMap.id (formsDegreeEquiv he).toLinearMap u)=ambientBiform u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul u v => simp only [TensorProduct.map_tmul,LinearMap.id_apply,ambientBiform_tmul,
      LinearEquiv.coe_coe,formsDegreeEquiv_val]

theorem row_two_deformed_target_lift (hd : 2≤d)
    (pF : Fin r → Poly K (h+m)) (pE : Fin q → Poly K (h+m))
    (hpF : ∀ i,(pF i).IsHomogeneous d) (hpE : ∀ i,(pE i).IsHomogeneous d)
    (gF : Fin r → Forms K h 1 ⊗[K] Forms K m (d-1))
    (gE : Fin q → Forms K h 2 ⊗[K] Forms K m (d-2))
    (htF : ∀ i,coreComponent h m 1 (pF i)=ambientBiform (gF i))
    (htE : ∀ i,coreComponent h m 2 (pE i)=ambientBiform (gE i))
    (huF : ∀ i k,1<k → coreComponent h m k (pF i)=0)
    (huE : ∀ i k,2<k → coreComponent h m k (pE i)=0)
    (hsurj : Function.Surjective
      ((biformTensorFamilyMap (x := 1) (y := d-1) gF).coprod
        (biformTensorFamilyToDegree (x := 0) (by omega : d-2+d=(d-1)+(d-1)) gE)))
    (I : Submodule K (Poly K (h+m)))
    (hIF : (Submodule.span K (Set.range pF))*Forms K (h+m) d≤I)
    (hIE : (Submodule.span K (Set.range pE))*Forms K (h+m) d≤I)
    (v : coreCoefficientSpace K h m (2*d) 2) :
    ∃ z : Forms K (h+m) (2*d),z.val∈I ∧ coreComponent h m 2 z.val=v.val ∧
      ∀ k,2<k → coreComponent h m k z.val=0 := by
  let w : Poly K (h+m) := v.val
  have hw : w∈coreCoefficientSpace K h m (2+((d-1)+(d-1))) 2 := by
    simpa only [show 2+((d-1)+(d-1))=2*d by omega] using v.property
  rw [coreCoefficientSpace_eq_biform_range] at hw
  obtain ⟨u,hu⟩ := hw
  obtain ⟨⟨cF,cE⟩,hc⟩ := hsurj u
  have hF := preparedBiformRow_homogeneous pF hpF cF
  have hE := preparedBiformRow_homogeneous pE hpE cE
  have hz : (preparedBiformRow pF cF+preparedBiformRow pE cE).IsHomogeneous (2*d) := by
    apply IsHomogeneous.add
    · simpa only [show d+(1+(d-1))=2*d by omega] using hF
    · simpa only [show d+(0+d)=2*d by omega] using hE
  refine ⟨⟨preparedBiformRow pF cF+preparedBiformRow pE cE,hz⟩,?_,?_,?_⟩
  · apply I.add_mem
    · apply hIF
      simpa only [show 1+(d-1)=d by omega] using preparedBiformRow_mem_products pF cF
    · apply hIE
      simpa only [Nat.zero_add] using preparedBiformRow_mem_products pE cE
  · change coreComponent h m 2 (preparedBiformRow pF cF+preparedBiformRow pE cE)=w
    have hTF := preparedBiformRow_top pF gF htF cF
    have hTE := preparedBiformRow_top pE gE htE cE
    have hEE : ambientBiform
        (biformTensorFamilyToDegree (x := 0) (by omega : d-2+d=(d-1)+(d-1)) gE cE)=
        ambientBiform (biformTensorFamilyMap gE cE) := by
      exact ambientBiform_regrade_right _ _
    change biformTensorFamilyMap gF cF+
      biformTensorFamilyToDegree (x := 0) (by omega : d-2+d=(d-1)+(d-1)) gE cE=u at hc
    rw [map_add,hTF,hTE,←hEE,←map_add,hc,hu]
  · intro k hk
    change coreComponent h m k (preparedBiformRow pF cF+preparedBiformRow pE cE)=0
    rw [map_add,preparedBiformRow_above pF huF cF (by omega),
      preparedBiformRow_above pE huE cE (by omega),add_zero]

end Froberg
