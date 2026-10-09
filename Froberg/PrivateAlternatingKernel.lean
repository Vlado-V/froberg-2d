module

public import Froberg.PrivatePolynomialMap
public import Froberg.Koszul

@[expose] public section

/-! The private polynomial row has no more than its constant alternating
relations. The proof uses the literal coefficients of its polynomial kernel. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PrivateColumns
open Module
variable {K : Type*} [Field K] {a z s b h c : ℕ}

/-- Extraction of a scalar-monomial coefficient as an output vector. -/
def privateSourceCoefficientMap (i : Fin b) (α : Fin (a+z) →₀ ℕ) :
    (Fin b → Fin h → Forms K (a+z) s) →ₗ[K] (Fin h → K) where
  toFun v := privateSourceCoefficient v i α
  map_add' v w := by
    funext j
    simp only [privateSourceCoefficient,Pi.add_apply,Submodule.coe_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply]
  map_smul' k v := by
    funext j
    simp only [privateSourceCoefficient,Pi.smul_apply,Submodule.coe_smul,MvPolynomial.coeff_smul,
      RingHom.id_apply]

/-- Each unordered pair has one candidate constant alternating coefficient. -/
def privateAlternatingCoefficients (ι : Fin b ↪ Fin z)
    (dual : Fin b → (Fin h → K) →ₗ[K] K) :
    (Fin b → Fin h → Forms K (a+z) s) →ₗ[K] (GeneratorPair b → K) :=
  LinearMap.pi fun p => (dual p.val.2).comp
    (privateSourceCoefficientMap p.val.1 (privateExponent a s ι p.val.2))

/-- Every actual private-row relation is determined by these pair coefficients.
The two-output hypothesis is precisely the one-dimensional product overlap. -/
theorem privateAlternatingCoefficients_injective_on_kernel (hs : 0 < s)
    (ι : Fin b ↪ Fin z) (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i, Function.Injective (A i)) (w : Fin b → Fin h → K)
    (dual : Fin b → (Fin h → K) →ₗ[K] K) (hdual : ∀ i, dual i (w i)=1)
    (hpair : ∀ p : GeneratorPair b, ∀ x y,
      A p.val.1 x + A p.val.2 y=0 → ∃ t : K,
        x=t • w p.val.2 ∧ y=(-t) • w p.val.1) :
    Function.Injective ((privateAlternatingCoefficients (a := a) (s := s) ι dual).comp
      (privatePolynomialMap (a := a) (s := s) ι A).ker.subtype) := by
  classical
  have hker : ∀ v : (privatePolynomialMap (a := a) (s := s) ι A).ker,
      privateAlternatingCoefficients (a := a) (s := s) ι dual v.val=0 → v=0 := by
    intro v hv
    have hrel := privatePolynomialMap_relation ι A v.val v.property
    have hcoeff (i : Fin b) (α : Fin (a+z) →₀ ℕ) (hα : α.degree=s) :
        privateSourceCoefficient v.val i α=0 := by
      by_cases hp : ∃ j, i ≠ j ∧ α=privateExponent a s ι j
      · obtain ⟨j,hij,rfl⟩ := hp
        rcases lt_or_gt_of_ne hij with hij' | hji'
        · let p : GeneratorPair b := ⟨(i,j),hij'⟩
          have hr := private_relation_pair hs ι A (privateSourceCoefficient v.val)
            (fun β _ => hrel β) i j hij
          obtain ⟨t,ht,ht'⟩ := hpair p _ _ hr
          have hc : dual j (privateSourceCoefficient v.val i (privateExponent a s ι j))=0 :=
            congrFun hv p
          rw [ht,map_smul,hdual,smul_eq_mul,mul_one] at hc
          rw [ht,hc,zero_smul]
        · let p : GeneratorPair b := ⟨(j,i),hji'⟩
          have hr := private_relation_pair hs ι A (privateSourceCoefficient v.val)
            (fun β _ => hrel β) j i (Ne.symm hij)
          obtain ⟨t,ht,ht'⟩ := hpair p _ _ hr
          have hc : dual i (privateSourceCoefficient v.val j (privateExponent a s ι i))=0 :=
            congrFun hv p
          rw [ht,map_smul,hdual,smul_eq_mul,mul_one] at hc
          rw [ht',hc,neg_zero,zero_smul]
      · apply private_relation_support hs ι A hA (privateSourceCoefficient v.val)
          (fun β _ => hrel β) i α hα
        intro j hij he
        exact hp ⟨j,hij,he⟩
    apply Subtype.ext
    funext i j
    apply Subtype.ext
    apply MvPolynomial.ext
    intro α
    by_cases hα : α.degree=s
    · exact congrFun (hcoeff i α hα) j
    · exact (v.val i j).property.coeff_eq_zero hα
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker (x-y)
  change privateAlternatingCoefficients (a := a) (s := s) ι dual (x.val-y.val)=0
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

/-- Consequently the actual polynomial kernel has at most one scalar
parameter per unordered pair of private generators. -/
theorem privatePolynomialMap_kernel_finrank_le (hs : 0 < s)
    (ι : Fin b ↪ Fin z) (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i, Function.Injective (A i)) (w : Fin b → Fin h → K)
    (dual : Fin b → (Fin h → K) →ₗ[K] K) (hdual : ∀ i, dual i (w i)=1)
    (hpair : ∀ p : GeneratorPair b, ∀ x y,
      A p.val.1 x + A p.val.2 y=0 → ∃ t : K,
        x=t • w p.val.2 ∧ y=(-t) • w p.val.1) :
    finrank K (privatePolynomialMap (a := a) (s := s) ι A).ker ≤ b.choose 2 := by
  have hi := privateAlternatingCoefficients_injective_on_kernel (a := a) hs ι A hA w dual hdual hpair
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  simpa [Module.finrank_pi_fintype,card_generatorPair] using hd

end Froberg.PrivateColumns
