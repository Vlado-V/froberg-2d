import Froberg.BilinearKoszulRow
import Froberg.BilinearScalarFamily
import Quartic.QuotientBilinearImage

/-! Injectivity of scalar multiplication on the true layer quotient,
together with independent layer products, gives the literal constant
scalar-layer Koszul kernel. No sparse presentation is needed. -/
noncomputable section
namespace Froberg
open Module Quartic
variable {K U V A : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]
variable {q c : ℕ}

theorem scalar_layer_constants_of_quotient_injective
    (mu : V →ₗ[K] U →ₗ[K] A) (Q : Fin q → V) (E : Fin c → U)
    (hE : Function.Injective (BilinearImage.tupleMap mu E))
    (hQ : Function.Injective (BilinearScalarFamily.multiplication
      (QuotientBilinearImage.quotientMap mu (Submodule.span K (Set.range E))) Q))
    (x : Fin q → U) (y : Fin c → V)
    (hrow : (∑ i,mu (Q i) (x i))+(∑ j,mu (y j) (E j))=0) :
    ∃ C : Fin q → Fin c → K,
      (∀ i,x i=∑ j,C i j • E j) ∧
      ∀ j,y j = -∑ i,C i j • Q i := by
  classical
  let R := Submodule.span K (Set.range E)
  let T := BilinearImage.image mu R
  have he0 : T.mkQ (∑ j,mu (y j) (E j))=0 := by
    apply (Submodule.Quotient.mk_eq_zero T).mpr
    exact T.sum_mem fun j _ => BilinearImage.product_mem mu R (y j) (E j)
      (Submodule.subset_span ⟨j,rfl⟩)
  have hx0 : BilinearScalarFamily.multiplication
      (QuotientBilinearImage.quotientMap mu R) Q (fun i => R.mkQ (x i))=0 := by
    rw [BilinearScalarFamily.multiplication_apply]
    simp_rw [QuotientBilinearImage.quotientMap_mk]
    rw [←map_sum]
    have hh := congrArg T.mkQ hrow
    rw [map_add,he0,add_zero,map_zero] at hh
    exact hh
  have hxzero := hQ (hx0.trans (map_zero _).symm)
  have hxmem (i) : x i∈R := by
    apply (Submodule.Quotient.mk_eq_zero R).mp
    exact congrFun hxzero i
  have hc (i) : ∃ a : Fin c → K,∑ j,a j • E j=x i :=
    (Submodule.mem_span_range_iff_exists_fun K).mp (hxmem i)
  choose C hC using hc
  have hb := LinearMap.congr_fun
    (bilinearKoszulRow_constants mu Q E (0 : K →ₗ[K] A)) C
  change (∑ i,mu (Q i) (∑ j,C i j • E j))+
    (∑ j,mu (-∑ i,C i j • Q i) (E j))+0=0 at hb
  simp only [hC,add_zero] at hb
  have hy : (fun j => -∑ i,C i j • Q i)=y := by
    apply hE
    rw [BilinearImage.tupleMap_apply,BilinearImage.tupleMap_apply]
    exact add_left_cancel (hb.trans hrow.symm)
  exact ⟨C,fun i => (hC i).symm,fun j => (congrFun hy j).symm⟩

end Froberg
