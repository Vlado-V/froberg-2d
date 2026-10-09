module

public import Froberg.AttachedGenerators
public import Froberg.VectorQuotientOpen

@[expose] public section

/-! Actual attached quotient witnesses imply relative open polynomial families. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg.AttachedMultiplication
open Module MvPolynomial Quartic VectorExpansionOpen VectorMultiplicationCoordinates
variable {K L P : Type*} [Field K] [Field L] [Algebra K L]
  {h n s d c : ℕ}

lemma generator_expands_of_quotient (e : Fin c → Fin n →₀ ℕ)
    (v : Fin c → Fin h → K) (he : ∀ i,(e i).degree=s) (hn : 0 < n)
    (hi₀ : Function.Injective (AttachedMultiplication.multiplication (d := 0) e v))
    (hi : Function.Injective (AttachedMultiplication.multiplication (d := d) e v))
    (ell q : ℕ)
    (hb : ∀ U : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he),
      finrank K U=ell → q ≤ finrank K (BilinearImage.image (quotientMultiply (d := d) e v he) U)) :
    Expands (generator e v he) d (ell+c) (q+c*FormCount n d) := by
  have hsrc : finrank K (relationSpace (d := 0) e v he)=c := by
    change finrank K (LinearMap.range (homogeneousMultiplication (d := 0) e v he))=c
    rw [LinearMap.finrank_range_of_inj (homogeneousMultiplication_injective e v he hi₀)]
    simp [Module.finrank_pi_fintype,finrank_forms K n 0 hn]
  have htgt : finrank K (relationSpace (d := d) e v he)=c*FormCount n d := by
    rw [← image_relationSpace e v he,relationSpace_zero_eq_span]
    apply product_span_dimension
    change Function.Injective (BilinearImage.tupleMap (vectorMultiply (d := d)) (generator e v he))
    rw [tupleMap_generator]
    exact homogeneousMultiplication_injective e v he hi
  have hamb := (expansion_iff_ambient e v he ell q).mp hb
  intro S hES hS
  have hES' : relationSpace (d := 0) e v he ≤ S := by
    rwa [relationSpace_zero_eq_span]
  have hd : finrank K S=ell+finrank K (relationSpace (d := 0) e v he) := by rwa [hsrc]
  simpa only [htgt,VectorMultiplicationCoordinates.multiplication] using hamb S hES' hd

theorem principal_open_attached_witness [IsAlgClosed L] {A : Type*} [Fintype A]
    (e : Fin c → Fin n →₀ ℕ) (v : Fin c → Fin h → K)
    (he : ∀ i,(e i).degree=s) (hn : 0 < n)
    (g : (P → K) → Fin c → Rows K h n s)
    (hg : ∀ j,IsPolynomialFamily (fun p => g p j)) (p₀ : P → K)
    (hp₀ : g p₀=generator e v he)
    (hi₀ : Function.Injective (AttachedMultiplication.multiplication (d := 0) e v))
    (hi : Function.Injective (AttachedMultiplication.multiplication (d := d) e v))
    (hgeom₀ : Function.Injective (AttachedMultiplication.multiplication (d := 0) e
      (fun i j => algebraMap K L (v i j))))
    (hgeom : Function.Injective (AttachedMultiplication.multiplication (d := d) e
      (fun i j => algebraMap K L (v i j))))
    (ell bound : A → ℕ) (hell : ∀ i,0 < ell i+c)
    (hbound : ∀ i (U : Submodule L ((Fin h → Forms L n s) ⧸
      relationSpace (d := 0) e (fun i j => algebraMap K L (v i j)) he)),
      finrank L U=ell i → bound i ≤ finrank L (BilinearImage.image
        (quotientMultiply (d := d) e (fun i j => algebraMap K L (v i j)) he) U)) :
    ∃ D : MvPolynomial P K,eval p₀ D ≠ 0 ∧ ∀ p : P → K,eval p D ≠ 0 →
      LinearIndependent K (g p) ∧
      Function.Injective (BilinearImage.tupleMap (vectorMultiply (d := d)) (g p)) ∧
      ∀ i (U : Submodule K ((Rows K h n s) ⧸ Submodule.span K (Set.range (g p)))),
        finrank K U=ell i → bound i ≤ finrank K (BilinearImage.image
          (QuotientBilinearImage.quotientMap (vectorMultiply (d := d))
            (Submodule.span K (Set.range (g p)))) U) := by
  apply quotient_principal_open (L := L) g hg p₀
  · rw [hp₀]
    exact generator_independent e v he hi₀ hn
  · rw [hp₀]
    change Function.Injective (BilinearImage.tupleMap (vectorMultiply (d := d)) (generator e v he))
    rw [tupleMap_generator]
    exact homogeneousMultiplication_injective e v he hi
  · exact hell
  · intro i
    rw [hp₀]
    simp_rw [map_generator]
    exact generator_expands_of_quotient e _ he hn hgeom₀ hgeom (ell i) (bound i) (hbound i)

end Froberg.AttachedMultiplication
