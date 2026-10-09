module

public import Froberg.AttachedStrictOpen
public import Froberg.AttachedDimensionCounts
public import Froberg.StrictVectorModel

@[expose] public section

/-! A geometric attached witness yields a genuine open of strict vector models. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg.AttachedMultiplication
open Module MvPolynomial Quartic VectorExpansionOpen VectorMultiplicationCoordinates
variable {K L P I : Type*} [Field K] [Field L] [Algebra K L] [Fintype I]
  {h n s d c : ℕ}

theorem principal_open_strict_model_from_attached [IsAlgClosed L]
    (r : Fin c ≃ I) (hc : 0 < c) (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    (he : ∀ i,(e i).degree=s) (hn : 0 < n)
    (g : (P → K) → Fin c → Rows K h n s)
    (hg : ∀ j,IsPolynomialFamily (fun p => g p j)) (p₀ : P → K)
    (hp₀ : g p₀=generator e v he ∘ r)
    (hi₀ : Function.Injective (AttachedMultiplication.multiplication (d := 0) e v))
    (hi : Function.Injective (AttachedMultiplication.multiplication (d := d) e v))
    (hgeom₀ : Function.Injective (AttachedMultiplication.multiplication (d := 0) e
      (fun i j => algebraMap K L (v i j))))
    (hgeom : Function.Injective (AttachedMultiplication.multiplication (d := d) e
      (fun i j => algebraMap K L (v i j))))
    (G : ℝ)
    (hA : 0 < finrank L ((Fin h → Forms L n s) ⧸
      relationSpace (d := 0) e (fun i j => algebraMap K L (v i j)) he))
    (hGA : (finrank L ((Fin h → Forms L n s) ⧸
      relationSpace (d := 0) e (fun i j => algebraMap K L (v i j)) he) : ℝ) ≤ G)
    (hbound : ∀ U : Submodule L ((Fin h → Forms L n s) ⧸
      relationSpace (d := 0) e (fun i j => algebraMap K L (v i j)) he),
      ((finrank L ((Fin h → Forms L n (s+d)) ⧸ relationSpace (d := d) e
        (fun i j => algebraMap K L (v i j)) he) : ℝ)/finrank L ((Fin h → Forms L n s) ⧸
        relationSpace (d := 0) e (fun i j => algebraMap K L (v i j)) he))*finrank L U+
        G*(min (finrank L U) (finrank L ((Fin h → Forms L n s) ⧸
          relationSpace (d := 0) e (fun i j => algebraMap K L (v i j)) he)-finrank L U) : ℕ) ≤
        (finrank L (BilinearImage.image
          (quotientMultiply (d := d) e (fun i j => algebraMap K L (v i j)) he) U) : ℝ)) :
    ∃ D : MvPolynomial P K,eval p₀ D ≠ 0 ∧ ∀ p : P → K,eval p D ≠ 0 → StrictModel (g p) d G := by
  have hcard : Fintype.card I=c := by simpa only [Fintype.card_fin] using (Fintype.card_congr r).symm
  have hsrc : finrank L ((Fin h → Forms L n s) ⧸
      relationSpace (d := 0) e (fun i j => algebraMap K L (v i j)) he)=RowCount h n s-c := by
    simpa only [hcard] using attached_source_dimension_count e _ he hn hgeom₀
  have htgt : finrank L ((Fin h → Forms L n (s+d)) ⧸
      relationSpace (d := d) e (fun i j => algebraMap K L (v i j)) he)=
      RowCount h n (s+d)-c*FormCount n d := by
    simpa only [hcard] using attached_quotient_dimension_count e _ he hgeom
  obtain ⟨D,hD,hgood⟩ := principal_open_reindexed_strict_shadow (L := L) r hc e v he hn
    g hg p₀ hp₀ hi₀ hi hgeom₀ hgeom
    (((RowCount h n (s+d)-c*FormCount n d : ℕ) : ℝ) / ((RowCount h n s-c : ℕ) : ℝ)) G
    (by simpa only [hsrc,htgt] using hbound)
  refine ⟨D,hD,?_⟩
  intro p hp
  obtain ⟨hlin,hinj,hgrow⟩ := hgood p hp
  have hsK := source_quotient_dimension (g p) hlin
  have htK := target_quotient_dimension (g p) hinj
  refine ⟨hlin,hinj,?_,?_,?_⟩
  · change 0 < finrank K ((Rows K h n s) ⧸ Submodule.span K (Set.range (g p)))
    rwa [hsK,← hsrc]
  · change (finrank K ((Rows K h n s) ⧸ Submodule.span K (Set.range (g p))) : ℝ) ≤ G
    rwa [hsK,← hsrc]
  · intro U
    have hs' : finrank K (Source (g p))=RowCount h n s-c := hsK
    have ht' : finrank K (Target (g p) d)=RowCount h n (s+d)-c*FormCount n d := htK
    rw [hs',ht']
    convert hgrow U using 1
    rfl

end Froberg.AttachedMultiplication
