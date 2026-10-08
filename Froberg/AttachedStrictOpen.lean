import Froberg.AttachedReindexedOpen
import Froberg.VectorQuotientDimensions

/-! The real strict-shadow inequality persists on an actual common open. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg.AttachedMultiplication
open Module MvPolynomial Quartic VectorExpansionOpen VectorMultiplicationCoordinates
variable {K L P I : Type*} [Field K] [Field L] [Algebra K L] [Fintype I]
  {h n s d c : ℕ}

theorem principal_open_reindexed_strict_shadow [IsAlgClosed L]
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
    (R G : ℝ)
    (hbound : ∀ U : Submodule L ((Fin h → Forms L n s) ⧸
      relationSpace (d := 0) e (fun i j => algebraMap K L (v i j)) he),
      R*finrank L U+G*(min (finrank L U) (RowCount h n s-c-finrank L U) : ℕ) ≤
        (finrank L (BilinearImage.image
          (quotientMultiply (d := d) e (fun i j => algebraMap K L (v i j)) he) U) : ℝ)) :
    ∃ D : MvPolynomial P K,eval p₀ D ≠ 0 ∧ ∀ p : P → K,eval p D ≠ 0 →
      LinearIndependent K (g p) ∧
      Function.Injective (BilinearImage.tupleMap (vectorMultiply (d := d)) (g p)) ∧
      ∀ U : Submodule K ((Rows K h n s) ⧸ Submodule.span K (Set.range (g p))),
        R*finrank K U+G*(min (finrank K U) (RowCount h n s-c-finrank K U) : ℕ) ≤
          (finrank K (BilinearImage.image
            (QuotientBilinearImage.quotientMap (vectorMultiply (d := d))
              (Submodule.span K (Set.range (g p)))) U) : ℝ) := by
  let A := RowCount h n s-c
  let ell : Fin (A+1) → ℕ := fun i => i.val
  let bound : Fin (A+1) → ℕ := fun i => Nat.ceil (R*i.val+G*(min i.val (A-i.val) : ℕ))
  have hbound' (i : Fin (A+1)) (U : Submodule L ((Fin h → Forms L n s) ⧸
      relationSpace (d := 0) e (fun i j => algebraMap K L (v i j)) he))
      (hU : finrank L U=ell i) : bound i ≤ finrank L (BilinearImage.image
        (quotientMultiply (d := d) e (fun i j => algebraMap K L (v i j)) he) U) := by
    apply Nat.ceil_le.mpr
    have hh := hbound U
    simpa only [hU,ell,A] using hh
  obtain ⟨D,hD,hgood⟩ := principal_open_reindexed_attached (L := L) r e v he hn g hg p₀ hp₀
    hi₀ hi hgeom₀ hgeom ell bound (fun i => by dsimp [ell]; omega) hbound'
  refine ⟨D,hD,?_⟩
  intro p hp
  obtain ⟨hlin,hinj,hall⟩ := hgood p hp
  refine ⟨hlin,hinj,?_⟩
  intro U
  have hdim := source_quotient_dimension (g p) hlin
  have hle : finrank K U ≤ A := by
    simpa only [hdim,A] using Submodule.finrank_le U
  let i : Fin (A+1) := ⟨finrank K U,by omega⟩
  have hb := hall i U rfl
  have hbR : (bound i : ℝ) ≤ finrank K (BilinearImage.image
      (QuotientBilinearImage.quotientMap (vectorMultiply (d := d))
        (Submodule.span K (Set.range (g p)))) U) := by exact_mod_cast hb
  exact (Nat.le_ceil _).trans hbR

end Froberg.AttachedMultiplication
