import Froberg.PolynomialTriangular

/-! A common ideal suffices for triangular elimination. Individual target
rows can be constructed using different generator blocks of that same ideal. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] {h m D n : ℕ}

def triangularIdealSource (I : Submodule K (Poly K (h+m)))
    (weight : Fin (n+1) → ℕ) (i : Fin (n+1)) : Submodule K (Forms K (h+m) D) :=
  I.comap (Forms K (h+m) D).subtype ⊓
    ⨅ (j : Fin (n+1)) (_ : i<j),
      (((coreComponent h m (weight j)).comp (Forms K (h+m) D).subtype).ker)

theorem mem_triangularIdealSource (I : Submodule K (Poly K (h+m)))
    (weight : Fin (n+1) → ℕ) (i : Fin (n+1)) (p : Forms K (h+m) D) :
    p∈triangularIdealSource I weight i ↔ p.val∈I ∧
      ∀ j,i<j → coreComponent h m (weight j) p.val=0 := by
  simp only [triangularIdealSource,Submodule.mem_inf,Submodule.mem_comap,
    Submodule.subtype_apply,Submodule.mem_iInf,LinearMap.mem_ker,LinearMap.comp_apply]

/-- If all positive target components have bounded-degree lifts in one
actual ideal, every quotient class has a representative on the bottom row. -/
theorem polynomial_ideal_elimination (I : Submodule K (Poly K (h+m)))
    (weight : Fin (n+1) → ℕ)
    (hlift : ∀ i,i≠0 → ∀ v : coreCoefficientSpace K h m D (weight i),
      ∃ q : Forms K (h+m) D,q.val∈I ∧
        coreComponent h m (weight i) q.val=v.val ∧
        ∀ j,i<j → coreComponent h m (weight j) q.val=0)
    (p : Forms K (h+m) D) :
    ∃ q : Forms K (h+m) D,p.val-q.val∈I ∧
      ∀ j : Fin n,coreComponent h m (weight j.succ) q.val=0 := by
  let S := triangularIdealSource (D := D) I weight
  let row (i : Fin (n+1)) : S i →ₗ[K] Forms K (h+m) D := (S i).subtype
  apply polynomial_triangular_quotient_representative (S := fun i => ↥(S i)) weight row _ _ I _ p
  · intro i j hij s
    exact ((mem_triangularIdealSource I weight i s.val).mp s.property).2 j hij
  · intro i hi v
    obtain ⟨q,hq,hqv,hupper⟩ := hlift i hi v
    exact ⟨⟨q,(mem_triangularIdealSource I weight i q).mpr ⟨hq,hupper⟩⟩,hqv⟩
  · intro i s
    exact ((mem_triangularIdealSource I weight i s.val).mp s.property).1

end Froberg
