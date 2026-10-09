module

public import Froberg.BiformPreparedRows
public import Froberg.TriangularSurjectivity

@[expose] public section

/-! Triangular elimination inside the actual homogeneous polynomial space.
The conclusion is subtraction of an actual relation, with every positive
selected X-degree component removed. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] {h m D n : ℕ}

def coreFormProjection (i : ℕ) :
    Forms K (h+m) D →ₗ[K] coreCoefficientSpace K h m D i :=
  ((coreComponent h m i).comp (Forms K (h+m) D).subtype).codRestrict
    (coreCoefficientSpace K h m D i) (fun p => ⟨p.val,p.property,rfl⟩)

@[simp] theorem coreFormProjection_val (i : ℕ) (p : Forms K (h+m) D) :
    (coreFormProjection i p).val=coreComponent h m i p.val := rfl

def homogeneousRowSum {S : Fin (n+1) → Type*}
    [∀ i,AddCommGroup (S i)] [∀ i,Module K (S i)]
    (row : (i : Fin (n+1)) → S i →ₗ[K] Forms K (h+m) D) :
    ((i : Fin (n+1)) → S i) →ₗ[K] Forms K (h+m) D :=
  ∑ i,(row i).comp (LinearMap.proj i)

@[simp] theorem homogeneousRowSum_apply {S : Fin (n+1) → Type*}
    [∀ i,AddCommGroup (S i)] [∀ i,Module K (S i)]
    (row : (i : Fin (n+1)) → S i →ₗ[K] Forms K (h+m) D)
    (s : (i : Fin (n+1)) → S i) : homogeneousRowSum row s=∑ i,row i (s i) := by
  simp only [homogeneousRowSum,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]

/-- Literal homogeneous relation rows with surjective leading components
eliminate every selected component above the bottom one. -/
theorem polynomial_triangular_elimination {S : Fin (n+1) → Type*}
    [∀ i,AddCommGroup (S i)] [∀ i,Module K (S i)]
    (weight : Fin (n+1) → ℕ)
    (row : (i : Fin (n+1)) → S i →ₗ[K] Forms K (h+m) D)
    (hupper : ∀ i j,i<j → ∀ s,coreComponent h m (weight j) (row i s).val=0)
    (htop : ∀ i,i≠0 → ∀ v : coreCoefficientSpace K h m D (weight i),
      ∃ s,coreComponent h m (weight i) (row i s).val=v.val)
    (p : Forms K (h+m) D) :
    ∃ s : (i : Fin (n+1)) → S i, ∀ j : Fin n,
      coreComponent h m (weight j.succ) (homogeneousRowSum row s).val=
        coreComponent h m (weight j.succ) p.val := by
  let C (i : Fin (n+1)) : S i →ₗ[K] ((j : Fin (n+1)) → coreCoefficientSpace K h m D (weight j)) :=
    LinearMap.pi (fun j => (coreFormProjection (weight j)).comp (row i))
  have hu : ∀ i j,i<j → ∀ s,C i s j=0 := by
    intro i j hij s
    apply Subtype.ext
    exact hupper i j hij s
  have hs : ∀ i,i≠0 → Function.Surjective (fun s => C i s i) := by
    intro i hi v
    obtain ⟨s,hsv⟩ := htop i hi v
    exact ⟨s,Subtype.ext hsv⟩
  obtain ⟨s,hsp⟩ := triangular_surjective_mod_bottom C hu hs
    (fun j : Fin n => coreFormProjection (weight j.succ) p)
  refine ⟨s,fun j => ?_⟩
  have he := congrArg Subtype.val (congrFun hsp j)
  simpa only [triangularRowSum,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    Finset.sum_apply,C,LinearMap.pi_apply,Submodule.coe_sum,coreFormProjection_val,
    homogeneousRowSum_apply,map_sum] using he

/-- If each row consists of genuine ideal relations, subtraction preserves
the quotient class while killing all selected positive components. -/
theorem polynomial_triangular_quotient_representative {S : Fin (n+1) → Type*}
    [∀ i,AddCommGroup (S i)] [∀ i,Module K (S i)]
    (weight : Fin (n+1) → ℕ)
    (row : (i : Fin (n+1)) → S i →ₗ[K] Forms K (h+m) D)
    (hupper : ∀ i j,i<j → ∀ s,coreComponent h m (weight j) (row i s).val=0)
    (htop : ∀ i,i≠0 → ∀ v : coreCoefficientSpace K h m D (weight i),
      ∃ s,coreComponent h m (weight i) (row i s).val=v.val)
    (I : Submodule K (Poly K (h+m))) (hI : ∀ i s,(row i s).val∈I)
    (p : Forms K (h+m) D) :
    ∃ q : Forms K (h+m) D, p.val-q.val∈I ∧
      ∀ j : Fin n,coreComponent h m (weight j.succ) q.val=0 := by
  obtain ⟨s,hs⟩ := polynomial_triangular_elimination weight row hupper htop p
  refine ⟨p-homogeneousRowSum row s,?_,?_⟩
  · have hsum : (homogeneousRowSum row s).val∈I := by
      rw [homogeneousRowSum_apply,Submodule.coe_sum]
      exact Submodule.sum_mem _ (fun i _ => hI i (s i))
    simpa only [Submodule.coe_sub,sub_sub_cancel] using hsum
  · intro j
    simp only [Submodule.coe_sub,map_sub,hs j,sub_self]

end Froberg
