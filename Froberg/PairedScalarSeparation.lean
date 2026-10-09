module

public import Froberg.PairedSpace
public import Froberg.PolynomialTensorTransport
public import Froberg.DeletedBidegreeQuotient

@[expose] public section

/-! Paired-variable scalar spaces in the precise bidegree summands used by
the generic scalar separation theorem. -/
noncomputable section
namespace Froberg
open Module Finset MvPolynomial MonomialExpansion PairedMonomials
variable {K : Type} [Field K] [Infinite K]

/-- Renaming variables transports a weight grading along the variable map. -/
theorem rename_weightedHomogeneous {σ τ M : Type*} [AddCommMonoid M]
    (f : σ ↪ τ) (u : σ → M) (v : τ → M) (hweight : ∀ i, v (f i) = u i)
    {p : MvPolynomial σ K} {m : M} (hp : p.IsWeightedHomogeneous u m) :
    (rename f p).IsWeightedHomogeneous v m := by
  classical
  intro a ha
  have has : a ∈ (rename f p).support := mem_support_iff.mpr ha
  rw [support_rename_of_injective f.injective] at has
  obtain ⟨b,hb,rfl⟩ := mem_image.mp has
  have he : Finsupp.weight v (b.mapDomain f) = Finsupp.weight u b := by
    simp only [Finsupp.weight_apply]
    rw [Finsupp.sum_mapDomain_index (by intro i; exact zero_smul ℕ (v i))
      (by intro i x y; exact add_smul x y (v i))]
    simp only [hweight]
  rw [he]
  exact hp (mem_support_iff.mp hb)

def splitWeight {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℕ × ℕ :=
  if i ∈ S then (1,0) else (0,1)

theorem fst_weight_splitWeight {n : ℕ} (S : Finset (Fin n)) (a : Fin n →₀ ℕ) :
    (Finsupp.weight (splitWeight S) a).1 = partialDegree S a := by
  calc
    (Finsupp.weight (splitWeight S) a).1 = ∑ i, if i ∈ S then a i else 0 := by
      change (AddMonoidHom.fst ℕ ℕ) (Finsupp.weight (splitWeight S) a) = _
      rw [Finsupp.weight_eq_sum,map_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [splitWeight,hi]
    _ = partialDegree S a := by simp [partialDegree]

/-- A balanced split contains paired variables with the designated first half. -/
theorem exists_split_pair_embedding {n : ℕ} (S : Finset (Fin n))
    (hS : S.card ≤ Sᶜ.card) :
    ∃ e : (Fin S.card × Bool) ↪ Fin n,
      ∀ i, splitWeight S (e i) = pairedWeight i := by
  classical
  obtain ⟨l⟩ : Nonempty (Fin S.card ↪ S) :=
    Function.Embedding.nonempty_of_card_le (by simp)
  obtain ⟨r⟩ : Nonempty (Fin S.card ↪ (Sᶜ : Finset (Fin n))) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin, Fintype.card_coe] using hS)
  have hl (i) : (l i).val ∈ S := (l i).property
  have hr (i) : (r i).val ∉ S := mem_compl.mp (r i).property
  let f : Fin S.card × Bool → Fin n := fun i => if i.2 then (l i.1).val else (r i.1).val
  have hf : Function.Injective f := by
    rintro ⟨i,b⟩ ⟨j,c⟩ he
    cases b <;> cases c
    · have hij : i = j := r.injective (Subtype.ext he)
      subst j
      rfl
    · have h : (r i).val = (l j).val := he
      exact False.elim (hr i (h ▸ hl j))
    · have h : (l i).val = (r j).val := he
      exact False.elim (hr j (h ▸ hl i))
    · have hij : i = j := l.injective (Subtype.ext he)
      subst j
      rfl
  refine ⟨⟨f,hf⟩,?_⟩
  rintro ⟨i,b⟩
  cases b <;> simp [f,splitWeight,pairedWeight,hl,hr]

/-- A scalar space with exactly the manuscript's paired-variable dimension;
its symmetric products occupy a single deleted bidegree summand. -/
theorem paired_scalar_space_exists {n : ℕ} (S : Finset (Fin n))
    (hS : S.card ≤ Sᶜ.card) (t : ℕ) :
    ∃ C : Submodule K (Poly K n),
      C ≤ Forms K n t ∧ finrank K C = S.card.choose t ∧
      Function.Injective (subspaceSymmetricMultiplication C) ∧
      C*C ≤ deletedBidegreeSpace K S (2*t) (2*(t/2)) := by
  classical
  obtain ⟨e,he⟩ := exists_split_pair_embedding S hS
  obtain ⟨W,hWh,hWb,hWd,hWi⟩ := paired_space_exists (K := K) S.card t
  letI : Module.Finite K (homogeneousSubmodule (Fin S.card × Bool) K t) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  letI : Module.Finite K W := Submodule.finiteDimensional_of_le hWh
  let f := (MvPolynomial.rename e : MvPolynomial (Fin S.card × Bool) K →ₐ[K] Poly K n)
  let C := W.map f.toLinearMap
  have hfh : Function.Injective f := MvPolynomial.rename_injective e e.injective
  have hCh : C ≤ Forms K n t := by
    rintro _ ⟨a,ha,rfl⟩
    exact (hWh ha).rename_isHomogeneous
  have hCb : C ≤ weightedHomogeneousSubmodule K (splitWeight S) (t/2,t-t/2) := by
    rintro _ ⟨a,ha,rfl⟩
    exact rename_weightedHomogeneous e pairedWeight (splitWeight S) he (hWb ha)
  have hCd : finrank K C = S.card.choose t := by
    rw [← hWd]
    exact (LinearEquiv.ofBijective (f.toLinearMap.submoduleMap W)
      ⟨LinearMap.submoduleMap_injective hfh W, LinearMap.submoduleMap_surjective _ _⟩).finrank_eq.symm
  refine ⟨C,hCh,hCd,subspaceSymmetricMultiplication_map_injective f hfh W hWi,?_⟩
  apply Submodule.mul_le.mpr
  intro a ha b hb
  apply (mem_deletedBidegreeSpace_iff S (2*(t/2)) (a*b)).mpr
  constructor
  · change (a*b).IsHomogeneous (2*t)
    simpa only [two_mul] using (hCh ha).mul (hCh hb)
  · intro β hβ
    by_contra hc
    have h := (hCb ha).mul (hCb hb) hc
    have hh := congrArg Prod.fst h
    rw [fst_weight_splitWeight] at hh
    exact hβ (by simpa only [Prod.fst_add,two_mul] using hh)

end Froberg
