import Froberg.PairedMatching
import Froberg.GenericProductSupport

/-! Assembly of the actual nonzero minors and their common coefficient specialization. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Froberg.PairedMonomials
open Finset ProductFibers ProductMinors
variable {X : Type*} [Fintype X] [DecidableEq X] {s : ℕ}

def formTerms (s : ℕ) (S : SizedSubset X s) : Finset ((X × Bool) →₀ ℕ) :=
  allowedExponents (s/2) S.1

theorem formTerms_nonempty (S : SizedSubset X s) : (formTerms s S).Nonempty := by
  obtain ⟨A,hAS,hA⟩ := Finset.exists_subset_card_eq (s := S.1) (n := s/2)
    (by rw [S.2]; omega)
  exact ⟨pairedExponent S.1 A, mem_allowedExponents hAS hA⟩

def defaultTerm (S : SizedSubset X s) : (X × Bool) →₀ ℕ :=
  (formTerms_nonempty S).choose

theorem defaultTerm_mem (S : SizedSubset X s) : defaultTerm S ∈ formTerms s S :=
  (formTerms_nonempty S).choose_spec

namespace ProductFiber
variable {K : Type*} [CommRing K] [Nontrivial K]

/-- A genuine coefficient minor, with the selected rows also realized as products of allowed terms. -/
structure MinorCertificate (K : Type*) [CommRing K] (F : ProductFiber X s) where
  rows : F.Columns → (X × Bool) →₀ ℕ
  nonzero : (productMinor (K := K) (formTerms s)
    (fun p => F.label (p,false)) (fun p => F.label (p,true)) rows).det ≠ 0
  permitted : ∀ p, ∃ e ∈ formTerms s (F.label (p,false)),
    ∃ f ∈ formTerms s (F.label (p,true)), rows p = e+f

theorem columns_subsingleton (F : ProductFiber X s) (ht : F.halfSize = 0) :
    Subsingleton F.Columns := by
  constructor
  intro p q
  induction p using Quotient.inductionOn with | _ P =>
    induction q using Quotient.inductionOn with | _ Q =>
      have hP : P.1 = ∅ := Finset.card_eq_zero.mp (P.2.trans ht)
      have hQ : Q.1 = ∅ := Finset.card_eq_zero.mp (Q.2.trans ht)
      exact congrArg (fun P => (⟦P⟧ : F.Columns)) (Subtype.ext (hP.trans hQ.symm))

/-- Every actual product fiber has a nonzero coefficient-polynomial minor. -/
theorem minorCertificate_nonempty (F : ProductFiber X s) : Nonempty (MinorCertificate K F) := by
  classical
  by_cases ht : F.halfSize = 0
  · letI := F.columns_subsingleton ht
    refine ⟨⟨fun p => defaultTerm (F.label (p,false)) + defaultTerm (F.label (p,true)), ?_, ?_⟩⟩
    · exact productMinor_ne_zero (formTerms s)
        (fun p => F.label (p,false)) (fun p => F.label (p,true)) defaultTerm
        (fun p => defaultTerm_mem _) (fun p => defaultTerm_mem _)
        (fun _ _ _ => Subsingleton.elim _ _)
    · intro p
      exact ⟨_,defaultTerm_mem _,_,defaultTerm_mem _,rfl⟩
  · obtain ⟨T⟩ := F.targets_nonempty
    refine ⟨⟨fun p => targetExponent F.doubled T.xy F.single (T.subset p),
      F.non_diagonal_minor T (Nat.pos_of_ne_zero ht), ?_⟩⟩
    intro p
    exact ⟨choices T (p,false),choices_mem T _,choices T (p,true),choices_mem T _,
      (choices_product T p).symm⟩

/-- Doubled indices and the total index support determine a fiber. -/
theorem eq_of_keys (F G : ProductFiber X s) (hi : F.doubled = G.doubled)
    (hu : F.doubled ∪ F.single = G.doubled ∪ G.single) : F = G := by
  have hs : F.single = G.single := by
    ext x
    have h := Finset.ext_iff.mp hu x
    simp only [Finset.mem_union] at h
    by_cases hx : x ∈ F.doubled
    · have hx' : x ∈ G.doubled := hi ▸ hx
      have hF : x ∉ F.single := fun hs => Finset.disjoint_left.mp F.disjoint hx hs
      have hG : x ∉ G.single := fun hs => Finset.disjoint_left.mp G.disjoint hx' hs
      simp [hF,hG]
    · have hx' : x ∉ G.doubled := hi ▸ hx
      simpa only [hx,hx',false_or] using h
  exact Subtype.ext (Prod.ext hi hs)

/-- Products of permitted monomials in distinct fibers have distinct exponents. -/
theorem eq_of_permitted_products (F G : ProductFiber X s) (p : F.Columns) (q : G.Columns)
    {e f g h : (X × Bool) →₀ ℕ}
    (he : e ∈ formTerms s (F.label (p,false))) (hf : f ∈ formTerms s (F.label (p,true)))
    (hg : g ∈ formTerms s (G.label (q,false))) (hh : h ∈ formTerms s (G.label (q,true)))
    (heq : e+f = g+h) : F = G := by
  obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨B,_,rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨C,_,rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp hh
  have hi := congrArg indexDegree heq
  have hk := (product_indexDegree_eq_iff
    (F.label (p,false)).1 (F.label (p,true)).1
    (G.label (q,false)).1 (G.label (q,true)).1 A B C D).mp hi
  rw [F.label_inter p,G.label_inter q,F.label_union p,G.label_union q] at hk
  exact eq_of_keys F G hk.1 hk.2

/-- A selected minor row has zero coefficient in every other fiber. -/
theorem MinorCertificate.cross {F G : ProductFiber X s} (M : MinorCertificate K F)
    (hFG : F ≠ G) (p : F.Columns) (q : G.Columns) :
    ((genericForm (K := K) (formTerms s) (G.label (q,false))) *
      genericForm (formTerms s) (G.label (q,true))).coeff (M.rows p) = 0 := by
  apply generic_product_coeff_zero
  intro g hg h hh heq
  obtain ⟨e,he,f,hf,hrow⟩ := M.permitted p
  exact hFG (eq_of_permitted_products F G p q he hf hg hh (hrow.symm.trans heq))

end ProductFiber
/-- Actual specialization of the coefficient-polynomial family. -/
def specializedForm {K : Type*} [CommRing K]
    (values : SizedSubset X s × ((X × Bool) →₀ ℕ) → K) (S : SizedSubset X s) :
    MvPolynomial (X × Bool) K :=
  MvPolynomial.map (MvPolynomial.eval values) (genericForm (formTerms s) S)

/-- One common coefficient assignment makes all product fibers independent,
and index-degree separation makes their union independent. -/
theorem exists_independent_fiber_products {K : Type*} [CommRing K] [IsDomain K] [Infinite K] :
    ∃ values : SizedSubset X s × ((X × Bool) →₀ ℕ) → K,
      LinearIndependent K (fun z : Σ F : ProductFiber X s, F.Columns =>
        specializedForm values (z.1.label (z.2,false)) *
        specializedForm values (z.1.label (z.2,true))) := by
  classical
  let cert (F : ProductFiber X s) : ProductFiber.MinorCertificate K F :=
    Classical.choice (F.minorCertificate_nonempty (K := K))
  obtain ⟨values,hv⟩ := exists_common_specialization (δ := ProductFiber X s)
    (fun F => (productMinor (K := K) (formTerms s)
      (fun p => F.label (p,false)) (fun p => F.label (p,true)) (cert F).rows).det)
    (fun F => (cert F).nonzero)
  refine ⟨values, ?_⟩
  apply linearIndependent_sigma_of_fiber_minors (δ := ProductFiber X s)
    (I := fun F => F.Columns)
    (fun F p => specializedForm values (F.label (p,false)) *
      specializedForm values (F.label (p,true))) (fun F => (cert F).rows)
  · intro F
    have hm : (fun i j : F.Columns =>
        (specializedForm values (F.label (j,false)) *
          specializedForm values (F.label (j,true))).coeff ((cert F).rows i) :
          Matrix F.Columns F.Columns K) =
        (MvPolynomial.eval values).mapMatrix (productMinor (formTerms s)
          (fun p => F.label (p,false)) (fun p => F.label (p,true)) (cert F).rows) := by
      ext i j
      unfold specializedForm
      rw [← map_mul,MvPolynomial.coeff_map]
      rfl
    rw [hm,← RingHom.map_det]
    exact hv F
  · intro F G hFG p q
    unfold specializedForm
    rw [← map_mul,MvPolynomial.coeff_map,(cert F).cross hFG p q,map_zero]

end Froberg.PairedMonomials
