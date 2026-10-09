module

public import Froberg.QuadraticBlockLocalization
public import Froberg.GenericProductSupport
public import Froberg.SymmetricProducts

@[expose] public section

/-! Common specialization of all quadratic block minors.  Each fiber is
certified on at most four blocks; its block degree separates it from the others. -/
noncomputable section
namespace Froberg.QuadraticBlocks
open Finset PairedMonomials ProductFibers ProductMinors
variable {X : Type*} [Fintype X] [DecidableEq X]

def productKey : Sym2 (Label X) → Finset X × Finset X :=
  Sym2.lift ⟨fun a b => (support a ∩ support b, support a ∪ support b),
    fun a b => by simp only [inter_comm, union_comm]⟩

@[simp] theorem productKey_mk (a b : Label X) :
    productKey s(a,b) = (support a ∩ support b, support a ∪ support b) := rfl

abbrev Columns (k : Finset X × Finset X) := {p : Sym2 (Label X) // productKey p = k}

def left {k : Finset X × Finset X} (p : Columns k) : Label X := p.val.out.1

def right {k : Finset X × Finset X} (p : Columns k) : Label X := p.val.out.2

@[simp] theorem pair_left_right {k : Finset X × Finset X} (p : Columns k) :
    s(left p,right p) = p.val := Quot.out_eq p.val

theorem key_left_right {k : Finset X × Finset X} (p : Columns k) :
    (support (left p) ∩ support (right p), support (left p) ∪ support (right p)) = k := by
  rw [← productKey_mk, pair_left_right]
  exact p.property

structure FiberCertificate (K : Type*) [CommRing K] (k : Finset X × Finset X) where
  rows : Columns k → (X × Bool) →₀ ℕ
  nonzero : (productMinor (K := K) terms left right rows).det ≠ 0
  permitted : ∀ p, ∃ a ∈ terms (left p), ∃ b ∈ terms (right p), rows p = a+b

variable {K : Type*} [CommRing K] [Nontrivial K]

theorem fiberCertificate_nonempty (k : Finset X × Finset X) :
    Nonempty (FiberCertificate K k) := by
  classical
  by_cases h : Nonempty (Columns k)
  · obtain ⟨p⟩ := h
    have hi := congrArg Prod.fst (key_left_right p)
    have hu := congrArg Prod.snd (key_left_right p)
    have hIU : k.1 ⊆ k.2 := by
      rw [← hi, ← hu]
      exact inter_subset_left.trans subset_union_left
    have hU : k.2.card ≤ 4 := by
      rw [← hu]
      have hc := card_union_le (support (left p)) (support (right p))
      simpa only [card_support] using hc
    obtain ⟨choice, hc, hinj⟩ := exists_global_fiber_choices k.1 k.2 hIU hU
    have hleft (q : Columns k) : support (left q) ⊆ k.2 := by
      rw [← congrArg Prod.snd (key_left_right q)]
      exact subset_union_left
    have hright (q : Columns k) : support (right q) ⊆ k.2 := by
      rw [← congrArg Prod.snd (key_left_right q)]
      exact subset_union_right
    refine ⟨⟨fun q => choice (left q) + choice (right q), ?_, ?_⟩⟩
    · apply productMinor_ne_zero terms left right choice
        (fun q => hc _ (hleft q)) (fun q => hc _ (hright q))
      intro q r he
      apply Subtype.ext
      rw [← pair_left_right q, ← pair_left_right r]
      exact hinj _ _ _ _ (congrArg Prod.fst (key_left_right q))
        (congrArg Prod.snd (key_left_right q)) (congrArg Prod.fst (key_left_right r))
        (congrArg Prod.snd (key_left_right r)) he
    · intro q
      exact ⟨_, hc _ (hleft q), _, hc _ (hright q), rfl⟩
  · letI : IsEmpty (Columns k) := not_nonempty_iff.mp h
    refine ⟨⟨isEmptyElim, ?_, isEmptyElim⟩⟩
    simp

/-- Different block-degree fibers have disjoint possible product exponents. -/
theorem key_eq_of_permitted_products {k l : Finset X × Finset X}
    (p : Columns k) (q : Columns l) {a b c d : (X × Bool) →₀ ℕ}
    (ha : a ∈ terms (left p)) (hb : b ∈ terms (right p))
    (hc : c ∈ terms (left q)) (hd : d ∈ terms (right q)) (he : a+b=c+d) : k = l := by
  obtain ⟨A, hA, rfl⟩ := mem_image.mp ha
  obtain ⟨B, hB, rfl⟩ := mem_image.mp hb
  obtain ⟨C, hC, rfl⟩ := mem_image.mp hc
  obtain ⟨D, hD, rfl⟩ := mem_image.mp hd
  have h := (product_indexDegree_eq_iff _ _ _ _ A B C D).mp (congrArg indexDegree he)
  exact (key_left_right p).symm.trans ((Prod.ext h.1 h.2).trans (key_left_right q))

theorem FiberCertificate.cross {k l : Finset X × Finset X} (cert : FiberCertificate K k)
    (hkl : k ≠ l) (p : Columns k) (q : Columns l) :
    ((genericForm (K := K) terms (left q)) * genericForm terms (right q)).coeff
      (cert.rows p) = 0 := by
  apply generic_product_coeff_zero
  intro c hc d hd he
  obtain ⟨a, ha, b, hb, hrow⟩ := cert.permitted p
  exact hkl (key_eq_of_permitted_products p q ha hb hc hd (hrow.symm.trans he))

def specializedForm (values : Label X × ((X × Bool) →₀ ℕ) → K) (l : Label X) :
    MvPolynomial (X × Bool) K :=
  MvPolynomial.map (MvPolynomial.eval values) (genericForm terms l)

theorem specializedForm_homogeneous (values : Label X × ((X × Bool) →₀ ℕ) → K)
    (l : Label X) : specializedForm values l ∈
      MvPolynomial.homogeneousSubmodule (X × Bool) K 2 := by
  classical
  unfold specializedForm genericForm
  simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.eval_X,
    MvPolynomial.map_monomial, map_one, MvPolynomial.C_mul_monomial, mul_one]
  apply Submodule.sum_mem
  intro m hm
  obtain ⟨A, hA, rfl⟩ := mem_image.mp hm
  exact MvPolynomial.isHomogeneous_monomial _ ((degree_pairedExponent _ _).trans (card_support l))

/-- Two generic bilinear quadrics per unordered pair of blocks have independent
unordered products over every infinite field. -/
theorem exists_independent_pairProducts [IsDomain K] [Infinite K] :
    ∃ values : Label X × ((X × Bool) →₀ ℕ) → K,
      LinearIndependent K (Froberg.pairProducts (specializedForm values)) := by
  classical
  let cert (k : Finset X × Finset X) : FiberCertificate K k :=
    Classical.choice (fiberCertificate_nonempty k)
  obtain ⟨values,hv⟩ := exists_common_specialization
    (fun k => (productMinor (K := K) terms left right (cert k).rows).det)
    (fun k => (cert k).nonzero)
  refine ⟨values, ?_⟩
  have hs : LinearIndependent K (fun z : Σ k : Finset X × Finset X, Columns k =>
      specializedForm values (left z.2) * specializedForm values (right z.2)) := by
    apply linearIndependent_sigma_of_fiber_minors
      (fun k p => specializedForm values (left p) * specializedForm values (right p))
      (fun k => (cert k).rows)
    · intro k
      have hm : (fun i j : Columns k =>
          (specializedForm values (left j) * specializedForm values (right j)).coeff ((cert k).rows i)) =
          (MvPolynomial.eval values).mapMatrix (productMinor terms left right (cert k).rows) := by
        ext i j
        unfold specializedForm
        rw [← map_mul, MvPolynomial.coeff_map]
        rfl
      rw [hm, ← RingHom.map_det]
      exact hv k
    · intro k l hkl p q
      unfold specializedForm
      rw [← map_mul, MvPolynomial.coeff_map, (cert k).cross hkl p q, map_zero]
  let f (p : Sym2 (Label X)) : Σ k : Finset X × Finset X, Columns k :=
    ⟨productKey p, ⟨p,rfl⟩⟩
  have hf : Function.Injective f := by
    intro p q h
    exact congrArg (fun z : Σ k : Finset X × Finset X, Columns k => z.2.val) h
  have h := hs.comp f hf
  convert h using 1
  funext p
  change Froberg.pairProducts (specializedForm values) p =
    specializedForm values p.out.1 * specializedForm values p.out.2
  exact (congrArg (Froberg.pairProducts (specializedForm values)) (Quot.out_eq p)).symm

end Froberg.QuadraticBlocks
