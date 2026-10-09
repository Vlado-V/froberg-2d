module

public import Froberg.FormalHomology
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Data.Sym.Card

@[expose] public section

/-! Independent unordered products imply injective multiplication on the actual symmetric square. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} [Field K]
variable {A : Type*} [CommRing A] [Algebra K A]
variable {ι : Type*}

/-- The actual product indexed by an unordered pair of generators. -/
def pairProducts (q : ι → A) : Sym2 ι → A :=
  Sym2.lift ⟨fun i j => q i * q j, fun i j => mul_comm _ _⟩

@[simp] theorem pairProducts_mk (q : ι → A) (i j : ι) :
    pairProducts q s(i,j) = q i * q j := rfl

/-- The corresponding formal product in the symmetric square. -/
def pairFormal (q : ι → A) : Sym2 ι → SymmetricSquare K A :=
  Sym2.lift ⟨fun i j => symProd (q i) (q j), fun i j => symProd_comm _ _⟩

@[simp] theorem pairFormal_mk (q : ι → A) (i j : ι) :
    pairFormal (K := K) q s(i,j) = symProd (q i) (q j) := rfl

/-- Multiplication descended through the defining symmetric-square quotient. -/
def symmetricMultiplication : SymmetricSquare K A →ₗ[K] A :=
  symmetricBilinearLift (LinearMap.mul K A) (fun a b => mul_comm a b)

@[simp] theorem symmetricMultiplication_symProd (a b : A) :
    symmetricMultiplication (K := K) (symProd a b) = a*b :=
  symmetricBilinearLift_symProd _ _ _ _

/-- Actual symmetric multiplication on a specified subspace of an algebra. -/
def subspaceSymmetricMultiplication (W : Submodule K A) : SymmetricSquare K W →ₗ[K] A :=
  (symmetricMultiplication (K := K)).comp (SymmetricFunctor.map W.subtype)

private theorem symProd_add_left' (a b c : A) :
    symProd (K := K) (a+b) c = symProd a c + symProd b c := (symProdLeft c).map_add a b
private theorem symProd_smul_left' (k : K) (a b : A) :
    symProd (k • a) b = k • symProd (K := K) a b := (symProdLeft b).map_smul k a
private theorem symProd_add_right' (a b c : A) :
    symProd (K := K) a (b+c) = symProd a b + symProd a c := by
  simp only [symProd_comm a, symProd_add_left']
private theorem symProd_smul_right' (k : K) (a b : A) :
    symProd a (k • b) = k • symProd (K := K) a b := by
  rw [symProd_comm, symProd_smul_left', symProd_comm b a]

/-- Products of spanning generators span every formal product in their span. -/
theorem symProd_mem_span_pairFormal (q : ι → A) {a b : A}
    (ha : a ∈ Submodule.span K (Set.range q)) (hb : b ∈ Submodule.span K (Set.range q)) :
    symProd a b ∈ Submodule.span K (Set.range (pairFormal (K := K) q)) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j,rfl⟩ := hy
      exact Submodule.subset_span ⟨s(i,j),rfl⟩
    | zero => simp
    | add b c _ _ hb hc =>
      rw [symProd_add_right']
      exact Submodule.add_mem _ hb hc
    | smul k b _ hb =>
      rw [symProd_smul_right']
      exact Submodule.smul_mem _ _ hb
  | zero => simp
  | add a c _ _ ha hc =>
    rw [symProd_add_left']
    exact Submodule.add_mem _ ha hc
  | smul k a _ ha =>
    rw [symProd_smul_left']
    exact Submodule.smul_mem _ _ ha

theorem formalSquare_span_le_pairFormal (q : ι → A) :
    formalSquare (Submodule.span K (Set.range q)) ≤
      Submodule.span K (Set.range (pairFormal (K := K) q)) := by
  rintro x ⟨y,rfl⟩
  induction y using symmetricSquare_induction with
  | hprod a b =>
    rw [symmetricMap_symProd]
    exact symProd_mem_span_pairFormal q a.2 b.2
  | hzero => simp
  | hadd a b ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  | hsmul k a ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ ha

@[simp] theorem symmetricMultiplication_pairFormal (q : ι → A) (p : Sym2 ι) :
    symmetricMultiplication (pairFormal (K := K) q p) = pairProducts q p := by
  induction p using Sym2.inductionOn with | _ i j => simp

/-- Independent actual products eliminate every formal symmetric relation on the span. -/
theorem symmetricMultiplication_injective_of_pairProducts (q : ι → A)
    (hq : LinearIndependent K (pairProducts q)) :
    Function.Injective (subspaceSymmetricMultiplication (Submodule.span K (Set.range q))) := by
  have hzero : ∀ x ∈ formalSquare (Submodule.span K (Set.range q)),
      symmetricMultiplication (K := K) x = 0 → x = 0 := by
    intro x hx hmul
    have hx' := formalSquare_span_le_pairFormal q hx
    rw [← Finsupp.range_linearCombination] at hx'
    obtain ⟨c,hc⟩ := hx'
    have he : symmetricMultiplication (K := K) (Finsupp.linearCombination K (pairFormal (K := K) q) c) =
        Finsupp.linearCombination K (pairProducts q) c := by
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
        symmetricMultiplication_pairFormal]
    have hz : Finsupp.linearCombination K (pairProducts q) c = 0 := by
      rw [← he,hc,hmul]
    have hc0 : c = 0 := hq (hz.trans (map_zero _).symm)
    rw [← hc,hc0,map_zero]
  intro x y hxy
  have hz : SymmetricFunctor.map (Submodule.span K (Set.range q)).subtype (x - y) = 0 := by
    apply hzero _ ⟨x-y,rfl⟩
    change subspaceSymmetricMultiplication (Submodule.span K (Set.range q)) (x-y) = 0
    rw [map_sub,hxy,sub_self]
  apply SymmetricFunctor.map_injective (Submodule.span K (Set.range q)).subtype
    (Submodule.subtype_injective _)
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

/-- Independent unordered products also imply independence of the generators. -/
theorem linearIndependent_of_pairProducts (q : ι → A)
    (hq : LinearIndependent K (pairProducts q)) : LinearIndependent K q := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    exact linearIndependent_empty_type
  | inr h =>
    obtain ⟨i₀⟩ := h
    have hi : Function.Injective (fun i => s(i₀,i)) := by
      intro i j hij
      rcases (Sym2.mk_eq_mk_iff (p := (i₀,i)) (q := (i₀,j))).mp hij with he | he
      · exact congrArg Prod.snd he
      · exact (congrArg Prod.snd he).trans (congrArg Prod.fst he)
    have h := hq.comp (fun i => s(i₀,i)) hi
    exact LinearIndependent.of_comp ((LinearMap.mul K A) (q i₀)) h

end Froberg
