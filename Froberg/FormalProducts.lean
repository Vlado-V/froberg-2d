import Froberg.SymmetricFunctor
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

/-! Formal symmetric products and the kernel of passage to a quotient. -/
noncomputable section
open TensorProduct
namespace Froberg

universe u v w
variable {K : Type} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {Z : Type w} [AddCommGroup Z] [Module K Z]

abbrev SymmetricSquare (K : Type) [CommSemiring K]
    (V : Type v) [AddCommMonoid V] [Module K V] := Sym[K] (Fin 2) V

/-- A formal symmetric product of two vectors. -/
def symProd (a b : V) : SymmetricSquare K V := SymmetricPower.tprod K ![a, b]

/-- Commutativity comes from the defining permutation relation. -/
theorem symProd_comm (a b : V) : symProd (K := K) a b = symProd b a := by
  have hv : (fun i => (![b, a] : Fin 2 → V) ((Equiv.swap 0 1) i)) = ![a, b] := by
    funext i
    fin_cases i <;> simp
  have h := SymmetricPower.tprod_equiv (R := K) (Equiv.swap (0 : Fin 2) 1) ![b, a]
  rw [hv] at h
  exact h

/-- Formal multiplication is linear in its first factor. -/
def symProdLeft (b : V) : V →ₗ[K] SymmetricSquare K V where
  toFun a := symProd a b
  map_add' a a' := (SymmetricPower.tprod K).cons_add ![b] a a'
  map_smul' c a := (SymmetricPower.tprod K).cons_smul ![b] c a

@[simp] theorem symProd_zero_left (b : V) : symProd (K := K) 0 b = 0 :=
  (symProdLeft (K := K) b).map_zero

@[simp] theorem symProd_zero_right (a : V) : symProd (K := K) a 0 = 0 := by
  rw [symProd_comm, symProd_zero_left]

theorem symProd_sub_left (a a' b : V) :
    symProd (K := K) (a - a') b = symProd a b - symProd a' b :=
  (symProdLeft (K := K) b).map_sub a a'

theorem symProd_sub_right (a b b' : V) :
    symProd (K := K) a (b - b') = symProd a b - symProd a b' := by
  rw [symProd_comm, symProd_sub_left, symProd_comm b a, symProd_comm b' a]

@[simp] theorem symmetricMap_symProd (f : V →ₗ[K] Z) (a b : V) :
    SymmetricFunctor.map f (symProd a b) = symProd (f a) (f b) := by
  rw [symProd, SymmetricFunctor.map_tprod, symProd]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Every symmetric tensor of order two is spanned by formal products. -/
@[elab_as_elim] theorem symmetricSquare_induction
    (x : SymmetricSquare K V) {p : SymmetricSquare K V → Prop}
    (hprod : ∀ a b, p (symProd a b)) (hzero : p 0)
    (hadd : ∀ a b, p a → p b → p (a + b))
    (hsmul : ∀ (c : K) a, p a → p (c • a)) : p x := by
  have hx : x ∈ Submodule.span K (Set.range (SymmetricPower.tprod K (ι := Fin 2) (M := V))) := by
    rw [SymmetricPower.span_tprod_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [hv]
    exact hprod (v 0) (v 1)
  | zero => exact hzero
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c a ha

/-- `L ⊙ V`, formed in the actual symmetric square, not in a polynomial image. -/
def formalMixed (L : Submodule K V) : Submodule K (SymmetricSquare K V) :=
  Submodule.span K {x | ∃ a b, a ∈ L ∧ x = symProd a b}

theorem symProd_mem_formalMixed (L : Submodule K V) {a : V} (ha : a ∈ L) (b : V) :
    symProd a b ∈ formalMixed L :=
  Submodule.subset_span ⟨a, b, ha, rfl⟩

theorem symProd_mem_formalMixed_right (L : Submodule K V) (a : V) {b : V} (hb : b ∈ L) :
    symProd a b ∈ formalMixed L := by
  rw [symProd_comm]
  exact symProd_mem_formalMixed L hb a

/-- Mixed products die when their first factor is quotiented out. -/
theorem formalMixed_le_ker (L : Submodule K V) :
    formalMixed L ≤ LinearMap.ker (SymmetricFunctor.map (ι := Fin 2) L.mkQ) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, b, ha, rfl⟩
  change SymmetricFunctor.map L.mkQ (symProd a b) = 0
  have hqa : L.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero L).mpr ha
  rw [symmetricMap_symProd, hqa, symProd_zero_left]

/-- The difference from a section lift is a sum of products containing kernel factors. -/
theorem symmetric_section_error_mem (L : Submodule K V)
    (s : (V ⧸ L) →ₗ[K] V) (hs : L.mkQ.comp s = LinearMap.id)
    (x : SymmetricSquare K V) :
    x - SymmetricFunctor.map s (SymmetricFunctor.map L.mkQ x) ∈ formalMixed L := by
  induction x using symmetricSquare_induction with
  | hprod a b =>
    rw [symmetricMap_symProd, symmetricMap_symProd]
    have hmem (v : V) : v - s (L.mkQ v) ∈ L := by
      apply (Submodule.Quotient.mk_eq_zero L).mp
      change L.mkQ (v - s (L.mkQ v)) = 0
      rw [map_sub]
      have h := LinearMap.congr_fun hs (L.mkQ v)
      change L.mkQ (s (L.mkQ v)) = L.mkQ v at h
      rw [h, sub_self]
    have heq : symProd (K := K) a b - symProd (s (L.mkQ a)) (s (L.mkQ b)) =
        symProd (a - s (L.mkQ a)) b + symProd (s (L.mkQ a)) (b - s (L.mkQ b)) := by
      rw [symProd_sub_left, symProd_sub_right]
      abel
    rw [heq]
    exact (formalMixed L).add_mem (symProd_mem_formalMixed L (hmem a) b)
      (symProd_mem_formalMixed_right L _ (hmem b))
  | hzero => simp
  | hadd a b ha hb =>
    simpa only [map_add, add_sub_add_comm] using (formalMixed L).add_mem ha hb
  | hsmul c a ha =>
    simpa only [map_smul, smul_sub] using (formalMixed L).smul_mem c ha

/-- The full kernel identity for the actual symmetric square of a quotient. -/
theorem ker_symmetric_quotient (L : Submodule K V) :
    LinearMap.ker (SymmetricFunctor.map (ι := Fin 2) L.mkQ) = formalMixed L := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := L.mkQ.exists_rightInverse_of_surjective L.range_mkQ
    intro x hx
    have h := symmetric_section_error_mem L s hs x
    change SymmetricFunctor.map L.mkQ x = 0 at hx
    simpa only [hx, map_zero, sub_zero] using h
  · exact formalMixed_le_ker L

/-- Pulling mixed products back to a subspace gives the mixed products of the intersection. -/
theorem formalMixed_comap_subtype (L A : Submodule K V) :
    (formalMixed L).comap (SymmetricFunctor.map (ι := Fin 2) A.subtype) =
      formalMixed (L.comap A.subtype) := by
  let B : Submodule K A := L.comap A.subtype
  let j : (A ⧸ B) →ₗ[K] (V ⧸ L) := B.mapQ L A.subtype le_rfl
  have hj : Function.Injective j := by
    apply LinearMap.ker_eq_bot.mp
    change LinearMap.ker (B.mapQ L A.subtype le_rfl) = ⊥
    rw [Submodule.ker_mapQ]
    exact B.mkQ_map_self
  have hs : Function.Injective (SymmetricFunctor.map (ι := Fin 2) j) :=
    SymmetricFunctor.map_injective j hj
  have hcomm : j.comp B.mkQ = L.mkQ.comp A.subtype :=
    B.mapQ_mkQ L A.subtype
  have hsym := congrArg
    (fun f : A →ₗ[K] (V ⧸ L) => SymmetricFunctor.map (ι := Fin 2) f) hcomm
  simp only [SymmetricFunctor.map_comp] at hsym
  rw [← ker_symmetric_quotient L, ← ker_symmetric_quotient (L.comap A.subtype)]
  ext x
  change SymmetricFunctor.map L.mkQ (SymmetricFunctor.map A.subtype x) = 0 ↔
    SymmetricFunctor.map B.mkQ x = 0
  have hx := LinearMap.congr_fun hsym x
  change SymmetricFunctor.map j (SymmetricFunctor.map B.mkQ x) =
    SymmetricFunctor.map L.mkQ (SymmetricFunctor.map A.subtype x) at hx
  rw [← hx]
  constructor
  · intro h
    apply hs
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- The formal symmetric square of a subspace inside the ambient symmetric square. -/
def formalSquare (A : Submodule K V) : Submodule K (SymmetricSquare K V) :=
  LinearMap.range (SymmetricFunctor.map (ι := Fin 2) A.subtype)

/-- Products with the first factor in `L` and the second in `A`. -/
def formalProducts (L A : Submodule K V) : Submodule K (SymmetricSquare K V) :=
  Submodule.span K {x | ∃ a b, a ∈ L ∧ b ∈ A ∧ x = symProd a b}

/-- Express mixed products formed internally in `A` as ambient formal products. -/
theorem map_formalMixed_subtype (L A : Submodule K V) :
    (formalMixed (L.comap A.subtype)).map (SymmetricFunctor.map (ι := Fin 2) A.subtype) =
      formalProducts (L ⊓ A) A := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, ha, rfl⟩
    change SymmetricFunctor.map A.subtype (symProd a b) ∈ formalProducts (L ⊓ A) A
    rw [symmetricMap_symProd]
    exact Submodule.subset_span ⟨a.val, b.val, ⟨ha, a.property⟩, b.property, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, b, ha, hb, rfl⟩
    refine ⟨symProd (⟨a, ha.2⟩ : A) (⟨b, hb⟩ : A), ?_, ?_⟩
    · exact symProd_mem_formalMixed (L.comap A.subtype) (show (⟨a, ha.2⟩ : A) ∈ L.comap A.subtype from ha.1) (⟨b, hb⟩ : A)
    · exact symmetricMap_symProd A.subtype _ _

/-- The exact formal-product intersection identity (3.4) of the manuscript. -/
theorem formalMixed_inf_formalSquare (L A : Submodule K V) :
    formalMixed L ⊓ formalSquare A = formalProducts (L ⊓ A) A := by
  rw [← map_formalMixed_subtype L A, ← formalMixed_comap_subtype L A]
  ext x
  constructor
  · rintro ⟨hx, ⟨y, rfl⟩⟩
    exact ⟨y, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, ⟨y, rfl⟩⟩

end Froberg
