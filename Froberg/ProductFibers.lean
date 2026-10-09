module

public import Froberg.Matching
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.Quotient

@[expose] public section

/-! The actual finite subset graphs in the product fibers of Lemma 4.1. -/
noncomputable section
namespace Froberg.ProductFibers
open Finset

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- The subsets of a fixed cardinality. -/
abbrev SizedSubset (R : Type*) [Fintype R] [DecidableEq R] (k : ℕ) :=
  {P : Finset R // P.card = k}

/-- Permuting the underlying indices permutes subsets of each size. -/
def subsetMap {k : ℕ} (e : Equiv.Perm R) : SizedSubset R k ≃ SizedSubset R k where
  toFun P := ⟨P.1.map e.toEmbedding, by simpa using P.2⟩
  invFun P := ⟨P.1.map e.symm.toEmbedding, by simpa using P.2⟩
  left_inv P := by ext x; simp
  right_inv P := by ext x; simp

@[simp] theorem subsetMap_val {k : ℕ} (e : Equiv.Perm R) (P : SizedSubset R k) :
    (subsetMap e P).1 = P.1.map e.toEmbedding := rfl

/-- The permutation group is transitive on subsets of a prescribed size. -/
theorem subset_transitive {k : ℕ} (P Q : SizedSubset R k) :
    ∃ e : Equiv.Perm R, subsetMap e P = Q := by
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq P.1 Q.1 (P.2.trans Q.2.symm)
  exact ⟨e, Subtype.ext he⟩

theorem perm_map_compl (e : Equiv.Perm R) (P : Finset R) :
    Pᶜ.map e.toEmbedding = (P.map e.toEmbedding)ᶜ := by
  ext x
  simp only [Finset.mem_map_equiv, Finset.mem_compl]

/-- Complement exchanges the two halves of a balanced partition. -/
def halfCompl {t : ℕ} (hR : Fintype.card R = 2 * t) :
    SizedSubset R t → SizedSubset R t := fun P =>
  ⟨P.1ᶜ, by rw [Finset.card_compl, hR, P.2]; omega⟩

@[simp] theorem halfCompl_halfCompl {t : ℕ} (hR : Fintype.card R = 2 * t)
    (P : SizedSubset R t) : halfCompl hR (halfCompl hR P) = P := by
  apply Subtype.ext
  simp [halfCompl]

@[simp] theorem subsetMap_halfCompl {t : ℕ} (hR : Fintype.card R = 2 * t)
    (e : Equiv.Perm R) (P : SizedSubset R t) :
    subsetMap e (halfCompl hR P) = halfCompl hR (subsetMap e P) := by
  apply Subtype.ext
  simp [halfCompl, subsetMap, perm_map_compl]

/-- Two oriented halves represent the same unordered partition exactly when they
are equal or complementary. -/
def partitionSetoid {t : ℕ} (hR : Fintype.card R = 2 * t) : Setoid (SizedSubset R t) where
  r P Q := P = Q ∨ P = halfCompl hR Q
  iseqv := ⟨fun P => Or.inl rfl, by
    intro P Q h
    rcases h with h | h
    · exact Or.inl h.symm
    · right
      rw [h, halfCompl_halfCompl], by
    intro P Q S h₁ h₂
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl (halfCompl_halfCompl hR S)⟩

/-- The source columns of a nontrivial product fiber. -/
abbrev Partition {t : ℕ} (hR : Fintype.card R = 2 * t) := Quotient (partitionSetoid hR)

instance {t : ℕ} (hR : Fintype.card R = 2 * t) : Fintype (Partition hR) :=
  Fintype.ofFinite _

def partitionMap {t : ℕ} (hR : Fintype.card R = 2 * t) (e : Equiv.Perm R) :
    Partition hR ≃ Partition hR :=
  Quotient.congr (subsetMap e) (by
    intro P Q
    change (P = Q ∨ P = halfCompl hR Q) ↔
      (subsetMap e P = subsetMap e Q ∨ subsetMap e P = halfCompl hR (subsetMap e Q))
    rw [← subsetMap_halfCompl, Equiv.apply_eq_iff_eq, Equiv.apply_eq_iff_eq])

@[simp] theorem partitionMap_mk {t : ℕ} (hR : Fintype.card R = 2 * t)
    (e : Equiv.Perm R) (P : SizedSubset R t) :
    partitionMap hR e ⟦P⟧ = ⟦subsetMap e P⟧ := rfl

/-- The adjacency condition is imposed on both halves, hence is independent of orientation. -/
def Adj {t m : ℕ} (hR : Fintype.card R = 2 * t) (allowed : ℕ → Prop)
    (p : Partition hR) (D : SizedSubset R m) : Prop :=
  Quotient.liftOn p (fun P => allowed (D.1 ∩ P.1).card ∧ allowed (D.1 ∩ P.1ᶜ).card)
    (by
      intro P Q h
      rcases h with rfl | rfl
      · rfl
      · simp only [halfCompl, compl_compl]
        exact propext and_comm)

@[simp] theorem adj_mk {t m : ℕ} (hR : Fintype.card R = 2 * t) (allowed : ℕ → Prop)
    (P : SizedSubset R t) (D : SizedSubset R m) :
    Adj hR allowed ⟦P⟧ D ↔
      allowed (D.1 ∩ P.1).card ∧ allowed (D.1 ∩ P.1ᶜ).card := Iff.rfl

/-- Adjacency is invariant under every permutation of the single indices. -/
theorem adj_map {t m : ℕ} (hR : Fintype.card R = 2 * t) (allowed : ℕ → Prop)
    (e : Equiv.Perm R) (p : Partition hR) (D : SizedSubset R m) :
    Adj hR allowed (partitionMap hR e p) (subsetMap e D) ↔ Adj hR allowed p D := by
  induction p using Quotient.inductionOn with | _ P =>
    simp only [partitionMap_mk, adj_mk, subsetMap_val]
    rw [← Finset.map_inter, ← perm_map_compl, ← Finset.map_inter]
    simp

/-- Every permutation orbit of source columns is the entire source class. -/
theorem partition_transitive {t : ℕ} (hR : Fintype.card R = 2 * t)
    (p q : Partition hR) : ∃ e : Equiv.Perm R, partitionMap hR e p = q := by
  induction p using Quotient.inductionOn with | _ P =>
    induction q using Quotient.inductionOn with | _ Q =>
      obtain ⟨e, he⟩ := subset_transitive P Q
      exact ⟨e, by simp [he]⟩

/-- The concrete subset graph is biregular, by permutation transitivity. -/
theorem subset_graph_symmetries {t m : ℕ} (hR : Fintype.card R = 2 * t)
    (allowed : ℕ → Prop) :
    (∀ p q : Partition hR, ∃ e : SizedSubset R m ≃ SizedSubset R m,
      ∀ D, Adj hR allowed p D ↔ Adj hR allowed q (e D)) ∧
    (∀ D E : SizedSubset R m, ∃ e : Partition hR ≃ Partition hR,
      ∀ p, Adj hR allowed p D ↔ Adj hR allowed (e p) E) := by
  constructor
  · intro p q
    obtain ⟨e, rfl⟩ := partition_transitive hR p q
    exact ⟨subsetMap e, fun D => (adj_map hR allowed e p D).symm⟩
  · intro D E
    obtain ⟨e, rfl⟩ := subset_transitive D E
    exact ⟨partitionMap hR e, fun p => (adj_map hR allowed e p D).symm⟩

/-- Target t-subsets have at least as many elements as the unordered source partitions. -/
theorem partition_card_le {t : ℕ} (hR : Fintype.card R = 2 * t) :
    Fintype.card (Partition hR) ≤ Fintype.card (SizedSubset R t) :=
  Fintype.card_le_of_injective Quotient.out Quotient.out_injective

/-- Orient a partition by taking the half containing a distinguished index. -/
def containingHalf {t : ℕ} (hR : Fintype.card R = 2 * t) (x : R)
    (p : Partition hR) : SizedSubset R t :=
  if x ∈ p.out.1 then p.out else halfCompl hR p.out

@[simp] theorem mem_containingHalf {t : ℕ} (hR : Fintype.card R = 2 * t)
    (x : R) (p : Partition hR) : x ∈ (containingHalf hR x p).1 := by
  simp only [containingHalf]
  split_ifs with h
  · exact h
  · exact Finset.mem_compl.mpr h

@[simp] theorem containingHalf_represents {t : ℕ} (hR : Fintype.card R = 2 * t)
    (x : R) (p : Partition hR) :
    (⟦containingHalf hR x p⟧ : Partition hR) = p := by
  rw [containingHalf]
  split_ifs
  · exact Quotient.out_eq p
  · trans (⟦p.out⟧ : Partition hR)
    · exact Quotient.sound (Or.inr rfl)
    · exact Quotient.out_eq p

/-- The two distinct form labels in each source column, oriented by a fixed index. -/
def partitionSide {t : ℕ} (hR : Fintype.card R = 2 * t) (x : R)
    (z : Partition hR × Bool) : SizedSubset R t :=
  if z.2 then halfCompl hR (containingHalf hR x z.1) else containingHalf hR x z.1

@[simp] theorem partitionSide_represents {t : ℕ} (hR : Fintype.card R = 2 * t)
    (x : R) (z : Partition hR × Bool) :
    (⟦partitionSide hR x z⟧ : Partition hR) = z.1 := by
  unfold partitionSide
  split_ifs
  · trans (⟦containingHalf hR x z.1⟧ : Partition hR)
    · exact Quotient.sound (Or.inr rfl)
    · exact containingHalf_represents hR x z.1
  · exact containingHalf_represents hR x z.1

@[simp] theorem mem_partitionSide_iff {t : ℕ} (hR : Fintype.card R = 2 * t)
    (x : R) (z : Partition hR × Bool) :
    x ∈ (partitionSide hR x z).1 ↔ z.2 = false := by
  rcases z with ⟨p, b⟩
  cases b <;> simp [partitionSide, halfCompl]

/-- The unique-partner property as an injective form-label map, directly usable
by the actual polynomial-minor construction. -/
theorem partitionSide_injective {t : ℕ} (hR : Fintype.card R = 2 * t) (x : R) :
    Function.Injective (partitionSide hR x) := by
  intro z z' h
  have hp : z.1 = z'.1 := by
    have he := congrArg (fun P => (⟦P⟧ : Partition hR)) h
    simpa only [partitionSide_represents] using he
  have hb : z.2 = z'.2 := by
    have he := congrArg (fun P : SizedSubset R t => x ∈ P.1) h
    simp only [mem_partitionSide_iff] at he
    cases hz : z.2 <;> cases hz' : z'.2 <;> simp_all
  exact Prod.ext hp hb

/-- Delete the distinguished index from its half. This is an injection into the
(t−1)-subsets, the capacity estimate for the odd, disjoint-support fiber. -/
def puncturedHalf {t : ℕ} (hR : Fintype.card R = 2 * t) (x : R)
    (p : Partition hR) : SizedSubset R (t - 1) :=
  ⟨(containingHalf hR x p).1.erase x, by
    rw [Finset.card_erase_of_mem (mem_containingHalf hR x p),
      (containingHalf hR x p).2]⟩

theorem puncturedHalf_injective {t : ℕ} (hR : Fintype.card R = 2 * t) (x : R) :
    Function.Injective (puncturedHalf hR x) := by
  intro p q h
  have he := congrArg (fun D : SizedSubset R (t - 1) => insert x D.1) h
  change insert x ((containingHalf hR x p).1.erase x) =
    insert x ((containingHalf hR x q).1.erase x) at he
  rw [Finset.insert_erase (mem_containingHalf hR x p),
    Finset.insert_erase (mem_containingHalf hR x q)] at he
  have he' : containingHalf hR x p = containingHalf hR x q := Subtype.ext he
  simpa using congrArg (fun P => (⟦P⟧ : Partition hR)) he'

theorem partition_card_le_pred {t : ℕ} (hR : Fintype.card R = 2 * t) (x : R) :
    Fintype.card (Partition hR) ≤ Fintype.card (SizedSubset R (t - 1)) :=
  Fintype.card_le_of_injective _ (puncturedHalf_injective hR x)

/-- Prescribed intersection sizes can be realized by choosing independently in
both halves of a partition. -/
theorem exists_edge {t m : ℕ} (hR : Fintype.card R = 2 * t)
    (allowed : ℕ → Prop) (r v : ℕ) (hrt : r ≤ t) (hvt : v ≤ t)
    (hrv : r + v = m) (hr : allowed r) (hv : allowed v) :
    ∃ p : Partition hR, ∃ D : SizedSubset R m, Adj hR allowed p D := by
  obtain ⟨P, _, hP⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset R)) (n := t) (by simpa [hR] using (show t ≤ 2*t by omega))
  obtain ⟨A, hAP, hA⟩ := Finset.exists_subset_card_eq (s := P) (n := r) (by omega)
  have hPc : Pᶜ.card = t := by rw [Finset.card_compl, hR, hP]; omega
  obtain ⟨B, hBP, hB⟩ := Finset.exists_subset_card_eq (s := Pᶜ) (n := v) (by omega)
  have hab : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    exact (Finset.mem_compl.mp (hBP hxB)) (hAP hxA)
  have hiA : (A ∪ B) ∩ P = A := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨ha | hb, hp⟩
      · exact ha
      · exact False.elim ((Finset.mem_compl.mp (hBP hb)) hp)
    · intro ha
      exact ⟨Or.inl ha, hAP ha⟩
  have hiB : (A ∪ B) ∩ Pᶜ = B := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨ha | hb, hp⟩
      · exact False.elim ((Finset.mem_compl.mp hp) (hAP ha))
      · exact hb
    · intro hb
      exact ⟨Or.inr hb, hBP hb⟩
  refine ⟨⟦⟨P,hP⟩⟧, ⟨A ∪ B, by rw [Finset.card_union_of_disjoint hab, hA, hB, hrv]⟩, ?_⟩
  change allowed ((A ∪ B) ∩ P).card ∧ allowed ((A ∪ B) ∩ Pᶜ).card
  simpa only [hiA, hiB, hA, hB] using And.intro hr hv

/-- A matching in the concrete subset graph, with every combinatorial hypothesis explicit. -/
theorem exists_subset_matching {t m : ℕ} (hR : Fintype.card R = 2 * t)
    (allowed : ℕ → Prop) (r v : ℕ) (hrt : r ≤ t) (hvt : v ≤ t)
    (hrv : r + v = m) (hr : allowed r) (hv : allowed v)
    (hcapacity : Fintype.card (Partition hR) ≤ Fintype.card (SizedSubset R m)) :
    ∃ f : Partition hR → SizedSubset R m,
      Function.Injective f ∧ ∀ p, Adj hR allowed p (f p) := by
  classical
  let neighbors : Partition hR → Finset (SizedSubset R m) :=
    fun p => Finset.univ.filter (Adj hR allowed p)
  obtain ⟨hl, hr'⟩ := subset_graph_symmetries (m := m) hR allowed
  suffices H : ∃ f : Partition hR → SizedSubset R m,
      Function.Injective f ∧ ∀ p, f p ∈ neighbors p by
    simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] using H
  apply Froberg.Matching.exists_matching_of_two_sided_symmetry neighbors
  · intro p q
    obtain ⟨e, he⟩ := hl p q
    exact ⟨e, fun D => by simpa [neighbors] using he D⟩
  · intro D E
    obtain ⟨e, he⟩ := hr' D E
    exact ⟨e, fun p => by simpa [neighbors] using he p⟩
  · obtain ⟨p, D, h⟩ := exists_edge hR allowed r v hrt hvt hrv hr hv
    exact ⟨p, D, by simpa [neighbors] using h⟩
  · exact hcapacity

/-- Lemma 4.1, even-degree product fibers: a matching into t-subsets. -/
theorem even_fiber_matching {a i t : ℕ} (hR : Fintype.card R = 2 * t)
    (hs : i + t = 2 * a) :
    ∃ f : Partition hR → SizedSubset R t,
      Function.Injective f ∧ ∀ p, Adj hR (fun b => a - i ≤ b ∧ b ≤ a) p (f p) := by
  apply exists_subset_matching hR _ (t / 2) (t - t / 2)
  · omega
  · omega
  · omega
  · constructor <;> omega
  · constructor <;> omega
  · exact partition_card_le hR

/-- Lemma 4.1, odd degree with a doubled index. The chosen y² index accounts
for the changed lower bound a+1−i. -/
theorem odd_doubled_fiber_matching {a i t : ℕ} (hR : Fintype.card R = 2 * t)
    (hs : i + t = 2 * a + 1) (hi : 1 ≤ i) :
    ∃ f : Partition hR → SizedSubset R t,
      Function.Injective f ∧ ∀ p, Adj hR (fun b => a + 1 - i ≤ b ∧ b ≤ a) p (f p) := by
  apply exists_subset_matching hR _ (t / 2) (t - t / 2)
  · omega
  · omega
  · omega
  · constructor <;> omega
  · constructor <;> omega
  · exact partition_card_le hR

/-- Lemma 4.1, odd disjoint-support fibers: a matching into (s−1)-subsets
meeting each half in exactly a indices, for s=2a+1. -/
theorem odd_disjoint_fiber_matching {a t : ℕ} (hR : Fintype.card R = 2 * t)
    (ht : t = 2 * a + 1) :
    ∃ f : Partition hR → SizedSubset R (t - 1),
      Function.Injective f ∧ ∀ p, Adj hR (fun b => b = a) p (f p) := by
  have hpos : 0 < Fintype.card R := by omega
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hpos
  apply exists_subset_matching hR _ a a
  · omega
  · omega
  · omega
  · rfl
  · rfl
  · exact partition_card_le_pred hR x

omit [Fintype R] in
/-- The intersection and union with one support determine the partner support.
Thus different product columns in a fixed index-degree fiber cannot share a form. -/
theorem unique_partner {S T U : Finset R}
    (hi : S ∩ T = S ∩ U) (hu : S ∪ T = S ∪ U) : T = U := by
  ext x
  have hi' := Finset.ext_iff.mp hi x
  have hu' := Finset.ext_iff.mp hu x
  simp only [Finset.mem_inter, Finset.mem_union] at hi' hu'
  tauto

/-- Every target subset divides into its intersections with the two source halves. -/
theorem card_inter_add_card_inter_compl (D P : Finset R) :
    (D ∩ P).card + (D ∩ Pᶜ).card = D.card := by
  have hs : D ∩ Pᶜ = D \ P := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
  rw [hs]
  exact Finset.card_inter_add_card_sdiff D P

/-- An allowed target admits a distribution of the doubled xy indices that gives
exactly a x-indices to each factor. This proves the numerical factorization step
of Lemma 4.1; in the odd case J omits the fixed y² index. -/
theorem allocate_doubled_indices {J : Type*} [Fintype J] [DecidableEq J]
    (D P : Finset R) (a : ℕ) (htotal : D.card + Fintype.card J = 2 * a)
    (hleft : (D ∩ P).card ≤ a) (hright : (D ∩ Pᶜ).card ≤ a) :
    ∃ E : Finset J,
      E.card + (D ∩ P).card = a ∧ Eᶜ.card + (D ∩ Pᶜ).card = a := by
  have hsplit := card_inter_add_card_inter_compl D P
  obtain ⟨E, _, hE⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset J)) (n := a - (D ∩ P).card)
    (by simp only [Finset.card_univ]; omega)
  exact ⟨E, by omega, by rw [Finset.card_compl]; omega⟩

end Froberg.ProductFibers
