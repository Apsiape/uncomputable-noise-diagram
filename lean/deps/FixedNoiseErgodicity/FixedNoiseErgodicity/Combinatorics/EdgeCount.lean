/-
# Counting connected edge sets (`mem:count` = `fgt:count`)

`mem:count`: in a graph in which every vertex has at most `Δ` neighbours, at most `Δ^{2n}` sets
of `n` edges form a connected graph containing a given vertex `z`.

**[choice]** Mathlib has no existence theorem for Euler tours, so instead of doubling the edges
we grow a walk from `z` that uses exactly the edges of `K` and has `2|K|` steps: edges are added
one at a time, each touching the current walk (connectivity), by inserting a detour `a, b, a`.
The walk is encoded, step by step, by the number of the next vertex among the neighbours of the
current one. The statement is slightly more general than the paper's: `K` may be empty, and
connectivity is "every end of an edge of `K` is reachable from `z` along edges of `K`".
-/
import Mathlib.Data.Sym.Sym2
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace FNE.EdgeCount

variable {V : Type*} [DecidableEq V]

/-! ## Walks as vertex lists -/

/-- The edges traversed by a walk given by its list of vertices. -/
def edgesOf : List V → List (Sym2 V)
  | a :: b :: l => s(a, b) :: edgesOf (b :: l)
  | _ => []

theorem edgesOf_append_cons (l : List V) (x : V) (rest : List V) :
    edgesOf (l ++ x :: rest) = edgesOf (l ++ [x]) ++ edgesOf (x :: rest) := by
  induction l with
  | nil => simp [edgesOf]
  | cons c l ih =>
    cases l with
    | nil => simp [edgesOf]
    | cons d l => simp only [List.cons_append, edgesOf] at ih ⊢; simp [ih]

/-- Both ends of a traversed edge are vertices of the walk. -/
theorem mem_of_mem_edgesOf : ∀ {w : List V} {e : Sym2 V}, e ∈ edgesOf w → ∀ v ∈ e, v ∈ w
  | a :: b :: l, e, he, v, hv => by
    simp only [edgesOf, List.mem_cons] at he
    rcases he with rfl | he
    · rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp
    · exact List.mem_cons_of_mem _ (mem_of_mem_edgesOf he v hv)
  | [], _, he, _, _ => by simp [edgesOf] at he
  | [_], _, he, _, _ => by simp [edgesOf] at he

/-- The invariant of a growing walk from `z` that covers exactly `T ⊆ K`. -/
structure Covers (K T : Finset (Sym2 V)) (z : V) (w : List V) : Prop where
  head : w.head? = some z
  sub : ∀ e ∈ edgesOf w, e ∈ K
  eq : (edgesOf w).toFinset = T
  len : (edgesOf w).length = 2 * T.card

/-- Reachability along edges of `K`. -/
def Reach (K : Finset (Sym2 V)) : V → V → Prop :=
  Relation.ReflTransGen (fun a b => s(a, b) ∈ K)

/-- `K` is connected at `z`: every end of an edge of `K` is reachable from `z` inside `K`. -/
def ConnectedAt (K : Finset (Sym2 V)) (z : V) : Prop := ∀ e ∈ K, ∀ v ∈ e, Reach K z v

/-- An edge of `K \ T` touches the walk (connectivity). -/
theorem exists_touching {K T : Finset (Sym2 V)} {z : V} {w : List V} (hc : ConnectedAt K z)
    (hw : Covers K T z w) (hT : T ⊂ K) : ∃ e ∈ K, e ∉ T ∧ ∃ a ∈ e, a ∈ w := by
  obtain ⟨e₀, he₀K, he₀T⟩ := Finset.exists_of_ssubset hT
  have hz : z ∈ w := List.mem_of_mem_head? hw.head
  have key : ∀ v, Reach K z v → v ∈ w ∨ ∃ e ∈ K, e ∉ T ∧ ∃ a ∈ e, a ∈ w := by
    intro v hv
    induction hv with
    | refl => exact Or.inl hz
    | @tail b c _ hbc ih =>
      rcases ih with hb | hfound
      · by_cases hbcT : s(b, c) ∈ T
        · rw [← hw.eq, List.mem_toFinset] at hbcT
          exact Or.inl (mem_of_mem_edgesOf hbcT c (Sym2.mem_mk_right b c))
        · exact Or.inr ⟨s(b, c), hbc, hbcT, b, Sym2.mem_mk_left b c, hb⟩
      · exact Or.inr hfound
  induction e₀ using Sym2.ind with
  | h x y =>
    rcases key x (hc _ he₀K x (Sym2.mem_mk_left x y)) with hx | hfound
    · exact ⟨s(x, y), he₀K, he₀T, x, Sym2.mem_mk_left x y, hx⟩
    · exact hfound

/-- One growth step: insert a detour along a new edge touching the walk. -/
theorem covers_insert {K T : Finset (Sym2 V)} {z : V} {w : List V} (hw : Covers K T z w)
    {e : Sym2 V} (heK : e ∈ K) (heT : e ∉ T) {a : V} (ha : a ∈ e) (haw : a ∈ w) :
    ∃ w', Covers K (insert e T) z w' ∧ ∀ v ∈ w', v ∈ w ∨ v = Sym2.Mem.other ha := by
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem haw
  set b := Sym2.Mem.other ha
  have hab : s(a, b) = e := Sym2.other_spec ha
  refine ⟨L₁ ++ a :: b :: a :: L₂, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have := hw.head
    cases L₁ <;> simpa using this
  · intro e' he'
    rw [edgesOf_append_cons] at he'
    have hsub := hw.sub
    rw [edgesOf_append_cons] at hsub
    simp only [edgesOf, List.mem_append, List.mem_cons] at he' hsub
    rcases he' with h | rfl | rfl | h
    · exact hsub e' (Or.inl h)
    · rwa [hab]
    · rwa [Sym2.eq_swap, hab]
    · exact hsub e' (Or.inr h)
  · have heq := hw.eq
    rw [edgesOf_append_cons] at heq ⊢
    rw [← heq]
    ext e'
    simp only [edgesOf, List.toFinset_append, List.toFinset_cons, Finset.mem_union,
      Finset.mem_insert, ← hab, Sym2.eq_swap (a := b)]
    tauto
  · have hlen := hw.len
    rw [edgesOf_append_cons] at hlen ⊢
    simp only [edgesOf, List.length_append, List.length_cons] at hlen ⊢
    rw [Finset.card_insert_of_notMem heT]
    omega
  · intro v hv
    simp only [List.mem_append, List.mem_cons] at hv ⊢
    tauto

/-- Every connected `K` at `z` is covered by a walk from `z` with `2|K|` steps. -/
theorem exists_covering_walk {K : Finset (Sym2 V)} {z : V} (hc : ConnectedAt K z) :
    ∃ w, Covers K K z w := by
  have main : ∀ m, ∀ T ⊆ K, K.card - T.card = m → (∃ w, Covers K T z w) → ∃ w, Covers K K z w := by
    intro m
    induction m with
    | zero =>
      intro T hTK hm hw
      have : T = K := Finset.eq_of_subset_of_card_le hTK (by omega)
      exact this ▸ hw
    | succ m ih =>
      intro T hTK hm ⟨w, hw⟩
      have hT : T ⊂ K := Finset.ssubset_iff_subset_ne.mpr ⟨hTK, by rintro rfl; omega⟩
      obtain ⟨e, heK, heT, a, ha, haw⟩ := exists_touching hc hw hT
      refine ih (insert e T) (Finset.insert_subset heK hTK) ?_
        ((covers_insert hw heK heT ha haw).imp fun _ h => h.1)
      rw [Finset.card_insert_of_notMem heT]
      have := Finset.card_lt_card hT
      omega
  exact main _ ∅ (Finset.empty_subset _) rfl
    ⟨[z], rfl, by simp [edgesOf], by simp [edgesOf], by simp [edgesOf]⟩

/-- The covering walk visits at most `|K| + 1` vertices. -/
theorem exists_covering_walk_card {K : Finset (Sym2 V)} {z : V} (hc : ConnectedAt K z) :
    ∃ w, Covers K K z w ∧ w.toFinset.card ≤ K.card + 1 := by
  have main : ∀ m, ∀ T ⊆ K, K.card - T.card = m →
      (∃ w, Covers K T z w ∧ w.toFinset.card ≤ T.card + 1) →
        ∃ w, Covers K K z w ∧ w.toFinset.card ≤ K.card + 1 := by
    intro m
    induction m with
    | zero =>
      intro T hTK hm hw
      have : T = K := Finset.eq_of_subset_of_card_le hTK (by omega)
      exact this ▸ hw
    | succ m ih =>
      intro T hTK hm ⟨w, hw, hcard⟩
      have hT : T ⊂ K := Finset.ssubset_iff_subset_ne.mpr ⟨hTK, by rintro rfl; omega⟩
      obtain ⟨e, heK, heT, a, ha, haw⟩ := exists_touching hc hw hT
      obtain ⟨w', hw', hv⟩ := covers_insert hw heK heT ha haw
      refine ih (insert e T) (Finset.insert_subset heK hTK) ?_ ⟨w', hw', ?_⟩
      · rw [Finset.card_insert_of_notMem heT]
        have := Finset.card_lt_card hT
        omega
      · have hsub : w'.toFinset ⊆ insert (Sym2.Mem.other ha) w.toFinset := by
          intro v hvw
          rw [List.mem_toFinset] at hvw
          rcases hv v hvw with h | h
          · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr h)
          · rw [h]
            exact Finset.mem_insert_self _ _
        rw [Finset.card_insert_of_notMem heT]
        have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        omega
  exact main _ ∅ (Finset.empty_subset _) rfl
    ⟨[z], ⟨rfl, by simp [edgesOf], by simp [edgesOf], by simp [edgesOf]⟩, by simp⟩

/-- A set of `n` edges that is connected at `z` has at most `n + 1` vertices (`z` included). -/
theorem exists_vertices {K : Finset (Sym2 V)} {z : V} (hc : ConnectedAt K z) :
    ∃ Vs : Finset V, Vs.card ≤ K.card + 1 ∧ z ∈ Vs ∧ ∀ e ∈ K, ∀ v ∈ e, v ∈ Vs := by
  obtain ⟨w, hw, hcard⟩ := exists_covering_walk_card hc
  refine ⟨w.toFinset, hcard, List.mem_toFinset.mpr (List.mem_of_mem_head? hw.head),
    fun e he v hv => List.mem_toFinset.mpr (mem_of_mem_edgesOf ?_ v hv)⟩
  rw [← List.mem_toFinset, hw.eq]
  exact he

/-! ## Encoding walks by neighbour numbers -/

section Encode

variable (nbr : V → Finset V)

/-- Each step goes to a neighbour. -/
def Steps : List V → Prop
  | a :: b :: l => b ∈ nbr a ∧ Steps (b :: l)
  | _ => True

/-- The number of `b` among the neighbours of `a` (junk `0` if `b` is not a neighbour). -/
noncomputable def num (a b : V) : ℕ :=
  if h : b ∈ nbr a then (Fintype.equivFin {x // x ∈ nbr a} ⟨b, h⟩ : ℕ) else 0

theorem num_lt {a b : V} (h : b ∈ nbr a) : num nbr a b < (nbr a).card := by
  simp only [num, h, dite_true]
  have := (Fintype.equivFin {x // x ∈ nbr a} ⟨b, h⟩).isLt
  simpa [Fintype.card_coe] using this

theorem num_inj {a b b' : V} (h : b ∈ nbr a) (h' : b' ∈ nbr a)
    (he : num nbr a b = num nbr a b') : b = b' := by
  simp only [num, h, h', dite_true] at he
  have := (Fintype.equivFin {x // x ∈ nbr a}).injective (Fin.ext he)
  exact congrArg Subtype.val this

/-- The word of a walk. -/
noncomputable def wordOf : List V → List ℕ
  | a :: b :: l => num nbr a b :: wordOf (b :: l)
  | _ => []

theorem wordOf_length : ∀ w : List V, (wordOf nbr w).length = (edgesOf w).length
  | a :: b :: l => by simp [wordOf, edgesOf, wordOf_length (b :: l)]
  | [] => rfl
  | [_] => rfl

theorem wordOf_lt (Δ : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ) :
    ∀ w : List V, Steps nbr w → ∀ x ∈ wordOf nbr w, x < Δ
  | a :: b :: l, hs, x, hx => by
    simp only [wordOf, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact lt_of_lt_of_le (num_lt nbr hs.1) (hΔ a)
    · exact wordOf_lt Δ hΔ (b :: l) hs.2 x hx
  | [], _, x, hx => by simp [wordOf] at hx
  | [_], _, x, hx => by simp [wordOf] at hx

/-- A walk is determined by its first vertex and its word. -/
theorem eq_of_wordOf_eq : ∀ (w w' : List V), w.head? = w'.head? → Steps nbr w → Steps nbr w' →
    wordOf nbr w = wordOf nbr w' → w = w'
  | [], w', hh, _, _, _ => by cases w' <;> simp_all
  | [a], [], hh, _, _, _ => by simp at hh
  | [a], [a'], hh, _, _, _ => by simpa using hh
  | [a], a' :: b' :: l', _, _, _, hw => by simp [wordOf] at hw
  | a :: b :: l, [], hh, _, _, _ => by simp at hh
  | a :: b :: l, [a'], _, _, _, hw => by simp [wordOf] at hw
  | a :: b :: l, a' :: b' :: l', hh, hs, hs', hw => by
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp only [wordOf, List.cons.injEq] at hw
    have hb : b = b' := num_inj nbr hs.1 hs'.1 hw.1
    subst hb
    have := eq_of_wordOf_eq (b :: l) (b :: l') rfl hs.2 hs'.2 hw.2
    rw [this]

/-- Walks along edges of `K` take neighbour steps. -/
theorem steps_of_sub {K : Finset (Sym2 V)} (hK : ∀ a b, s(a, b) ∈ K → b ∈ nbr a) :
    ∀ w : List V, (∀ e ∈ edgesOf w, e ∈ K) → Steps nbr w
  | a :: b :: l, h => ⟨hK a b (h _ (by simp [edgesOf])),
      steps_of_sub hK (b :: l) fun e he => h e (by simp [edgesOf, he])⟩
  | [], _ => trivial
  | [_], _ => trivial

end Encode

/-! ## Bounded words -/

/-- The words of length `m` over `{0, …, Δ-1}`. -/
def boundedLists (Δ : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | m + 1 => (Finset.range Δ ×ˢ boundedLists Δ m).image (fun p => p.1 :: p.2)

theorem card_boundedLists_le (Δ : ℕ) : ∀ m, (boundedLists Δ m).card ≤ Δ ^ m
  | 0 => by simp [boundedLists]
  | m + 1 => by
    simp only [boundedLists]
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_product, Finset.card_range, pow_succ, mul_comm]
    exact Nat.mul_le_mul_right _ (card_boundedLists_le Δ m)

theorem mem_boundedLists (Δ : ℕ) :
    ∀ l : List ℕ, (∀ x ∈ l, x < Δ) → l ∈ boundedLists Δ l.length
  | [], _ => by simp [boundedLists]
  | x :: l, h => by
    simp only [List.length_cons, boundedLists, Finset.mem_image, Finset.mem_product,
      Finset.mem_range, Prod.exists]
    exact ⟨x, l, ⟨h x (by simp), mem_boundedLists Δ l fun y hy => h y (by simp [hy])⟩, rfl⟩

/-! ## `mem:count` -/

/-- **`mem:count` / `fgt:count`.** Let every vertex `a` have at most `Δ` neighbours (the finset
`nbr a`), and let `S` be a finite family of `n`-edge sets `K`, each made of graph edges and
connected at `z`. Then `|S| ≤ Δ^{2n}`. -/
theorem card_le_pow (nbr : V → Finset V) (Δ : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ) (z : V) (n : ℕ)
    (S : Finset (Finset (Sym2 V)))
    (hS : ∀ K ∈ S, K.card = n ∧ (∀ a b, s(a, b) ∈ K → b ∈ nbr a) ∧ ConnectedAt K z) :
    S.card ≤ Δ ^ (2 * n) := by
  classical
  have hw : ∀ K ∈ S, ∃ w, Covers K K z w := fun K hK => exists_covering_walk (hS K hK).2.2
  choose! walk hwalk using hw
  calc S.card ≤ (boundedLists Δ (2 * n)).card := by
        refine Finset.card_le_card_of_injOn (fun K => wordOf nbr (walk K)) ?_ ?_
        · intro K hK
          have hc := hwalk K hK
          have hsteps := steps_of_sub nbr (hS K hK).2.1 (walk K) hc.sub
          have hlen : (wordOf nbr (walk K)).length = 2 * n := by
            rw [wordOf_length, hc.len, (hS K hK).1]
          simpa [hlen] using mem_boundedLists Δ _ (wordOf_lt nbr Δ hΔ (walk K) hsteps)
        · intro K hK K' hK' heq
          have hc := hwalk K hK
          have hc' := hwalk K' hK'
          have hweq : walk K = walk K' :=
            eq_of_wordOf_eq nbr (walk K) (walk K') (by rw [hc.head, hc'.head])
              (steps_of_sub nbr (hS K hK).2.1 _ hc.sub)
              (steps_of_sub nbr (hS K' hK').2.1 _ hc'.sub) heq
          rw [← hc.eq, ← hc'.eq, hweq]
    _ ≤ Δ ^ (2 * n) := card_boundedLists_le Δ _

end FNE.EdgeCount
