/-
# Proposition 2.1: the proposal is one finite-range cellular automaton on `ℤ⁶` (R5)

Node R5 of `BLUEPRINT.md` (Part A.2), NEW.

Paper (Prop 2.1): "Once `R, B, s` are fixed, (6) defines one computably specified finite-range
cellular automaton. The number of parent sites in both dependency directions together is at most
`κ = 2B(n_A + n_Q + 2)`, `n_A = 9q`, `n_Q = (2T+1)²[T(L+m-1)+1]⁴`. This bound is independent of `|R|`
and `n₀`."

* `siteEquiv : ℤ⁶ ≃+ ℤ² × ℤ⁴` (D5: coordinates `0, 1` planar, `2, …, 5` the provider coordinates);
* generic: a translation-commuting map `G` on configurations over `ℤ² × ℤ⁴` with a finite alphabet,
  local on a finite neighbourhood `N`, is one cellular automaton `caOf G N : CA 6` (alphabet
  `Fin |Σ|` through `Fintype.equivFin`, D6), with **`caOf_apply`** (its global map is `G`
  transported) and `card_nbhd_caOf` (`|N_F| ≤ |N|`);
* **`ruleCA CD s`** (the automaton (6) for chart data `CD`, `B` and `s`), `ruleCA_apply`, and
  **`prop_2_1`**: for `B ≥ 1`, `2|N_F| ≤ κ = 2B(n_A + n_Q + 2)`; the bound does not mention the
  tile type.
-/
import UncomputableNoiseDiagram.Rule.Proposal

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Rule

/-! ## The coordinate identification `ℤ⁶ ≅ ℤ² × ℤ⁴` -/

/-- The site of `ℤ² × ℤ⁴` with planar coordinates `x 0, x 1` and provider coordinates
`x 2, …, x 5`. -/
def toISite (x : UND.Site 6) : ISite := ((x 0, x 1), fun i => x i.succ.succ)

/-- The inverse identification. -/
def ofISite (p : ISite) : UND.Site 6 :=
  Fin.cons (α := fun _ => ℤ) p.1.1 (Fin.cons (α := fun _ => ℤ) p.1.2 p.2)

/-- D5: `ℤ⁶ ≃+ ℤ² × ℤ⁴`. -/
def siteEquiv : UND.Site 6 ≃+ ISite where
  toFun := toISite
  invFun := ofISite
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨a, b⟩, P⟩
    rfl
  map_add' x y := rfl

/-! ## A local translation-commuting map is a cellular automaton -/

variable {S : Type*} [Fintype S] [Nonempty S]

open Classical in
/-- Extend a pattern on the neighbourhood to a configuration (arbitrary elsewhere). -/
def extendPat (N6 : Finset (UND.Site 6)) (pat : N6 → Fin (Fintype.card S)) : ISite → S :=
  fun w => if h : siteEquiv.symm w ∈ N6 then (Fintype.equivFin S).symm (pat ⟨_, h⟩)
    else Classical.arbitrary S

/-- D6: the cellular automaton on `ℤ⁶` with alphabet `Fin |Σ|` given by a map `G` on
configurations over `ℤ² × ℤ⁴` and a finite neighbourhood `N`: the local rule evaluates `G` at the
origin on the pattern. -/
def caOf (G : (ISite → S) → (ISite → S)) (N : Finset ISite) : UND.CA 6 where
  numSymbols := Fintype.card S
  numSymbols_pos := Fintype.card_pos
  nbhd := N.image siteEquiv.symm
  localRule := fun pat => Fintype.equivFin S (G (extendPat (N.image siteEquiv.symm) pat) 0)

/-- The transported configuration. -/
def decodeConfig (x : UND.Site 6 → Fin (Fintype.card S)) : ISite → S :=
  fun w => (Fintype.equivFin S).symm (x (siteEquiv.symm w))

/-- **The global map of `caOf G N` is `G`** (transported through `siteEquiv` and
`Fintype.equivFin`), when `G` commutes with translations and is local on `N`. -/
theorem caOf_apply (G : (ISite → S) → (ISite → S)) (N : Finset ISite)
    (htr : ∀ x a, G (fun w => x (w + a)) = fun w => G x (w + a))
    (hloc : ∀ x y w, (∀ z ∈ N, x (w + z) = y (w + z)) → G x w = G y w)
    (x : UND.Site 6 → Fin (Fintype.card S)) (w6 : UND.Site 6) :
    (caOf G N).apply x w6 = Fintype.equivFin S (G (decodeConfig x) (siteEquiv w6)) := by
  classical
  set a := siteEquiv w6
  have h1 : G (decodeConfig x) a = G (fun w => decodeConfig x (w + a)) 0 := by
    have := congrFun (htr (decodeConfig x) a) 0
    rw [zero_add] at this
    exact this.symm
  rw [h1]
  show Fintype.equivFin S (G (extendPat (N.image siteEquiv.symm) (fun z => x (w6 + z.1))) 0) = _
  congr 1
  refine hloc _ _ 0 (fun z hz => ?_)
  rw [zero_add]
  have hmem : siteEquiv.symm z ∈ N.image siteEquiv.symm := Finset.mem_image_of_mem _ hz
  unfold extendPat decodeConfig
  rw [dite_eq_left hmem]
  congr 2
  rw [map_add, AddEquiv.symm_apply_apply, add_comm]

/-- The neighbourhood of `caOf G N` has at most `|N|` sites. -/
theorem card_nbhd_caOf (G : (ISite → S) → (ISite → S)) (N : Finset ISite) :
    (caOf G N).nbhd.card ≤ N.card :=
  Finset.card_image_le

/-! ## The automaton (6) -/

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] (CD : ChartData B τ)

instance : Nonempty (PhysSym CD) := ⟨(none, none, fun _ => 0)⟩

/-- **The automaton (6)** for the chart data `CD` (tile set `R` with its controller predicates), the
lane count `B` and the threshold `s`. -/
def ruleCA (s : ℕ) : UND.CA 6 := caOf (proposal (CD := CD) s) (nbhdP B)

/-- The global map of `ruleCA` is the proposal (6) (for `B ≥ 1`). -/
theorem ruleCA_apply (s : ℕ) (hB : 1 ≤ B) (x : UND.Site 6 → Fin (Fintype.card (PhysSym CD)))
    (w6 : UND.Site 6) :
    (ruleCA CD s).apply x w6 =
      Fintype.equivFin (PhysSym CD) (proposal s (decodeConfig x) (siteEquiv w6)) :=
  caOf_apply _ _ (fun x a => proposal_translate s x a)
    (fun _ _ _ h => proposal_local s hB h) x w6

/-- **Proposition 2.1.** For `B ≥ 1` the proposal (6) is one finite-range cellular automaton on
`ℤ⁶` whose global map is (6), and the parent sites in both dependency directions together number
at most `κ = 2B(n_A + n_Q + 2)`, a bound independent of the tile set. -/
theorem prop_2_1 (s : ℕ) (hB : 1 ≤ B) :
    (∀ x w6, (ruleCA CD s).apply x w6 =
      Fintype.equivFin (PhysSym CD) (proposal s (decodeConfig x) (siteEquiv w6))) ∧
    2 * (ruleCA CD s).nbhd.card ≤ UND.Param.kappa B := by
  refine ⟨ruleCA_apply CD s hB, ?_⟩
  have h1 := card_nbhd_caOf (proposal (CD := CD) s) (nbhdP B)
  have h2 := (card_nbhdP_le B).2
  have h3 := (UND.Param.parents_le B hB).2
  change 2 * (caOf (proposal (CD := CD) s) (nbhdP B)).nbhd.card ≤ _
  omega

end UND.Rule
