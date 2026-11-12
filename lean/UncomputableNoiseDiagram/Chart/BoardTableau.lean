/-
# Lemma 3.3: channels, records and the recursion of the board computation (S8)

Part of node S8 of `BLUEPRINT.md` (Part A.3), NEW. Paper (Lemma 3.3, proof, last two paragraphs):
"Horizontal-only sites transmit horizontal colours and have empty vertical colours and records. …
Consequently consecutive logical cells share one horizontal colour … Apply the same argument to
vertical channels … Every active site has a triple record. … The shared vertical colour at `(i, j)`
and `(i, j+1)` has descriptions `(s_i(j), t_N(i,j)) = (t_S(i,j+1), s_i(j+1))`. Thus
`t_N(i,j) = s_i(j+1)` and `t_S(i,j+1) = s_i(j)`, with bottom symbols on the outer boundaries. At
`i = 0` the west flag initializes the contents. At `i < N_d - 1` the east colour is
`f_P(t_S, t_C, t_N)` and is passed to the next cell's central content. Substitution gives the stated
recursion `s_0(j) = init(H_row(y_j), χ₂(y_j), [j = 0])`,
`s_{i+1}(j) = f_P(s_i(j-1), s_i(j), s_i(j+1))`, `s_i(-1) = s_i(N_d) = ⊥`."

Formalization: consecutive free coordinates are `x < x'` free with no free coordinate between; the
first and last free coordinates are `L_* + 1`, `R_* - 1` (`Bot_* + 1`, `Top_* - 1`).
* `channel` (generic): a colour passes along a channel of copying sites;
* `board_hchannel`, `board_vchannel`: consecutive board cells share one horizontal (vertical)
  colour;
* **`board_record`**: every board site carries a record obeying (C0) and the tableau (10); in
  particular its central content never carries HALT;
* **`board_init`** (`s_0(j) = init(H_row, χ₂, [j = 0])`), **`board_step`**
  (`s_{i+1}(j) = f_P(t_S, s_i(j), t_N)`), **`board_vlink`** (`t_N(i,j) = s_i(j+1)`,
  `t_S(i,j+1) = s_i(j)`), **`board_bottom`**, **`board_top`** (`⊥` on the outer boundaries).
-/
import UncomputableNoiseDiagram.Chart.BoardFlags

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Chart

open UPD UPD.Scaffold

/-- **A channel** (one axis): if the east colour of each site equals the west colour of the next,
and every site strictly between `a < b` copies its west colour to its east colour, then the east
colour at `a` is the west colour at `b`. -/
theorem channel {β : Type*} (lW lE : ℤ → β) (hm : ∀ z, lE z = lW (z + 1)) {a b : ℤ} (hab : a < b)
    (hcopy : ∀ z, a < z → z < b → lW z = lE z) : lE a = lW b := by
  have key : ∀ i : ℕ, a + 1 + i ≤ b → lE a = lW (a + 1 + i) := by
    intro i
    induction i with
    | zero => intro _; rw [hm]; simp
    | succ i ih =>
      intro hi
      push_cast at hi ⊢
      rw [ih (by omega), hcopy _ (by omega) (by omega), hm]
      congr 1
      ring
  have := key (b - a - 1).toNat (by omega)
  rwa [show a + 1 + ((b - a - 1).toNat : ℤ) = b by omega] at this

variable {S : Type} [Fintype S] [DecidableEq S] {C : ContentOps S} {k : ℕ}
  {c : Plane → RTile C k} {τ : ℕ → Bool × Bool}

/-- Consecutive board cells on a free row share one horizontal colour. -/
theorem board_hchannel (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x x' y : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x)
    (hx' : IsFree (phaseOffsets (col τ)) d m₁ x') (hxx' : x < x')
    (hcons : ∀ z, x < z → z < x' → ¬ IsFree (phaseOffsets (col τ)) d m₁ z)
    (hy : IsFree (phaseOffsets (row τ)) d m₂ y) :
    (c (x, y)).1.1.lE = (c (x', y)).1.1.lW := by
  have hrow := board_row hc hτ hd m₁ m₂ hy
  refine channel (fun z => (c (z, y)).1.1.lW) (fun z => (c (z, y)).1.1.lE) (fun z => ?_) hxx'
    (fun z h1 h2 => ?_)
  · have h := congrArg (fun t => t.2.2.2) (hc.matchE (z, y))
    simpa only [Prod.mk_add_mk, add_zero, RVal.cE, RVal.cW] using h
  · have hz1 : frameLo (phaseOffsets (col τ)) d m₁ < z := by have := hx.1; omega
    have hz2 : z < frameHi (phaseOffsets (col τ)) d m₁ := by have := hx'.2.1; omega
    have hH : (c (z, y)).1.1.IsHCarrier := ⟨(hrow z hz1 hz2).1, (hrow z hz1 hz2).2.1⟩
    exact (c (z, y)).2.1.2.2.2.2.2.1.2
      ⟨hH, board_not_vcarrier hc hτ hd m₁ m₂ hz1 hz2 (hcons z h1 h2) hy⟩

/-- Consecutive board cells on a free column share one vertical colour. -/
theorem board_vchannel (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x y y' : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x)
    (hy : IsFree (phaseOffsets (row τ)) d m₂ y) (hy' : IsFree (phaseOffsets (row τ)) d m₂ y')
    (hyy' : y < y') (hcons : ∀ z, y < z → z < y' → ¬ IsFree (phaseOffsets (row τ)) d m₂ z) :
    (c (x, y)).1.1.lN = (c (x, y')).1.1.lS := by
  have hcol := board_col hc hτ hd m₁ m₂ hx
  refine channel (fun z => (c (x, z)).1.1.lS) (fun z => (c (x, z)).1.1.lN) (fun z => ?_) hyy'
    (fun z h1 h2 => ?_)
  · have h := congrArg (fun t => t.2.2.2) (hc.matchN (x, z))
    simpa only [Prod.mk_add_mk, add_zero, RVal.cN, RVal.cS] using h
  · have hz1 : frameLo (phaseOffsets (row τ)) d m₂ < z := by have := hy.1; omega
    have hz2 : z < frameHi (phaseOffsets (row τ)) d m₂ := by have := hy'.2.1; omega
    have hV : (c (x, z)).1.1.IsVCarrier := ⟨(hcol z hz1 hz2).1, (hcol z hz1 hz2).2.1⟩
    exact (c (x, z)).2.1.2.2.2.2.2.2.1.2
      ⟨hV, board_not_hcarrier hc hτ hd m₁ m₂ hz1 hz2 (hcons z h1 h2) hx⟩

/-- **Every board site carries a record** obeying (C0) and the tableau (10) (so its central content
never carries HALT). -/
theorem board_record (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x y : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x)
    (hy : IsFree (phaseOffsets (row τ)) d m₂ y) :
    ∃ tS tC tN, (c (x, y)).1.1.k = some (tS, tC, tN) ∧ (c (x, y)).1.1.C0 ∧
      (c (x, y)).1.1.Tab C tS tC tN :=
  (c (x, y)).2.1.2.2.2.2.2.2.2.2 (board_active hc hτ hd m₁ m₂ hx hy)

/-- The tableau of a given record at a board site. -/
theorem board_tab (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x y : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x)
    (hy : IsFree (phaseOffsets (row τ)) d m₂ y) {tS tN : Option S} {tC : S}
    (hk : (c (x, y)).1.1.k = some (tS, tC, tN)) : (c (x, y)).1.1.Tab C tS tC tN := by
  obtain ⟨a, b, e, hk', -, htab⟩ := board_record hc hτ hd m₁ m₂ hx hy
  rw [hk] at hk'
  simp only [Option.some.injEq, Prod.mk.injEq] at hk'
  obtain ⟨rfl, rfl, rfl⟩ := hk'
  exact htab

/-- **`s_0(j) = init(H_row(y_j), χ₂(y_j), [j = 0])`**: at the first free column the content is the
initial content of its row. -/
theorem board_init (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {y : ℤ} (hy : IsFree (phaseOffsets (row τ)) d m₂ y)
    {tS tN : Option S} {tC : S}
    (hk : (c (frameLo (phaseOffsets (col τ)) d m₁ + 1, y)).1.1.k = some (tS, tC, tN)) :
    tC = C.init (c (frameLo (phaseOffsets (col τ)) d m₁ + 1, y)).1.1.q.H
      (c (frameLo (phaseOffsets (col τ)) d m₁ + 1, y)).1.1.q.parent.1.a.1.b2
      (decide (y = frameLo (phaseOffsets (row τ)) d m₂ + 1)) := by
  have hx := isFree_rfree (frameOffsets_phase (col τ)) hd m₁
  have htab := board_tab hc hτ hd m₁ m₂ hx hy hk
  obtain ⟨hW, -⟩ := board_flags_row hc hτ hd m₁ m₂ hx hy
  obtain ⟨hS, -⟩ := board_flags_col hc hτ hd m₁ m₂ hx hy
  have hW' : (c (frameLo (phaseOffsets (col τ)) d m₁ + 1, y)).1.1.fW = true := by
    rw [show rfree (phaseOffsets (col τ)) d m₁ = frameLo (phaseOffsets (col τ)) d m₁ + 1 from rfl]
      at hW
    rw [hW]; simp
  have h := htab.2.2.2.2.1 hW'
  rw [h, hS]
  rfl

/-- **`s_{i+1}(j) = f_P(t_S, s_i(j), t_N)`**: the central content of the next board cell on a free
row is `f_P` of the record of the previous cell. -/
theorem board_step (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x x' y : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x)
    (hx' : IsFree (phaseOffsets (col τ)) d m₁ x') (hxx' : x < x')
    (hcons : ∀ z, x < z → z < x' → ¬ IsFree (phaseOffsets (col τ)) d m₁ z)
    (hy : IsFree (phaseOffsets (row τ)) d m₂ y) {tS tN tS' tN' : Option S} {tC tC' : S}
    (hk : (c (x, y)).1.1.k = some (tS, tC, tN)) (hk' : (c (x', y)).1.1.k = some (tS', tC', tN')) :
    tC' = C.fP tS tC tN := by
  have htab := board_tab hc hτ hd m₁ m₂ hx hy hk
  have htab' := board_tab hc hτ hd m₁ m₂ hx' hy hk'
  have hE : (c (x, y)).1.1.fE = false := by
    rw [(board_flags_row hc hτ hd m₁ m₂ hx hy).2]
    have := hx'.2.1
    simp only [decide_eq_false_iff_not]
    omega
  have hW : (c (x', y)).1.1.fW = false := by
    rw [(board_flags_row hc hτ hd m₁ m₂ hx' hy).1]
    have := hx.1
    simp only [decide_eq_false_iff_not]
    omega
  have h1 := htab.2.2.2.2.2.2.1 hE
  have h2 := htab'.2.2.2.2.2.1 hW
  have h3 := board_hchannel hc hτ hd m₁ m₂ hx hx' hxx' hcons hy
  rw [h1, h2] at h3
  exact (Option.some.inj h3).symm

/-- **`t_N(i,j) = s_i(j+1)`, `t_S(i,j+1) = s_i(j)`**: consecutive board cells on a free column read
each other's central contents. -/
theorem board_vlink (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x y y' : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x)
    (hy : IsFree (phaseOffsets (row τ)) d m₂ y) (hy' : IsFree (phaseOffsets (row τ)) d m₂ y')
    (hyy' : y < y') (hcons : ∀ z, y < z → z < y' → ¬ IsFree (phaseOffsets (row τ)) d m₂ z)
    {tS tN tS' tN' : Option S} {tC tC' : S}
    (hk : (c (x, y)).1.1.k = some (tS, tC, tN)) (hk' : (c (x, y')).1.1.k = some (tS', tC', tN')) :
    tN = some tC' ∧ tS' = some tC := by
  have htab := board_tab hc hτ hd m₁ m₂ hx hy hk
  have htab' := board_tab hc hτ hd m₁ m₂ hx hy' hk'
  have hN : (c (x, y)).1.1.fN = false := by
    rw [(board_flags_col hc hτ hd m₁ m₂ hx hy).2]
    have := hy'.2.1
    simp only [decide_eq_false_iff_not]
    omega
  have hS : (c (x, y')).1.1.fS = false := by
    rw [(board_flags_col hc hτ hd m₁ m₂ hx hy').1]
    have := hy.1
    simp only [decide_eq_false_iff_not]
    omega
  obtain ⟨v, hv, hlN⟩ := htab.2.2.2.1 hN
  obtain ⟨v', hv', hlS⟩ := htab'.2.1 hS
  have h3 := board_vchannel hc hτ hd m₁ m₂ hx hy hy' hyy' hcons
  rw [hlN, hlS] at h3
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj h3)
  exact ⟨by rw [hv, e2], by rw [hv', ← e1]⟩

/-- **`s_i(-1) = ⊥`**: at the first free row the south entry of every record is `⊥`. -/
theorem board_bottom (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x)
    {tS tN : Option S} {tC : S}
    (hk : (c (x, frameLo (phaseOffsets (row τ)) d m₂ + 1)).1.1.k = some (tS, tC, tN)) :
    tS = none := by
  have hy := isFree_rfree (frameOffsets_phase (row τ)) hd m₂
  have htab := board_tab hc hτ hd m₁ m₂ hx hy hk
  have hS := (board_flags_col hc hτ hd m₁ m₂ hx hy).1
  exact htab.1 (by rw [hS]; simp [rfree])

/-- **`s_i(N_d) = ⊥`**: at the last free row the north entry of every record is `⊥`. -/
theorem board_top (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x)
    {tS tN : Option S} {tC : S}
    (hk : (c (x, frameHi (phaseOffsets (row τ)) d m₂ - 1)).1.1.k = some (tS, tC, tN)) :
    tN = none := by
  have hy := isFree_frameHi_sub_one (frameOffsets_phase (row τ)) hd m₂
  have htab := board_tab hc hτ hd m₁ m₂ hx hy hk
  have hN := (board_flags_col hc hτ hd m₁ m₂ hx hy).2
  exact htab.2.2.1 (by rw [hN]; simp)

end UND.Chart
