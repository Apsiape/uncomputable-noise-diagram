/-
# Lemma 3.3: the exact boundary flags of a board (S8)

Part of node S8 of `BLUEPRINT.md` (Part A.3), NEW. Paper (Lemma 3.3, proof, fifth paragraph): "All
horizontal event tags in this strip are pairs. The left wall sets the inward minus entry to wall;
the right wall sets the inward plus entry to wall. Each active site supplies the facing cell
entries, and the single-carrier channels copy both entries. The successive gap pairs, including
gaps consisting of a single shared edge, are `(wall, cell)`, `(cell, cell)`, `(cell, wall)`. Thus
the west/east flags are exactly the two extreme-index indicators. The transposed event argument
proves the south/north flags."

The extreme free coordinates are `L_* + 1` and `R_* - 1` (`UPD.Scaffold.isFree_rfree`,
`isFree_frameHi_sub_one`), so "`f_W = [i = 0]`, `f_E = [i = N_d - 1]`" reads `f_W = [x = L_* + 1]`,
`f_E = [x = R_* - 1]`, and transposed `f_S = [y = Bot_* + 1]`, `f_N = [y = Top_* - 1]`.

* `flag_first`, `flag_second` (generic in the axis): the minus entries from the left wall and the
  plus entries from the right wall, through active sites and single-carrier channels;
* **`board_flags_row`**: at a board site (free × free), `f_W = [x = L_* + 1]`, `f_E = [x = R_* - 1]`;
* **`board_flags_col`**: `f_S = [y = Bot_* + 1]`, `f_N = [y = Top_* - 1]`.
-/
import UncomputableNoiseDiagram.Chart.BoardGaps

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Chart

open UPD UPD.Scaffold

/-- **Minus entries along a strip** (one axis): from the left wall's `wall`, through active sites'
`cell` and the channels' copies, the minus entry of the west tag at `x ∈ (L, R]` is `wall` exactly
at the first free coordinate `L + 1`. -/
theorem flag_first (eW eE : ℤ → Option (Ev × Ev)) (F : ℤ → Prop) {L R : ℤ}
    (hm : ∀ x, eE x = eW (x + 1)) (hL : Ev.FirstIs (eE L) .wall)
    (hact : ∀ x, L < x → x < R → F x → Ev.FirstIs (eE x) .cell)
    (hhor : ∀ x, L < x → x < R → ¬ F x → eW x = eE x) (hF1 : F (L + 1)) :
    ∀ x, L < x → x ≤ R → (eW x).map Prod.fst = some (if x = L + 1 then .wall else .cell) := by
  classical
  have key : ∀ i : ℕ, L + 1 + i ≤ R →
      (eW (L + 1 + i)).map Prod.fst = some (if L + 1 + (i : ℤ) = L + 1 then .wall else .cell) := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨b, hb⟩ := hL
      simp only [Nat.cast_zero, add_zero, ite_true]
      rw [← hm, hb]; rfl
    | succ i ih =>
      intro hi
      push_cast at hi ⊢
      have hx1 : L < L + 1 + i := by omega
      have hx2 : L + 1 + i < R := by omega
      have hne1 : L + 1 + (i : ℤ) + 1 ≠ L + 1 := by omega
      rw [show L + 1 + ((i : ℤ) + 1) = L + 1 + i + 1 by ring]
      simp only [hne1, ↓reduceIte]
      rw [← hm]
      by_cases hF : F (L + 1 + i)
      · obtain ⟨b, hb⟩ := hact _ hx1 hx2 hF
        rw [hb]; rfl
      · have hne : L + 1 + (i : ℤ) ≠ L + 1 := fun h => hF (by rw [h]; exact hF1)
        rw [← hhor _ hx1 hx2 hF, ih (by omega)]
        simp only [hne, ↓reduceIte]
  intro x hx1 hx2
  have := key (x - L - 1).toNat (by omega)
  rwa [show L + 1 + ((x - L - 1).toNat : ℤ) = x by omega] at this

/-- **Plus entries along a strip** (one axis): from the right wall's `wall`, through active sites'
`cell` and the channels' copies, the plus entry of the east tag at `x ∈ [L, R)` is `wall` exactly
at the last free coordinate `R - 1`. -/
theorem flag_second (eW eE : ℤ → Option (Ev × Ev)) (F : ℤ → Prop) {L R : ℤ}
    (hm : ∀ x, eE x = eW (x + 1)) (hR : Ev.SecondIs (eW R) .wall)
    (hact : ∀ x, L < x → x < R → F x → Ev.SecondIs (eW x) .cell)
    (hhor : ∀ x, L < x → x < R → ¬ F x → eW x = eE x) (hF1 : F (R - 1)) :
    ∀ x, L ≤ x → x < R → (eE x).map Prod.snd = some (if x = R - 1 then .wall else .cell) := by
  classical
  have key : ∀ i : ℕ, L ≤ R - 1 - i →
      (eE (R - 1 - i)).map Prod.snd = some (if R - 1 - (i : ℤ) = R - 1 then .wall else .cell) := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨a, ha⟩ := hR
      simp only [Nat.cast_zero, sub_zero, ite_true]
      rw [hm, sub_add_cancel, ha]; rfl
    | succ i ih =>
      intro hi
      push_cast at hi ⊢
      have hx1 : L < R - 1 - i := by omega
      have hx2 : R - 1 - i < R := by omega
      have hne1 : R - 1 - (i : ℤ) - 1 ≠ R - 1 := by omega
      rw [show R - 1 - ((i : ℤ) + 1) = R - 1 - i - 1 by ring]
      simp only [hne1, ↓reduceIte]
      rw [hm, sub_add_cancel]
      by_cases hF : F (R - 1 - i)
      · obtain ⟨a, ha⟩ := hact _ hx1 hx2 hF
        rw [ha]; rfl
      · have hne : R - 1 - (i : ℤ) ≠ R - 1 := fun h => hF (by rw [h]; exact hF1)
        rw [hhor _ hx1 hx2 hF, ih (by omega)]
        simp only [hne, ↓reduceIte]
  intro x hx1 hx2
  have := key (R - 1 - x).toNat (by omega)
  rwa [show R - 1 - ((R - 1 - x).toNat : ℤ) = x by omega] at this

theorem fW_of_map {S : Type} {s : RVal S} {v : Ev} (h : s.eW.map Prod.fst = some v) :
    s.fW = decide (v = .wall) := by
  unfold RVal.fW
  rcases he : s.eW with _ | ⟨a, b⟩
  · rw [he] at h; cases h
  · rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h; rfl

theorem fE_of_map {S : Type} {s : RVal S} {v : Ev} (h : s.eE.map Prod.snd = some v) :
    s.fE = decide (v = .wall) := by
  unfold RVal.fE
  rcases he : s.eE with _ | ⟨a, b⟩
  · rw [he] at h; cases h
  · rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h; rfl

theorem fS_of_map {S : Type} {s : RVal S} {v : Ev} (h : s.eS.map Prod.fst = some v) :
    s.fS = decide (v = .wall) := by
  unfold RVal.fS
  rcases he : s.eS with _ | ⟨a, b⟩
  · rw [he] at h; cases h
  · rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h; rfl

theorem fN_of_map {S : Type} {s : RVal S} {v : Ev} (h : s.eN.map Prod.snd = some v) :
    s.fN = decide (v = .wall) := by
  unfold RVal.fN
  rcases he : s.eN with _ | ⟨a, b⟩
  · rw [he] at h; cases h
  · rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h; rfl

theorem decide_ite_wall (p : Prop) [Decidable p] :
    decide ((if p then Ev.wall else Ev.cell) = Ev.wall) = decide p := by
  by_cases hp : p <;> simp [hp]

variable {S : Type} [Fintype S] [DecidableEq S] {C : ContentOps S} {k : ℕ}
  {c : Plane → RTile C k} {τ : ℕ → Bool × Bool}

theorem one_lt_ell_frame (a : ℕ → ℤ) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    frameLo a d m + 2 < frameHi a d m := by
  have hp : (4 : ℤ) ≤ 4 ^ d := le_self_pow₀ (by norm_num) (by omega)
  simp only [frameLo, frameHi]
  nlinarith

/-- **Lemma 3.3, west/east flags**: at a board site `(x, y)` (both free), `f_W = [x = L_* + 1]` and
`f_E = [x = R_* - 1]`. -/
theorem board_flags_row (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x y : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x)
    (hy : IsFree (phaseOffsets (row τ)) d m₂ y) :
    (c (x, y)).1.1.fW = decide (x = frameLo (phaseOffsets (col τ)) d m₁ + 1) ∧
      (c (x, y)).1.1.fE = decide (x = frameHi (phaseOffsets (col τ)) d m₁ - 1) := by
  set L := frameLo (phaseOffsets (col τ)) d m₁ with hLdef
  set R := frameHi (phaseOffsets (col τ)) d m₁ with hRdef
  have hLR := one_lt_ell_frame (phaseOffsets (col τ)) hd m₁
  obtain ⟨hVL, hVR, -⟩ := board_row_walls hτ hd m₁ m₂ hy
  have hrow := board_row hc hτ hd m₁ m₂ hy
  have hm : ∀ z : ℤ, (c (z, y)).1.1.eE = (c (z + 1, y)).1.1.eW := fun z => by
    have h := congrArg (fun t => t.2.2.1) (hc.matchE (z, y))
    simpa only [Prod.mk_add_mk, add_zero, RVal.cE, RVal.cW] using h
  have hoE : (c (L, y)).1.1.oE = (.L, .R) := by
    have h := congrArg (fun t => t.2.1) (hc.matchE (L, y))
    simp only [Prod.mk_add_mk, add_zero, RVal.cE, RVal.cW] at h
    rw [h]; exact (hrow (L + 1) (by omega) (by omega)).2.1
  have hoW : (c (R, y)).1.1.oW = (.L, .R) := by
    have h := congrArg (fun t => t.2.1) (hc.matchE (R - 1, y))
    simp only [Prod.mk_add_mk, add_zero, RVal.cE, RVal.cW, sub_add_cancel] at h
    rw [← h]; exact (hrow (R - 1) (by omega) (by omega)).2.2
  have hL : Ev.FirstIs (c (L, y)).1.1.eE .wall := (c (L, y)).2.1.2.2.2.1.2.2.1 ⟨hVL, hoE⟩
  have hR : Ev.SecondIs (c (R, y)).1.1.eW .wall := (c (R, y)).2.1.2.2.2.1.2.2.2 ⟨hVR, hoW⟩
  have hact : ∀ z, L < z → z < R → IsFree (phaseOffsets (col τ)) d m₁ z →
      (Ev.SecondIs (c (z, y)).1.1.eW .cell ∧ Ev.FirstIs (c (z, y)).1.1.eE .cell) := fun z _ _ hz =>
    (c (z, y)).2.1.2.2.2.1.2.1 (board_active hc hτ hd m₁ m₂ hz hy)
  have hhor : ∀ z, L < z → z < R → ¬ IsFree (phaseOffsets (col τ)) d m₁ z →
      (c (z, y)).1.1.eW = (c (z, y)).1.1.eE := fun z h1 h2 hz => by
    have hH : (c (z, y)).1.1.IsHCarrier := ⟨(hrow z h1 h2).1, (hrow z h1 h2).2.1⟩
    exact (c (z, y)).2.1.2.2.2.1.1 ⟨hH, board_not_vcarrier hc hτ hd m₁ m₂ h1 h2 hz hy⟩
  have h1 := flag_first (fun z => (c (z, y)).1.1.eW) (fun z => (c (z, y)).1.1.eE)
    (IsFree (phaseOffsets (col τ)) d m₁) hm hL (fun z a b hz => (hact z a b hz).2) hhor
    (isFree_rfree (frameOffsets_phase _) hd m₁) x hx.1 hx.2.1.le
  have h2 := flag_second (fun z => (c (z, y)).1.1.eW) (fun z => (c (z, y)).1.1.eE)
    (IsFree (phaseOffsets (col τ)) d m₁) hm hR (fun z a b hz => (hact z a b hz).1) hhor
    (isFree_frameHi_sub_one (frameOffsets_phase _) hd m₁) x hx.1.le hx.2.1
  rw [fW_of_map h1, fE_of_map h2, decide_ite_wall, decide_ite_wall]
  exact ⟨rfl, rfl⟩

/-- **Lemma 3.3, south/north flags**: at a board site `(x, y)` (both free), `f_S = [y = Bot_* + 1]`
and `f_N = [y = Top_* - 1]`. -/
theorem board_flags_col (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x y : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x)
    (hy : IsFree (phaseOffsets (row τ)) d m₂ y) :
    (c (x, y)).1.1.fS = decide (y = frameLo (phaseOffsets (row τ)) d m₂ + 1) ∧
      (c (x, y)).1.1.fN = decide (y = frameHi (phaseOffsets (row τ)) d m₂ - 1) := by
  set L := frameLo (phaseOffsets (row τ)) d m₂ with hLdef
  set R := frameHi (phaseOffsets (row τ)) d m₂ with hRdef
  have hLR := one_lt_ell_frame (phaseOffsets (row τ)) hd m₂
  obtain ⟨hHB, hHT, -⟩ := board_col_walls hτ hd m₁ m₂ hx
  have hcol := board_col hc hτ hd m₁ m₂ hx
  have hm : ∀ z : ℤ, (c (x, z)).1.1.eN = (c (x, z + 1)).1.1.eS := fun z => by
    have h := congrArg (fun t => t.2.2.1) (hc.matchN (x, z))
    simpa only [Prod.mk_add_mk, add_zero, RVal.cN, RVal.cS] using h
  have hoN : (c (x, L)).1.1.oN = (.B, .T) := by
    have h := congrArg (fun t => t.2.1) (hc.matchN (x, L))
    simp only [Prod.mk_add_mk, add_zero, RVal.cN, RVal.cS] at h
    rw [h]; exact (hcol (L + 1) (by omega) (by omega)).2.1
  have hoS : (c (x, R)).1.1.oS = (.B, .T) := by
    have h := congrArg (fun t => t.2.1) (hc.matchN (x, R - 1))
    simp only [Prod.mk_add_mk, add_zero, RVal.cN, RVal.cS, sub_add_cancel] at h
    rw [← h]; exact (hcol (R - 1) (by omega) (by omega)).2.2
  have hL : Ev.FirstIs (c (x, L)).1.1.eN .wall := (c (x, L)).2.1.2.2.2.2.1.2.2.1 ⟨hHB, hoN⟩
  have hR : Ev.SecondIs (c (x, R)).1.1.eS .wall := (c (x, R)).2.1.2.2.2.2.1.2.2.2 ⟨hHT, hoS⟩
  have hact : ∀ z, L < z → z < R → IsFree (phaseOffsets (row τ)) d m₂ z →
      (Ev.SecondIs (c (x, z)).1.1.eS .cell ∧ Ev.FirstIs (c (x, z)).1.1.eN .cell) := fun z _ _ hz =>
    (c (x, z)).2.1.2.2.2.2.1.2.1 (board_active hc hτ hd m₁ m₂ hx hz)
  have hver : ∀ z, L < z → z < R → ¬ IsFree (phaseOffsets (row τ)) d m₂ z →
      (c (x, z)).1.1.eS = (c (x, z)).1.1.eN := fun z h1 h2 hz => by
    have hV : (c (x, z)).1.1.IsVCarrier := ⟨(hcol z h1 h2).1, (hcol z h1 h2).2.1⟩
    exact (c (x, z)).2.1.2.2.2.2.1.1 ⟨hV, board_not_hcarrier hc hτ hd m₁ m₂ h1 h2 hz hx⟩
  have h1 := flag_first (fun z => (c (x, z)).1.1.eS) (fun z => (c (x, z)).1.1.eN)
    (IsFree (phaseOffsets (row τ)) d m₂) hm hL (fun z a b hz => (hact z a b hz).2) hver
    (isFree_rfree (frameOffsets_phase _) hd m₂) y hy.1 hy.2.1.le
  have h2 := flag_second (fun z => (c (x, z)).1.1.eS) (fun z => (c (x, z)).1.1.eN)
    (IsFree (phaseOffsets (row τ)) d m₂) hm hR (fun z a b hz => (hact z a b hz).1) hver
    (isFree_frameHi_sub_one (frameOffsets_phase _) hd m₂) y hy.1.le hy.2.1
  rw [fS_of_map h1, fN_of_map h2, decide_ite_wall, decide_ite_wall]
  exact ⟨rfl, rfl⟩

end UND.Chart
