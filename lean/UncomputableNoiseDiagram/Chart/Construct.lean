/-
# Prop 4.3, the nonhalting branch: the computational chart of a typical phase (M5)

Part of node M5 of `BLUEPRINT.md` (Part A.4). ADAPTED: the hard-model core's typical-phase
construction `UPD.BG.cfg` (`Background/Construct.lean`, DMhard Props 5.1, 5.7 and Lemma 5.3:
orientation tags `oEc`/`oNc`, event tags `eEc`/`eNc`, active sites `actF`, channels `HSeg`/`VSeg`,
grid sites `GPos`, `gsite`) supplies the routing fields verbatim (D31: `UPD.Scaffold.Typical`);
the decorated quarters, colours, records and central words are NEW.

Paper (Prop 4.3, proof, nonhalting): "For nonhalting choose a typical phase and cutoff `2a-2` or
`2a-1`. In a typical phase, [DMhard, Propositions 5.1 and 5.7 and Lemma 5.3] give a legal
assignment of the orientation and event tags, with active sites exactly the grids
`F_d^{(1)} × F_d^{(2)}`, each active site in one grid, and the boundary flags of Lemma 3.3. These
assignments use only (O1)–(E3), which we retain. Fill every board with its initialized finite run.
Large boards decode `n` by Lemmas 4.2 and 4.1; small boards fail or reach a boundary. A finite
exit fails, so none contains HALT. Fill channel colours from their board and put empty records
elsewhere. These assignments satisfy all tuple filters, and the phase extension is unique."

* `freeAt_eq_zeta`: our `freeAt` (by `Nat.nth`) is the hard-model core's `ζ`;
* `dqOf` (the decorated quarter with the cutoff `[r < cut]`), **`dqOf_spec`** (Lemma 3.2 as a
  definition: a legal decorated chart over `Y_τ` for typical `τ`);
* `HSegM`, `VSegM`, `GPosM` (channels and board sites with the row frame `I_d(m)` named, so that
  the board's input tracks are known), uniqueness;
* `sAt` (the board content `s_i(j)`), `hcolF` (`s_{i+1}(j)` on `[x_i, x_{i+1})`), `vcolF`
  (`(s_i(j), s_i(j+1))` on `[y_j, y_{j+1})`), `recF` (the record at `(x_i, y_j)`), `lEm`, `lNm`,
  `kFm`; their values at the board sites (`lEm_gsite`, …, `kFm_gsite`);
* `rawVal`, `rawOf` (the tile data: routing tuple and central word of `Y_τ`);
* (O1)–(E3) from `UPD.BG.cfg_O1 … cfg_E3` (the fields are the same), (K1), (K2), and at the board
  sites (C0) and **the tableau (10)** (`raw_rules`: "no HALT" from `board_run_no_halt`, the input
  tracks from `runP_tracks`, `chi2_eq`, `freeAt_eq_zeta`); `raw_allowed`, `raw_tileOK`, matching
  (`raw_tileE`, `raw_tileN`: decorated quarters, routing colours, overlapping words, the decoded
  phase copies horizontally and increases by one vertically);
* `NHalt U n₀ cut` (the hypotheses of the nonhalting branch), **`chartOf`**, **`chartOf_isRChart`**
  (a legal `R`-chart for every typical phase), `chartOf_phase` (its quarter phase is `τ`),
  `chartOf_V`, `chartOf_H` (the cutoff `[r < cut]`), **`chartOf_bottom_flag`** (row flag one on
  bottom rows of depths `d < a`, zero on depths `d ≥ a`).
-/
import UncomputableNoiseDiagram.Chart.NonHalting
import UndecidablePhaseDiagram.Background.BgMap

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Chart

open UPD UPD.Scaffold

/-! ## `freeAt` is the hard-model core's `ζ` -/

theorem nd_eq (d : ℕ) : MachineM.Nd d = Nd d := rfl

theorem freeAt_eq_zeta (t : ℕ → Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {i : ℕ} (hi : i < Nd d) :
    freeAt t d m i = BG.zeta (phaseOffsets t) d m i := by
  have ha := frameOffsets_phase t
  have hc : (BG.freeSet (phaseOffsets t) d m).card = MachineM.Nd d := BG.card_freeSet ha hd m
  have hu := Finset.orderEmbOfFin_unique (s := BG.freeSet (phaseOffsets t) d m)
    (f := fun x : Fin (BG.freeSet (phaseOffsets t) d m).card => freeAt t d m x.val) rfl
    (fun x => BG.mem_freeSet.2 (freeAt_free t hd m (lt_of_lt_of_eq x.2 hc)))
    (fun x y hxy => freeAt_lt t hd m hxy (lt_of_lt_of_eq y.2 hc))
  rw [BG.zeta_eq ha hd m hi]
  exact congrFun hu ⟨i, by rw [hc]; exact hi⟩

/-! ## The decorated quarters of the construction -/

/-- The bits passing the filter (8): the given ones if they pass it, else `V = H_row = 1`. -/
def okBits (ψ : Black) (V H : Bool) : Bool × Bool := if rankOK ψ V H then (V, H) else (true, true)

theorem rankOK_okBits (ψ : Black) (V H : Bool) :
    rankOK ψ (okBits ψ V H).1 (okBits ψ V H).2 = true := by
  unfold okBits
  split
  · assumption
  · cases ψ <;> rfl

/-- The decorated quarter at `ξ` for the cutoff `b_r = [r < cut]` (Lemma 3.2): the quarter
`Y_τ(ξ)` with `V = [rank(ξ₁) < cut]`, `H_row = [rank(ξ₂) < cut]` (the filter (8) holds for
typical `τ`, `dqOf_spec`). -/
def dqOf (cut : ℕ) (τ : ℕ → Bool × Bool) (ξ : Plane) : DQuarter :=
  ⟨(qtilingOf τ ξ).quad, ⟨⟨(qtilingOf τ ξ).parent,
    (okBits (qtilingOf τ ξ).parent.1.base.black (decide (prankOf (col τ) ξ.1 < cut))
      (decide (prankOf (row τ) ξ.2 < cut))).1,
    (okBits (qtilingOf τ ξ).parent.1.base.black (decide (prankOf (col τ) ξ.1 < cut))
      (decide (prankOf (row τ) ξ.2 < cut))).2⟩, rankOK_okBits _ _ _⟩⟩

theorem dqOf_toQ (cut : ℕ) (τ : ℕ → Bool × Bool) (ξ : Plane) :
    (dqOf cut τ ξ).toQ = qtilingOf τ ξ := rfl

theorem exists_prank_of_notInt {t : ℕ → Bool} (h : NotInt t) (z : ℤ) : ∃ r, PRank t z r :=
  (NotInt.tail h).exists_rank _

/-- For typical `τ` the decorated quarters form a legal decorated chart over `Y_τ` with the cutoff
`b_r = [r < cut]` (Lemma 3.2, second sentence, as a definition). -/
theorem dqOf_spec {τ : ℕ → Bool × Bool} (hτ : Typical τ) (cut : ℕ) :
    IsDTiling (dqOf cut τ) ∧ (∀ ξ, (dqOf cut τ ξ).V = decide (prankOf (col τ) ξ.1 < cut)) ∧
      (∀ ξ, (dqOf cut τ ξ).H = decide (prankOf (row τ) ξ.2 < cut)) := by
  obtain ⟨-, hP⟩ := qtilingOf_spec hτ.1
  obtain ⟨Z, hZ, hZq, hZV, hZH⟩ := cutoff_exists hP hτ.2.1 hτ.2.2.1 cut
  have hrc := fun z => prankOf_spec (exists_prank_of_notInt hτ.2.1 z)
  have hrr := fun z => prankOf_spec (exists_prank_of_notInt hτ.2.2.1 z)
  have e : ∀ ξ, dqOf cut τ ξ = Z ξ := by
    intro ξ
    have hq := hZq ξ
    have hV := hZV ξ _ (hrc ξ.1)
    have hH := hZH ξ _ (hrr ξ.2)
    generalize Z ξ = q at hq hV hH ⊢
    obtain ⟨quad, ⟨⟨a, V, H⟩, hp⟩⟩ := q
    simp only [DQuarter.toQ] at hq
    simp only [DQuarter.V] at hV
    simp only [DQuarter.H] at hH
    subst hV hH
    simp only [dqOf, okBits, ← hq, hp, ↓reduceIte]
  have hZ' : dqOf cut τ = Z := funext e
  refine ⟨hZ' ▸ hZ, fun ξ => ?_, fun ξ => ?_⟩
  · rw [e, hZV ξ _ (hrc ξ.1)]
  · rw [e, hZH ξ _ (hrr ξ.2)]

/-! ## Channels and board sites, with the row frame named -/

/-- `ξ` lies on the horizontal channel `[x_i, x_{i+1})` of the row `y_j` of a depth-`d` board whose
row frame is `I_d(m)` (`p = (d, i, j, m)`; the hard-model core's `HSeg` with `m₂` named). -/
def HSegM (τ : ℕ → Bool × Bool) (p : ℕ × ℕ × ℕ × ℤ) (ξ : Plane) : Prop :=
  1 ≤ p.1 ∧ p.2.1 + 1 < MachineM.Nd p.1 ∧ p.2.2.1 < MachineM.Nd p.1 ∧ ∃ m1 : ℤ,
    ξ.2 = BG.zeta (BG.a2 τ) p.1 p.2.2.2 p.2.2.1 ∧ BG.zeta (BG.a1 τ) p.1 m1 p.2.1 ≤ ξ.1 ∧
      ξ.1 < BG.zeta (BG.a1 τ) p.1 m1 (p.2.1 + 1)

/-- `ξ` lies on the vertical channel `[y_j, y_{j+1})` of the column `x_i` of a depth-`d` board
whose row frame is `I_d(m)` (`p = (d, i, j, m)`). -/
def VSegM (τ : ℕ → Bool × Bool) (p : ℕ × ℕ × ℕ × ℤ) (ξ : Plane) : Prop :=
  1 ≤ p.1 ∧ p.2.1 < MachineM.Nd p.1 ∧ p.2.2.1 + 1 < MachineM.Nd p.1 ∧ ∃ m1 : ℤ,
    ξ.1 = BG.zeta (BG.a1 τ) p.1 m1 p.2.1 ∧ BG.zeta (BG.a2 τ) p.1 p.2.2.2 p.2.2.1 ≤ ξ.2 ∧
      ξ.2 < BG.zeta (BG.a2 τ) p.1 p.2.2.2 (p.2.2.1 + 1)

/-- `ξ = (x_i, y_j)` on a depth-`d` board whose row frame is `I_d(m)`. -/
def GPosM (τ : ℕ → Bool × Bool) (p : ℕ × ℕ × ℕ × ℤ) (ξ : Plane) : Prop :=
  1 ≤ p.1 ∧ p.2.1 < MachineM.Nd p.1 ∧ p.2.2.1 < MachineM.Nd p.1 ∧ ∃ m1 : ℤ,
    ξ = BG.gsite τ p.1 m1 p.2.2.2 p.2.1 p.2.2.1

section Segments

variable {τ : ℕ → Bool × Bool}

theorem HSegM.hseg {d i j : ℕ} {m : ℤ} {ξ : Plane} (h : HSegM τ (d, i, j, m) ξ) :
    BG.HSeg τ (d, i, j) ξ := by
  obtain ⟨h1, h2, h3, m1, h4⟩ := h
  exact ⟨h1, h2, h3, m1, m, h4⟩

theorem VSegM.vseg {d i j : ℕ} {m : ℤ} {ξ : Plane} (h : VSegM τ (d, i, j, m) ξ) :
    BG.VSeg τ (d, i, j) ξ := by
  obtain ⟨h1, h2, h3, m1, h4⟩ := h
  exact ⟨h1, h2, h3, m1, m, h4⟩

theorem GPosM.gpos {d i j : ℕ} {m : ℤ} {ξ : Plane} (h : GPosM τ (d, i, j, m) ξ) :
    BG.GPos τ (d, i, j) ξ := by
  obtain ⟨h1, h2, h3, m1, h4⟩ := h
  exact ⟨h1, h2, h3, m1, m, h4⟩

theorem HSegM_unique {p p' : ℕ × ℕ × ℕ × ℤ} {ξ : Plane} (h : HSegM τ p ξ) (h' : HSegM τ p' ξ) :
    p = p' := by
  obtain ⟨d, i, j, m⟩ := p
  obtain ⟨d', i', j', m'⟩ := p'
  have e := BG.HSeg_unique h.hseg h'.hseg
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  obtain ⟨hd, -, hj, -, hy, -⟩ := h
  obtain ⟨-, -, -, -, hy', -⟩ := h'
  have f := BG.zeta_free (frameOffsets_phase (row τ)) hd m hj
  have f' := BG.zeta_free (frameOffsets_phase (row τ)) hd m' hj
  rw [← hy] at f
  rw [← hy'] at f'
  obtain ⟨-, rfl⟩ := BG.free_unique hd hd f f'
  rfl

theorem VSegM_unique {p p' : ℕ × ℕ × ℕ × ℤ} {ξ : Plane} (h : VSegM τ p ξ) (h' : VSegM τ p' ξ) :
    p = p' := by
  obtain ⟨d, i, j, m⟩ := p
  obtain ⟨d', i', j', m'⟩ := p'
  have e := BG.VSeg_unique h.vseg h'.vseg
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  have ha2 : FrameOffsets (BG.a2 τ) := frameOffsets_phase _
  obtain ⟨hd, -, hj, -, -, hy1, hy2⟩ := h
  obtain ⟨-, -, -, -, -, hy1', hy2'⟩ := h'
  dsimp only at hd hj hy1 hy2 hy1' hy2'
  have f0 := BG.zeta_free ha2 hd m (show j < MachineM.Nd d by omega)
  have f1 := BG.zeta_free ha2 hd m hj
  have f0' := BG.zeta_free ha2 hd m' (show j < MachineM.Nd d by omega)
  have f1' := BG.zeta_free ha2 hd m' hj
  have := frame_window_unique (a := BG.a2 τ) (d := d) (m := m) (m' := m') (z := ξ.2)
    ⟨by have := f0.1; omega, by have := f1.2.1; omega⟩
    ⟨by have := f0'.1; omega, by have := f1'.2.1; omega⟩
  subst this
  rfl

theorem GPosM_unique {p p' : ℕ × ℕ × ℕ × ℤ} {ξ : Plane} (h : GPosM τ p ξ) (h' : GPosM τ p' ξ) :
    p = p' := by
  obtain ⟨d, i, j, m⟩ := p
  obtain ⟨d', i', j', m'⟩ := p'
  have e := BG.GPos_unique h.gpos h'.gpos
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  obtain ⟨hd, -, hj, m1, hy⟩ := h
  obtain ⟨-, -, -, m1', hy'⟩ := h'
  dsimp only at hd hj
  have f := BG.zeta_free (frameOffsets_phase (row τ)) hd m hj
  have f' := BG.zeta_free (frameOffsets_phase (row τ)) hd m' hj
  rw [show BG.zeta (BG.a2 τ) d m j = ξ.2 by rw [hy]; rfl] at f
  rw [show BG.zeta (BG.a2 τ) d m' j = ξ.2 by rw [hy']; rfl] at f'
  obtain ⟨-, rfl⟩ := BG.free_unique hd hd f f'
  rfl

end Segments

/-! ## Board contents, colours and records -/

section Contents

variable (U : Machine) (n0 cut : ℕ) (τ : ℕ → Bool × Bool)

/-- The content `s_i(j)` of the depth-`d` board with row frame `I_d(m)`: the board run of `P` on the
input tracks `[rank(y_j) < cut]`, `rank(y_j) mod 2` (`initP` beyond the board). -/
def sAt (d : ℕ) (m : ℤ) (i j : ℕ) : MachineP.Cell U n0 :=
  if hj : j < Nd d then
    MachineP.runP U n0 (Nd d) (cutH (row τ) d m cut) (cutPi (row τ) d m) i ⟨j, hj⟩
  else MachineP.initP U n0 false false false

/-- The horizontal colour of the channel `[x_i, x_{i+1})` of row `y_j`: `s_{i+1}(j)`. -/
def hcolF (p : ℕ × ℕ × ℕ × ℤ) : MachineP.Cell U n0 :=
  sAt U n0 cut τ p.1 p.2.2.2 (p.2.1 + 1) p.2.2.1

/-- The vertical colour of the channel `[y_j, y_{j+1})` of column `x_i`: `(s_i(j), s_i(j+1))`. -/
def vcolF (p : ℕ × ℕ × ℕ × ℤ) : MachineP.Cell U n0 × MachineP.Cell U n0 :=
  (sAt U n0 cut τ p.1 p.2.2.2 p.2.1 p.2.2.1, sAt U n0 cut τ p.1 p.2.2.2 p.2.1 (p.2.2.1 + 1))

/-- The record at `(x_i, y_j)`: `(s_i(j-1) or ⊥, s_i(j), s_i(j+1) or ⊥)`. -/
def recF (p : ℕ × ℕ × ℕ × ℤ) :
    Option (MachineP.Cell U n0) × MachineP.Cell U n0 × Option (MachineP.Cell U n0) :=
  (if p.2.2.1 = 0 then none else some (sAt U n0 cut τ p.1 p.2.2.2 p.2.1 (p.2.2.1 - 1)),
    sAt U n0 cut τ p.1 p.2.2.2 p.2.1 p.2.2.1,
    if p.2.2.1 + 1 < Nd p.1 then some (sAt U n0 cut τ p.1 p.2.2.2 p.2.1 (p.2.2.1 + 1)) else none)

open Classical in
/-- `ℓ^E` at `ξ`: the horizontal colour on the channels, `∘` elsewhere. -/
def lEm (ξ : Plane) : Option (MachineP.Cell U n0) :=
  if h : ∃ p, HSegM τ p ξ then some (hcolF U n0 cut τ h.choose) else none

open Classical in
/-- `ℓ^N` at `ξ`: the vertical colour on the channels, `∘` elsewhere. -/
def lNm (ξ : Plane) : Option (MachineP.Cell U n0 × MachineP.Cell U n0) :=
  if h : ∃ p, VSegM τ p ξ then some (vcolF U n0 cut τ h.choose) else none

open Classical in
/-- The record at `ξ`: `recF` at the board sites, empty elsewhere. -/
def kFm (ξ : Plane) :
    Option (Option (MachineP.Cell U n0) × MachineP.Cell U n0 × Option (MachineP.Cell U n0)) :=
  if h : ∃ p, GPosM τ p ξ then some (recF U n0 cut τ h.choose) else none

variable {U n0 cut τ}

theorem lEm_of {p : ℕ × ℕ × ℕ × ℤ} {ξ : Plane} (h : HSegM τ p ξ) :
    lEm U n0 cut τ ξ = some (hcolF U n0 cut τ p) := by
  have hex : ∃ p, HSegM τ p ξ := ⟨p, h⟩
  rw [lEm, dite_eq_left hex, HSegM_unique hex.choose_spec h]

theorem lEm_none {ξ : Plane} (h : ¬ ∃ p, HSegM τ p ξ) : lEm U n0 cut τ ξ = none := by
  rw [lEm, dite_eq_right h]

theorem lNm_of {p : ℕ × ℕ × ℕ × ℤ} {ξ : Plane} (h : VSegM τ p ξ) :
    lNm U n0 cut τ ξ = some (vcolF U n0 cut τ p) := by
  have hex : ∃ p, VSegM τ p ξ := ⟨p, h⟩
  rw [lNm, dite_eq_left hex, VSegM_unique hex.choose_spec h]

theorem lNm_none {ξ : Plane} (h : ¬ ∃ p, VSegM τ p ξ) : lNm U n0 cut τ ξ = none := by
  rw [lNm, dite_eq_right h]

theorem kFm_of {p : ℕ × ℕ × ℕ × ℤ} {ξ : Plane} (h : GPosM τ p ξ) :
    kFm U n0 cut τ ξ = some (recF U n0 cut τ p) := by
  have hex : ∃ p, GPosM τ p ξ := ⟨p, h⟩
  rw [kFm, dite_eq_left hex, GPosM_unique hex.choose_spec h]

theorem kFm_none {ξ : Plane} (h : ¬ ∃ p, GPosM τ p ξ) : kFm U n0 cut τ ξ = none := by
  rw [kFm, dite_eq_right h]

theorem sAt_zero {d : ℕ} {m : ℤ} {j : ℕ} (hj : j < Nd d) :
    sAt U n0 cut τ d m 0 j = MachineP.initP U n0 (cutH (row τ) d m cut j) (cutPi (row τ) d m j)
      (decide (j = 0)) := by
  rw [sAt, dite_eq_left hj]
  rfl

theorem sAt_of {d : ℕ} {m : ℤ} {i j : ℕ} (hj : j < Nd d) :
    sAt U n0 cut τ d m i j =
      MachineP.runP U n0 (Nd d) (cutH (row τ) d m cut) (cutPi (row τ) d m) i ⟨j, hj⟩ := by
  rw [sAt, dite_eq_left hj]

theorem runP_succ (N : ℕ) (h pi : ℕ → Bool) (i : ℕ) :
    MachineP.runP U n0 N h pi (i + 1) = MachineP.nextRow (MachineP.runP U n0 N h pi i) :=
  Function.iterate_succ_apply' _ _ _

theorem sAt_succ {d : ℕ} {m : ℤ} {i j : ℕ} (hj : j < Nd d) :
    sAt U n0 cut τ d m (i + 1) j = MachineP.fP U n0
      (if j = 0 then none else some (sAt U n0 cut τ d m i (j - 1))) (sAt U n0 cut τ d m i j)
      (if j + 1 < Nd d then some (sAt U n0 cut τ d m i (j + 1)) else none) := by
  rw [sAt_of hj, sAt_of hj, runP_succ]
  simp only [MachineP.nextRow]
  congr 1
  · rcases j with _ | j
    · simp
    · rw [dite_eq_left (Nat.succ_pos j), ite_eq_right (Nat.succ_ne_zero j), sAt_of (by omega)]
  · by_cases h : j + 1 < Nd d
    · rw [dite_eq_left h, ite_eq_left h, sAt_of h]
    · rw [dite_eq_right h, ite_eq_right h]

end Contents


/-! ## The colours and records at the sites of a board -/

section Gsite

variable {U : Machine} {n0 cut : ℕ} {τ : ℕ → Bool × Bool} {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ)
  {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d)
include hd hi hj

theorem lEm_gsite :
    lEm U n0 cut τ (BG.gsite τ d m1 m2 i j) =
      if i + 1 < MachineM.Nd d then some (hcolF U n0 cut τ (d, i, j, m2)) else none := by
  have ha1 : FrameOffsets (BG.a1 τ) := frameOffsets_phase _
  split_ifs with h
  · exact lEm_of (p := (d, i, j, m2)) ⟨hd, h, hj, m1, rfl, le_rfl,
      (BG.zeta_lt_iff ha1 hd m1 hi h).2 (by omega)⟩
  · refine lEm_none ?_
    rintro ⟨⟨d', i', j', m'⟩, hs⟩
    have fi := BG.zeta_free ha1 hd m1 hi
    obtain ⟨rfl, -, hi', e1, e2⟩ := BG.HSeg_inv hd hj rfl ⟨fi.1.le, fi.2.1.le⟩ hs.hseg
    have : i < i' + 1 := (BG.zeta_lt_iff ha1 hd m1 hi hi').1 e2
    omega

theorem lWm_gsite :
    lEm U n0 cut τ ((BG.gsite τ d m1 m2 i j).1 - 1, (BG.gsite τ d m1 m2 i j).2) =
      if i = 0 then none else some (hcolF U n0 cut τ (d, i - 1, j, m2)) := by
  have ha1 : FrameOffsets (BG.a1 τ) := frameOffsets_phase _
  split_ifs with h
  · refine lEm_none ?_
    rintro ⟨⟨d', i', j', m'⟩, hs⟩
    subst h
    have hs' := hs.hseg
    simp only [BG.gsite, BG.zeta_zero ha1 hd m1] at hs'
    have hlh := frameLo_lt_frameHi (BG.a1 τ) d m1
    obtain ⟨rfl, -, hi', e1, -⟩ := BG.HSeg_inv (m1 := m1) hd hj rfl
      ⟨by simp [rfree], by simp only [rfree]; omega⟩ hs'
    have := (BG.zeta_free (i := i') ha1 hd m1 (by omega)).1
    simp only [rfree] at e1; omega
  · have hpos : 0 < i := Nat.pos_of_ne_zero h
    have hlt := (BG.zeta_lt_iff ha1 hd m1 (show i - 1 < MachineM.Nd d by omega) hi).2 (by omega)
    refine lEm_of (p := (d, i - 1, j, m2)) ⟨hd, by simp only; omega, hj, m1, rfl, ?_, ?_⟩
    · simp only [BG.gsite]; omega
    · simp only [BG.gsite]; rw [Nat.sub_add_cancel hpos]; omega

theorem lNm_gsite :
    lNm U n0 cut τ (BG.gsite τ d m1 m2 i j) =
      if j + 1 < MachineM.Nd d then some (vcolF U n0 cut τ (d, i, j, m2)) else none := by
  have ha2 : FrameOffsets (BG.a2 τ) := frameOffsets_phase _
  split_ifs with h
  · exact lNm_of (p := (d, i, j, m2)) ⟨hd, hi, h, m1, rfl, le_rfl,
      (BG.zeta_lt_iff ha2 hd m2 hj h).2 (by omega)⟩
  · refine lNm_none ?_
    rintro ⟨⟨d', i', j', m'⟩, hs⟩
    have fj := BG.zeta_free ha2 hd m2 hj
    obtain ⟨rfl, -, hj', e1, e2⟩ := BG.VSeg_inv hd hi rfl ⟨fj.1.le, fj.2.1.le⟩ hs.vseg
    have : j < j' + 1 := (BG.zeta_lt_iff ha2 hd m2 hj hj').1 e2
    omega

theorem lSm_gsite :
    lNm U n0 cut τ ((BG.gsite τ d m1 m2 i j).1, (BG.gsite τ d m1 m2 i j).2 - 1) =
      if j = 0 then none else some (vcolF U n0 cut τ (d, i, j - 1, m2)) := by
  have ha2 : FrameOffsets (BG.a2 τ) := frameOffsets_phase _
  split_ifs with h
  · refine lNm_none ?_
    rintro ⟨⟨d', i', j', m'⟩, hs⟩
    subst h
    have hs' := hs.vseg
    simp only [BG.gsite, BG.zeta_zero ha2 hd m2] at hs'
    have hlh := frameLo_lt_frameHi (BG.a2 τ) d m2
    obtain ⟨rfl, -, hj', e1, -⟩ := BG.VSeg_inv (m2 := m2) hd hi rfl
      ⟨by simp [rfree], by simp only [rfree]; omega⟩ hs'
    have := (BG.zeta_free (i := j') ha2 hd m2 (by omega)).1
    simp only [rfree] at e1; omega
  · have hpos : 0 < j := Nat.pos_of_ne_zero h
    have hlt := (BG.zeta_lt_iff ha2 hd m2 (show j - 1 < MachineM.Nd d by omega) hj).2 (by omega)
    refine lNm_of (p := (d, i, j - 1, m2)) ⟨hd, hi, by simp only; omega, m1, rfl, ?_, ?_⟩
    · simp only [BG.gsite]; omega
    · simp only [BG.gsite]; rw [Nat.sub_add_cancel hpos]; omega

theorem kFm_gsite :
    kFm U n0 cut τ (BG.gsite τ d m1 m2 i j) = some (recF U n0 cut τ (d, i, j, m2)) :=
  kFm_of (p := (d, i, j, m2)) ⟨hd, hi, hj, m1, rfl⟩

end Gsite

/-! ## The site values and their tests -/

section Values

variable (U : Machine) (n0 k cut : ℕ) (τ : ℕ → Bool × Bool)

/-- The routing tuple at `ξ`: the decorated quarter (cutoff `[r < cut]`), the orientation and event
tags of the hard-model core's typical-phase construction (`UPD.BG.cfg`: DMhard Props 5.1, 5.7,
Lemma 5.3), the colours of the channels and the records of the board runs. -/
def rawVal (ξ : Plane) : RVal (MachineP.Cell U n0) where
  q := dqOf cut τ ξ
  oW := BG.oEc τ (ξ.1 - 1, ξ.2)
  oE := BG.oEc τ ξ
  oS := BG.oNc τ (ξ.1, ξ.2 - 1)
  oN := BG.oNc τ ξ
  eW := BG.eEc τ (ξ.1 - 1, ξ.2)
  eE := BG.eEc τ ξ
  eS := BG.eNc τ (ξ.1, ξ.2 - 1)
  eN := BG.eNc τ ξ
  lW := lEm U n0 cut τ (ξ.1 - 1, ξ.2)
  lE := lEm U n0 cut τ ξ
  lS := lNm U n0 cut τ (ξ.1, ξ.2 - 1)
  lN := lNm U n0 cut τ ξ
  k := kFm U n0 cut τ ξ

/-- The tile data at `ξ`: the routing tuple and the central word of `Y_τ` at `ξ`. -/
def rawOf (ξ : Plane) : RVal (MachineP.Cell U n0) × Word (winRad k) :=
  (rawVal U n0 cut τ ξ, wordAt (winRad k) (qtilingOf τ) ξ)

/-- The hard-model core's construction (all spins `+`): its routing fields are those of `rawVal`. -/
abbrev cfgP (ξ : Plane) : SiteVal U := BG.cfg U τ (fun _ => Spin.plus) ξ

variable {U n0 cut τ}

theorem raw_active (ξ : Plane) : (rawVal U n0 cut τ ξ).IsActive ↔ (cfgP U τ ξ).IsActive :=
  Iff.rfl

theorem raw_O1 (hτ : Typical τ) (ξ : Plane) : (rawVal U n0 cut τ ξ).O1 :=
  BG.cfg_O1 (U := U) hτ (fun _ => Spin.plus) ξ

theorem raw_O2 (hτ : Typical τ) (ξ : Plane) : (rawVal U n0 cut τ ξ).O2 :=
  BG.cfg_O2 (U := U) hτ (fun _ => Spin.plus) ξ

theorem raw_E1 (ξ : Plane) : (rawVal U n0 cut τ ξ).E1 :=
  BG.cfg_E1 (U := U) (τ := τ) (fun _ => Spin.plus) ξ

theorem raw_E2 (hτ : Typical τ) (ξ : Plane) : (rawVal U n0 cut τ ξ).E2 :=
  BG.cfg_E2 (U := U) hτ (fun _ => Spin.plus) ξ

theorem raw_E3 (hτ : Typical τ) (ξ : Plane) : (rawVal U n0 cut τ ξ).E3 :=
  BG.cfg_E3 (U := U) hτ (fun _ => Spin.plus) ξ

theorem raw_K1 (hτ : Typical τ) (ξ : Plane) : (rawVal U n0 cut τ ξ).K1 := by
  have ha1 : FrameOffsets (BG.a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (BG.a2 τ) := frameOffsets_phase _
  obtain ⟨z, y⟩ := ξ
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · refine lEm_none ?_
    rintro ⟨⟨d, i, j, m⟩, hs⟩
    have := (BG.hseg_carrier (U := U) hτ (fun _ => Spin.plus) hs.hseg).2
    rw [sub_add_cancel] at this
    exact h this
  · exact lEm_none fun ⟨⟨d, i, j, m⟩, hs⟩ =>
      h (BG.hseg_carrier (U := U) hτ (fun _ => Spin.plus) hs.hseg).1
  · obtain ⟨-, hnV⟩ := h
    have hna : ¬ BG.actF τ (z, y) := fun ha =>
      hnV ((BG.cfg_active (U := U) hτ (fun _ => Spin.plus) _).2 ha).2
    show lEm U n0 cut τ (z - 1, y) = lEm U n0 cut τ (z, y)
    by_cases h1 : ∃ p, HSegM τ p (z - 1, y)
    · obtain ⟨⟨d, i, j, m⟩, hs⟩ := h1
      rw [lEm_of hs]
      obtain ⟨hd, hi, hj, m1, ey, ex1, ex2⟩ := hs
      simp only at hd hi hj ey ex1 ex2
      by_cases hz : z < BG.zeta (BG.a1 τ) d m1 (i + 1)
      · rw [lEm_of (p := (d, i, j, m)) ⟨hd, hi, hj, m1, ey, by dsimp only; omega, hz⟩]
      · exfalso
        have hz' : z = BG.zeta (BG.a1 τ) d m1 (i + 1) := by omega
        exact hna ⟨d, m1, m, hd, by rw [hz']; exact BG.zeta_free ha1 hd m1 hi,
          by dsimp only; rw [ey]; exact BG.zeta_free ha2 hd m hj⟩
    · rw [lEm_none h1]
      symm
      refine lEm_none ?_
      rintro ⟨⟨d, i, j, m⟩, hs⟩
      obtain ⟨hd, hi, hj, m1, ey, ex1, ex2⟩ := hs
      simp only at hd hi hj ey ex1 ex2
      by_cases hz : BG.zeta (BG.a1 τ) d m1 i < z
      · exact h1 ⟨(d, i, j, m), hd, hi, hj, m1, ey, by dsimp only; omega, by dsimp only; omega⟩
      · have hz' : z = BG.zeta (BG.a1 τ) d m1 i := by omega
        exact hna ⟨d, m1, m, hd, by rw [hz']; exact BG.zeta_free ha1 hd m1 (by omega),
          by dsimp only; rw [ey]; exact BG.zeta_free ha2 hd m hj⟩

theorem raw_K2 (hτ : Typical τ) (ξ : Plane) : (rawVal U n0 cut τ ξ).K2 := by
  have ha1 : FrameOffsets (BG.a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (BG.a2 τ) := frameOffsets_phase _
  obtain ⟨x, z⟩ := ξ
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · refine lNm_none ?_
    rintro ⟨⟨d, i, j, m⟩, hs⟩
    have := (BG.vseg_carrier (U := U) hτ (fun _ => Spin.plus) hs.vseg).2
    rw [sub_add_cancel] at this
    exact h this
  · exact lNm_none fun ⟨⟨d, i, j, m⟩, hs⟩ =>
      h (BG.vseg_carrier (U := U) hτ (fun _ => Spin.plus) hs.vseg).1
  · obtain ⟨-, hnH⟩ := h
    have hna : ¬ BG.actF τ (x, z) := fun ha =>
      hnH ((BG.cfg_active (U := U) hτ (fun _ => Spin.plus) _).2 ha).1
    show lNm U n0 cut τ (x, z - 1) = lNm U n0 cut τ (x, z)
    by_cases h1 : ∃ p, VSegM τ p (x, z - 1)
    · obtain ⟨⟨d, i, j, m⟩, hs⟩ := h1
      rw [lNm_of hs]
      obtain ⟨hd, hi, hj, m1, ex, ey1, ey2⟩ := hs
      simp only at hd hi hj ex ey1 ey2
      by_cases hz : z < BG.zeta (BG.a2 τ) d m (j + 1)
      · rw [lNm_of (p := (d, i, j, m)) ⟨hd, hi, hj, m1, ex, by dsimp only; omega, hz⟩]
      · exfalso
        have hz' : z = BG.zeta (BG.a2 τ) d m (j + 1) := by omega
        exact hna ⟨d, m1, m, hd, by dsimp only; rw [ex]; exact BG.zeta_free ha1 hd m1 hi,
          by rw [hz']; exact BG.zeta_free ha2 hd m hj⟩
    · rw [lNm_none h1]
      symm
      refine lNm_none ?_
      rintro ⟨⟨d, i, j, m⟩, hs⟩
      obtain ⟨hd, hi, hj, m1, ex, ey1, ey2⟩ := hs
      simp only at hd hi hj ex ey1 ey2
      by_cases hz : BG.zeta (BG.a2 τ) d m j < z
      · exact h1 ⟨(d, i, j, m), hd, hi, hj, m1, ex, by dsimp only; omega, by dsimp only; omega⟩
      · have hz' : z = BG.zeta (BG.a2 τ) d m j := by omega
        exact hna ⟨d, m1, m, hd, by dsimp only; rw [ex]; exact BG.zeta_free ha1 hd m1 hi,
          by rw [hz']; exact BG.zeta_free ha2 hd m (by omega)⟩

end Values


/-! ## The tableau at the board sites, and legality -/

/-- The hypotheses of the nonhalting branch of Prop 4.3: for some `n ≥ 1` on which `U` does not
halt, `n₀ ≥ 1` and the cutoff is `2a - 2` or `2a - 1`, `a = n + n₀`. -/
def NHalt (U : Machine) (n0 cut : ℕ) : Prop :=
  ∃ n, 1 ≤ n ∧ 1 ≤ n0 ∧ ¬ U.HaltsOn n ∧ (cut = 2 * (n + n0) - 2 ∨ cut = 2 * (n + n0) - 1)

section Rules

variable {U : Machine} {n0 cut : ℕ} {τ : ℕ → Bool × Bool} (hτ : Typical τ) {d : ℕ} (hd : 1 ≤ d)
  (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d)
include hτ hd hj

omit hi in
/-- `H_row` at a board site is the input track `h_in` of its board. -/
theorem raw_H : (rawVal U n0 cut τ (BG.gsite τ d m1 m2 i j)).q.H = cutH (row τ) d m2 cut j := by
  rw [cutH, ite_eq_left (show j < Nd d from hj), freeAt_eq_zeta (row τ) hd m2 hj]
  exact (dqOf_spec hτ cut).2.2 _

omit hi in
/-- `χ₂` at a board site is the input track `π` of its board. -/
theorem raw_B :
    (rawVal U n0 cut τ (BG.gsite τ d m1 m2 i j)).q.parent.1.a.1.b2 = cutPi (row τ) d m2 j := by
  rw [cutPi, freeAt_eq_zeta (row τ) hd m2 hj]
  exact chi2_eq (Z := dqOf cut τ) (qtilingOf_spec hτ.1).2 (BG.gsite τ d m1 m2 i j)
    (prankOf_spec (exists_prank_of_notInt hτ.2.2.1 _))

include hi

/-- **The tableau (10) at a board site**: with the record `recF`, (C0) and (10) hold, including
"no HALT" (`board_run_no_halt`) and the read-only input tracks (`runP_tracks`). -/
theorem raw_rules (hN : NHalt U n0 cut) :
    (rawVal U n0 cut τ (BG.gsite τ d m1 m2 i j)).C0 ∧
    (rawVal U n0 cut τ (BG.gsite τ d m1 m2 i j)).Tab (contentP U n0)
      (recF U n0 cut τ (d, i, j, m2)).1 (recF U n0 cut τ (d, i, j, m2)).2.1
      (recF U n0 cut τ (d, i, j, m2)).2.2 := by
  obtain ⟨n, hn, hn0, hU, hcut⟩ := hN
  obtain ⟨fW, fE, fS, fN⟩ := BG.cfg_grids_c (U := U) hτ (fun _ => Spin.plus) hd m1 m2 hi hj
  have hlW := lWm_gsite (U := U) (n0 := n0) (cut := cut) (τ := τ) hd m1 m2 hi hj
  have hlE := lEm_gsite (U := U) (n0 := n0) (cut := cut) (τ := τ) hd m1 m2 hi hj
  have hlS := lSm_gsite (U := U) (n0 := n0) (cut := cut) (τ := τ) hd m1 m2 hi hj
  have hlN := lNm_gsite (U := U) (n0 := n0) (cut := cut) (τ := τ) hd m1 m2 hi hj
  have hH := raw_H (U := U) (n0 := n0) (cut := cut) hτ hd m1 m2 (i := i) hj
  have hB := raw_B (U := U) (n0 := n0) (cut := cut) hτ hd m1 m2 (i := i) hj
  have hNd := MachineM.two_le_Nd d
  have e := nd_eq d
  set s := rawVal U n0 cut τ (BG.gsite τ d m1 m2 i j) with hs
  change s.fW = decide (i = 0) at fW
  change s.fE = decide (i = MachineM.Nd d - 1) at fE
  change s.fS = decide (j = 0) at fS
  change s.fN = decide (j = MachineM.Nd d - 1) at fN
  change s.lW = _ at hlW
  change s.lE = _ at hlE
  change s.lS = _ at hlS
  change s.lN = _ at hlN
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlW, fW]; by_cases h : i = 0 <;> simp [h]
  · rw [hlE, fE]; by_cases h : i + 1 < MachineM.Nd d
    · simp [h]; omega
    · simp [h]; omega
  · rw [hlS, fS]; by_cases h : j = 0 <;> simp [h]
  · rw [hlN, fN]; by_cases h : j + 1 < MachineM.Nd d
    · simp [h]; omega
    · simp [h]; omega
  · intro h
    rw [fS, decide_eq_true_iff] at h
    simp only [recF]
    rw [ite_eq_left h]
  · intro h
    rw [fS, decide_eq_false_iff_not] at h
    refine ⟨sAt U n0 cut τ d m2 i (j - 1), by simp only [recF]; rw [ite_eq_right h], ?_⟩
    rw [hlS, ite_eq_right h]
    simp only [vcolF, recF, Nat.sub_add_cancel (Nat.pos_of_ne_zero h)]
  · intro h
    rw [fN, decide_eq_true_iff] at h
    simp only [recF]
    rw [ite_eq_right (by omega)]
  · intro h
    rw [fN, decide_eq_false_iff_not] at h
    refine ⟨sAt U n0 cut τ d m2 i (j + 1), by simp only [recF]; rw [ite_eq_left (by omega)], ?_⟩
    rw [hlN, ite_eq_left (by omega)]
    rfl
  · intro h
    rw [fW, decide_eq_true_iff] at h
    show sAt U n0 cut τ d m2 i j = MachineP.initP U n0 s.q.H s.q.parent.1.a.1.b2 s.fS
    rw [hH, hB, fS, h, sAt_zero hj]
  · intro h
    rw [fW, decide_eq_false_iff_not] at h
    rw [hlW, ite_eq_right h]
    simp only [hcolF, recF, Nat.sub_add_cancel (Nat.pos_of_ne_zero h)]
  · intro h
    rw [fE, decide_eq_false_iff_not] at h
    rw [hlE, ite_eq_left (by omega)]
    simp only [hcolF, recF]
    rw [sAt_succ hj]
    rfl
  · show MachineP.CarriesHalt U n0 (sAt U n0 cut τ d m2 i j) = false
    rw [sAt_of hj]
    exact board_run_no_halt hn hn0 hU (row τ) hcut hd m2 i ⟨j, hj⟩
  · show (sAt U n0 cut τ d m2 i j).1.hin = s.q.H
    rw [hH, sAt_of hj]
    exact (MachineP.runP_tracks (by omega) _ _ i ⟨j, hj⟩).1
  · show (sAt U n0 cut τ d m2 i j).1.pi = s.q.parent.1.a.1.b2
    rw [hB, sAt_of hj]
    exact (MachineP.runP_tracks (by omega) _ _ i ⟨j, hj⟩).2

end Rules

section Legal

variable {U : Machine} {n0 k cut : ℕ} {τ : ℕ → Bool × Bool}

theorem raw_K3 (hτ : Typical τ) (hN : NHalt U n0 cut) (ξ : Plane) :
    (rawVal U n0 cut τ ξ).K3 (contentP U n0) := by
  have ha1 : FrameOffsets (BG.a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (BG.a2 τ) := frameOffsets_phase _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine kFm_none ?_
    rintro ⟨⟨d, i, j, m⟩, hd, hi, hj, m1, rfl⟩
    exact h ((BG.cfg_active (U := U) hτ (fun _ => Spin.plus) _).2
      ⟨d, m1, m, hd, BG.zeta_free ha1 hd m1 hi, BG.zeta_free ha2 hd m hj⟩)
  · obtain ⟨d, m1, m2, hd, h1, h2⟩ := (BG.cfg_active (U := U) hτ (fun _ => Spin.plus) _).1 h
    obtain ⟨i, j, hi, hj, rfl⟩ := (BG.mem_grid_iff hd).1 ⟨h1, h2⟩
    obtain ⟨hC0, hT⟩ := raw_rules hτ hd m1 m2 hi hj hN
    exact ⟨_, _, _, kFm_gsite hd m1 m2 hi hj, hC0, hT⟩

/-- The tuple tests of Section 3.3 hold at every site. -/
theorem raw_allowed (hτ : Typical τ) (hN : NHalt U n0 cut) (ξ : Plane) :
    (rawVal U n0 cut τ ξ).Allowed (contentP U n0) :=
  ⟨raw_O1 hτ ξ, raw_O2 hτ ξ, raw_E1 ξ, raw_E2 hτ ξ, raw_E3 hτ ξ, raw_K1 hτ ξ, raw_K2 hτ ξ,
    raw_K3 hτ hN ξ⟩

/-- Every site value is a tile of `R` (the tests and the central word). -/
theorem raw_tileOK (hτ : Typical τ) (hN : NHalt U n0 cut) (ξ : Plane) :
    TileOK (contentP U n0) k (rawOf U n0 k cut τ ξ) := by
  refine ⟨raw_allowed hτ hN ξ, ?_⟩
  show qtilingOf τ (ξ + (0, 0)) = qtilingOf τ ξ
  rw [Prod.mk_zero_zero, add_zero]

theorem raw_matchE (hτ : Typical τ) (ξ : Plane) :
    RVal.MatchE (rawVal U n0 cut τ ξ) (rawVal U n0 cut τ (ξ + (1, 0))) := by
  have hq : (dqOf cut τ ξ).colE = (dqOf cut τ (ξ + (1, 0))).colW :=
    (dqOf_spec hτ cut).1.1 ξ trivial trivial
  obtain ⟨z, y⟩ := ξ
  simp only [Prod.mk_add_mk, add_zero] at hq ⊢
  simp only [RVal.MatchE, RVal.cE, RVal.cW, rawVal, add_sub_cancel_right, hq]

theorem raw_matchN (hτ : Typical τ) (ξ : Plane) :
    RVal.MatchN (rawVal U n0 cut τ ξ) (rawVal U n0 cut τ (ξ + (0, 1))) := by
  have hq : (dqOf cut τ ξ).colN = (dqOf cut τ (ξ + (0, 1))).colS :=
    (dqOf_spec hτ cut).1.2 ξ trivial trivial
  obtain ⟨z, y⟩ := ξ
  simp only [Prod.mk_add_mk, add_zero] at hq ⊢
  simp only [RVal.MatchN, RVal.cN, RVal.cS, rawVal, add_sub_cancel_right, hq]

theorem raw_tileE (hτ : Typical τ) (a b : RTile (contentP U n0) k) (ξ : Plane)
    (ha : a.1 = rawOf U n0 k cut τ ξ) (hb : b.1 = rawOf U n0 k cut τ (ξ + (1, 0))) :
    TileE (contentP U n0) k a b := by
  have hP := (qtilingOf_spec hτ.1).2
  refine ⟨?_, fun x y hxy => ?_, ?_⟩
  · rw [ha, hb]; exact raw_matchE hτ ξ
  · rw [ha, hb]
    show qtilingOf τ (ξ + x.1) = qtilingOf τ (ξ + (1, 0) + y.1)
    rw [hxy]
    congr 1
    abel
  · rw [ha, hb]; exact phaseTable_wordAt_add_e1 hP k ξ

theorem raw_tileN (hτ : Typical τ) (a b : RTile (contentP U n0) k) (ξ : Plane)
    (ha : a.1 = rawOf U n0 k cut τ ξ) (hb : b.1 = rawOf U n0 k cut τ (ξ + (0, 1))) :
    TileN (contentP U n0) k a b := by
  have hP := (qtilingOf_spec hτ.1).2
  refine ⟨?_, fun x y hxy => ?_, ?_⟩
  · rw [ha, hb]; exact raw_matchN hτ ξ
  · rw [ha, hb]
    show qtilingOf τ (ξ + x.1) = qtilingOf τ (ξ + (0, 1) + y.1)
    rw [hxy]
    congr 1
    abel
  · rw [ha, hb]; exact phaseTable_wordAt_add_e2 hP k ξ

end Legal

/-! ## The chart -/

section Chart

variable (U : Machine) (n0 k cut : ℕ) (τ : ℕ → Bool × Bool)

open Classical in
/-- Tile data as a tile of `R` (the fallback `t₀` if the tests fail). -/
def toTile (t0 : RTile (contentP U n0) k) (v : RVal (MachineP.Cell U n0) × Word (winRad k)) :
    RTile (contentP U n0) k :=
  if h : TileOK (contentP U n0) k v then ⟨v, h⟩ else t0

/-- **The computational chart of phase `τ`** (Prop 4.3, nonhalting): the tile `rawOf` at every
site (the fallback `t₀` is never used when `τ` is typical and `NHalt` holds, `chartOf_val`). -/
def chartOf (t0 : RTile (contentP U n0) k) (ξ : Plane) : RTile (contentP U n0) k :=
  toTile U n0 k t0 (rawOf U n0 k cut τ ξ)

variable {U n0 k cut τ}

theorem chartOf_val (hτ : Typical τ) (hN : NHalt U n0 cut) (t0 : RTile (contentP U n0) k)
    (ξ : Plane) : (chartOf U n0 k cut τ t0 ξ).1 = rawOf U n0 k cut τ ξ := by
  rw [chartOf, toTile, dite_eq_left (raw_tileOK hτ hN ξ)]

/-- **Prop 4.3, nonhalting, one typical phase**: the chart is a legal `R`-chart. -/
theorem chartOf_isRChart (hτ : Typical τ) (hN : NHalt U n0 cut) (t0 : RTile (contentP U n0) k) :
    IsRChart (contentP U n0) k (chartOf U n0 k cut τ t0) :=
  ⟨fun ξ _ _ => raw_tileE hτ _ _ ξ (chartOf_val hτ hN t0 ξ) (chartOf_val hτ hN t0 _),
    fun ξ _ _ => raw_tileN hτ _ _ ξ (chartOf_val hτ hN t0 ξ) (chartOf_val hτ hN t0 _)⟩

/-- Its quarters are `Y_τ`. -/
theorem chartOf_quarters (hτ : Typical τ) (hN : NHalt U n0 cut) (t0 : RTile (contentP U n0) k) :
    (fun ξ => (chartOf U n0 k cut τ t0 ξ).1.1.q.toQ) = qtilingOf τ := by
  funext ξ
  rw [chartOf_val hτ hN t0 ξ]
  rfl

/-- Its quarter phase is `τ`. -/
theorem chartOf_phase (hτ : Typical τ) (hN : NHalt U n0 cut) (t0 : RTile (contentP U n0) k) :
    IsQPhase (fun ξ => (chartOf U n0 k cut τ t0 ξ).1.1.q.toQ) τ := by
  rw [chartOf_quarters hτ hN t0]
  exact (qtilingOf_spec hτ.1).2

/-- Its column bits are the cutoff `V = [rank < cut]`. -/
theorem chartOf_V (hτ : Typical τ) (hN : NHalt U n0 cut) (t0 : RTile (contentP U n0) k)
    (ξ : Plane) : (chartOf U n0 k cut τ t0 ξ).1.1.q.V = decide (prankOf (col τ) ξ.1 < cut) := by
  rw [chartOf_val hτ hN t0 ξ]
  exact (dqOf_spec hτ cut).2.1 ξ

/-- Its row bits are the cutoff `H_row = [rank < cut]`. -/
theorem chartOf_H (hτ : Typical τ) (hN : NHalt U n0 cut) (t0 : RTile (contentP U n0) k)
    (ξ : Plane) : (chartOf U n0 k cut τ t0 ξ).1.1.q.H = decide (prankOf (row τ) ξ.2 < cut) := by
  rw [chartOf_val hτ hN t0 ξ]
  exact (dqOf_spec hτ cut).2.2 ξ

/-- The row flags of Prop 4.3: `H_row = 1` on the bottom rows of depths `1 ≤ d < a` and `0` on
depths `d ≥ a` (`a = n + n₀`; bottom rows have parent rank `2d - 1`). -/
theorem chartOf_bottom_flag (hτ : Typical τ) (t0 : RTile (contentP U n0) k) {n : ℕ}
    (hn : 1 ≤ n) (hn0 : 1 ≤ n0) (hU : ¬ U.HaltsOn n)
    (hcut : cut = 2 * (n + n0) - 2 ∨ cut = 2 * (n + n0) - 1) {d : ℕ} (hd : 1 ≤ d) (m x : ℤ) :
    (chartOf U n0 k cut τ t0 (x, frameLo (phaseOffsets (row τ)) d m)).1.1.q.H =
      decide (d < n + n0) := by
  rw [chartOf_H hτ ⟨n, hn, hn0, hU, hcut⟩ t0, prankOf_eq (prank_frameLo (row τ) hd m)]
  refine decide_eq_decide.2 ?_
  omega

end Chart

end UND.Chart
