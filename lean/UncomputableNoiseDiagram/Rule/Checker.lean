/-
# Section 2.1: the planar checker and the provider threshold (R1, R2)

Nodes R1, R2 of `BLUEPRINT.md` (Part A.2). ADAPTED from the forgetting core's checker
(`FNE.Compatible`, `FNE.CheckerKeeps`, `FNE.checker`, `FNE.quorumRule`, `FNE.quorum_unique`;
`FixedNoiseErgodicity/Statements.lean`, `Basic.lean`, `Section2/PCA.lean`), generalized (D4) from
ℕ-coloured Wang tiles to a finite tile type with horizontal and vertical matching relations
(`WangRel`), since the routing alphabet `R` (A.3, S7) is a finite set of tuples defined later, and
from the quorum over `k + 1` unit providers to the threshold `h` over the `q` providers of five
clusters.

Paper (Section 2.1): "For a finite Wang set `R`, let `𝓛_R` consist of pairs `(c, b)`, where `c`
is an edge-matching `R`-pattern on `Mo` and `b ∈ {0,1}`. … Two letters at displacement
`ζ ∈ Mo \ {0}` are compatible when their `R`-blocks agree on the overlap after translation by `ζ`
and their bits agree. Put `𝒜_R = {⊥} ∪ 𝓛_R`. … A full legal chart means an assignment of live
letters compatible in all eight Moore directions. … For a data configuration `D₀`, check each
provider `(u, P + s)` by retaining its central live letter exactly when its eight Moore neighbours
are live and compatible with that centre at their respective displacements. A failed check
returns `⊥`. Define `F_R(D₀)(u, P)` as a live letter occurring in at least `h` checked providers,
and `⊥` if none does. Since `2h > q`, that letter is unique. A legal chart cloned over `P` is fixed
by `F_R`."

* sites `(u, P) ∈ ℤ² × ℤ⁴` are `ISite = FNE.Site 4` (D5; the identification with `Fin 6 → ℤ` is
  made in `Rule/CA.lean`); `Mo = FNE.box 1`, `Mo \ {0} = FNE.mooreDirs`, cells `FNE.Cell` (REUSE);
* the providers `s ∈ S = ⋃ᵢ Sᵢ`, `Sᵢ = Cᵢ + {0,…,15}⁴`, are indexed by `Prov = Option (Fin 4) ×
  (Fin 4 → Fin 16)` (cluster, block offset), `|Prov| = q` (`card_Prov`); the offsets
  `provOff π = C_c + o` have coordinates in `[0, 175]`;
* `FR` (the checker `F_R`), `quorum_unique` (`2h > q`), `FR_eq_some_iff`, `FR_eq_none_iff`,
  **`FR_cloned`** (a cloned full legal chart is fixed), `FR_translate` (translation
  commutation), `FR_local` (locality on `Mo × S`), and for the iterates `F_R^n`:
  `FR_iter_translate`, **`FR_iter_local`** (locality on `[-n, n]² × [0, 175 n]⁴`).
-/
import UncomputableNoiseDiagram.Statements
import UncomputableNoiseDiagram.Parameters.Geometry
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Rule

open FNE (Plane box Cell mooreDirs)

/-! ## R1: chart letters -/

/-- D4: a tile set given by matching relations: `E a b` (`b` may sit east of `a`) and `N a b`
(`b` may sit north of `a`). For a Wang set these are the edge-colour equalities. -/
structure WangRel (τ : Type*) where
  /-- horizontal matching: `b` east of `a` -/
  E : τ → τ → Prop
  /-- vertical matching: `b` north of `a` -/
  N : τ → τ → Prop

variable {τ : Type*} [Fintype τ] [DecidableEq τ] (R : WangRel τ)

/-- An edge-matching `R`-pattern on `Mo = {-1,0,1}²`. -/
def IsLegalBlock (β : Cell → τ) : Prop :=
  (∀ w w' : Cell, w'.1 = w.1 + (1, 0) → R.E (β w) (β w')) ∧
  (∀ w w' : Cell, w'.1 = w.1 + (0, 1) → R.N (β w) (β w'))

/-- The legal `3 × 3` blocks. -/
abbrev LegalBlock := {β : Cell → τ // IsLegalBlock R β}

noncomputable instance : Fintype (LegalBlock R) := Fintype.ofFinite _

/-- `𝓛_R`: a live letter `(c, b)`, a legal block and a bit. -/
abbrev LiveLetter := LegalBlock R × Bool

/-- `𝒜_R = {⊥} ∪ 𝓛_R`; `none` is `⊥`. -/
abbrev ChartSym := Option (LiveLetter R)

/-- The central tile of a live letter (read by the controller). -/
def ctr (s : LiveLetter R) : τ := s.1.1 FNE.Cell.zero

/-- Two live letters at displacement `ζ` are compatible: their bits agree and their blocks agree on
the overlap after translation by `ζ`. -/
def Compatible (s s' : LiveLetter R) (d : Plane) : Prop :=
  s.2 = s'.2 ∧ ∀ w w' : Cell, w'.1 = w.1 - d → s.1.1 w = s'.1.1 w'

/-- A full legal chart: live letters compatible in all eight Moore directions. -/
def IsFullChart (c : Plane → LiveLetter R) : Prop :=
  ∀ u, ∀ d ∈ mooreDirs, Compatible R (c u) (c (u + d)) d

/-- The check of a planar data configuration at `u` passes: the centre is live and its eight Moore
neighbours are live and compatible with it at their displacements. -/
def Keeps (x : Plane → ChartSym R) (u : Plane) : Prop :=
  ∃ s, x u = some s ∧ ∀ d ∈ mooreDirs, ∃ s', x (u + d) = some s' ∧ Compatible R s s' d

open Classical in
/-- The checked value: the central live letter if the check passes, `⊥` otherwise. -/
def chk (x : Plane → ChartSym R) (u : Plane) : ChartSym R := if Keeps R x u then x u else none

/-! ## R2: the provider threshold -/

/-- Sites `(u, P) ∈ ℤ² × ℤ⁴` (D5). -/
abbrev ISite := FNE.Site 4

/-- The providers: a cluster (`none` is `S₀`, `some i` is `S_{i+1}`) and a block offset in
`{0, …, 15}⁴`. -/
abbrev Prov := Option (Fin 4) × (Fin 4 → Fin 16)

/-- The provider vector `C_c + o`. -/
def provOff (π : Prov) : Fin 4 → ℤ := UND.Param.clusterOffset π.1 + fun j => ((π.2 j : ℕ) : ℤ)

/-- There are `q = 5·16⁴` providers. -/
theorem card_Prov : Fintype.card Prov = UND.Param.q := by
  simp [Fintype.card_prod, Fintype.card_option, UND.Param.q, UND.Param.K]

/-- Provider coordinates lie in `[0, L + m - 1] = [0, 175]`. -/
theorem provOff_mem (π : Prov) (j : Fin 4) : 0 ≤ provOff π j ∧ provOff π j ≤ 175 := by
  have ho : ((π.2 j : ℕ) : ℤ) ≤ 15 := by have := (π.2 j).2; omega
  have ho0 : (0 : ℤ) ≤ ((π.2 j : ℕ) : ℤ) := Int.natCast_nonneg _
  simp only [provOff, Pi.add_apply]
  rcases π with ⟨c, o⟩
  cases c with
  | none => simp only [UND.Param.clusterOffset, Pi.zero_apply]; omega
  | some i =>
    simp only [UND.Param.clusterOffset]
    split_ifs <;> omega

/-- The number of checked providers of `w = (u, P)` that read the live letter `s`. -/
def quorumCount (D : ISite → ChartSym R) (w : ISite) (s : LiveLetter R) : ℕ :=
  (Finset.univ.filter
    (fun π : Prov => chk R (fun u => D (u, w.2 + provOff π)) w.1 = some s)).card

open Classical in
/-- The threshold decision: a live letter with at least `h` votes, `⊥` if none. -/
def quorumPick (f : LiveLetter R → ℕ) : ChartSym R :=
  if hex : ∃ s, UND.Param.h ≤ f s then some hex.choose else none

/-- **The checker `F_R`**: `F_R(D₀)(u, P)` is a live letter occurring in at least `h` checked
providers, and `⊥` if none does. -/
def FR (D : ISite → ChartSym R) : ISite → ChartSym R := fun w => quorumPick R (quorumCount R D w)

/-- **Uniqueness of the quorum letter** (`2h > q`). -/
theorem quorum_unique (D : ISite → ChartSym R) (w : ISite) {s s' : LiveLetter R}
    (hs : UND.Param.h ≤ quorumCount R D w s) (hs' : UND.Param.h ≤ quorumCount R D w s') :
    s = s' := by
  classical
  by_contra hne
  have hdisj : Disjoint
      (Finset.univ.filter
        (fun π : Prov => chk R (fun u => D (u, w.2 + provOff π)) w.1 = some s))
      (Finset.univ.filter
        (fun π : Prov => chk R (fun u => D (u, w.2 + provOff π)) w.1 = some s')) := by
    rw [Finset.disjoint_filter]
    intro π _ h1 h2
    exact hne (Option.some_injective _ (h1.symm.trans h2))
  have hcard := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_univ
    ((Finset.univ.filter
        (fun π : Prov => chk R (fun u => D (u, w.2 + provOff π)) w.1 = some s)) ∪
      (Finset.univ.filter
        (fun π : Prov => chk R (fun u => D (u, w.2 + provOff π)) w.1 = some s')))
  rw [card_Prov] at hle
  unfold quorumCount at hs hs'
  have := UND.Param.q_lt_two_h
  omega

theorem quorumPick_eq_some_iff {f : LiveLetter R → ℕ}
    (huniq : ∀ s s', UND.Param.h ≤ f s → UND.Param.h ≤ f s' → s = s') (s : LiveLetter R) :
    quorumPick R f = some s ↔ UND.Param.h ≤ f s := by
  unfold quorumPick
  constructor
  · intro h
    split_ifs at h with hex
    · cases h
      exact hex.choose_spec
  · intro h
    have hex : ∃ s, UND.Param.h ≤ f s := ⟨s, h⟩
    rw [dite_eq_left hex]
    rw [huniq _ _ hex.choose_spec h]

theorem quorumPick_eq_none_iff (f : LiveLetter R → ℕ) :
    quorumPick R f = none ↔ ∀ s, f s < UND.Param.h := by
  unfold quorumPick
  constructor
  · intro h s
    by_contra hs
    have hex : ∃ s, UND.Param.h ≤ f s := ⟨s, by omega⟩
    rw [dite_eq_left hex] at h
    cases h
  · intro h
    have hex : ¬ ∃ s, UND.Param.h ≤ f s := fun ⟨s, hs⟩ => by have := h s; omega
    rw [dite_eq_right hex]

/-- `F_R(D)(w) = s` (live) exactly when at least `h` checked providers read `s`. -/
theorem FR_eq_some_iff (D : ISite → ChartSym R) (w : ISite) (s : LiveLetter R) :
    FR R D w = some s ↔ UND.Param.h ≤ quorumCount R D w s :=
  quorumPick_eq_some_iff R (fun _ _ h1 h2 => quorum_unique R D w h1 h2) s

/-- `F_R(D)(w) = ⊥` exactly when no live letter has `h` votes. -/
theorem FR_eq_none_iff (D : ISite → ChartSym R) (w : ISite) :
    FR R D w = none ↔ ∀ s, quorumCount R D w s < UND.Param.h :=
  quorumPick_eq_none_iff R _

/-- A full legal chart passes every check. -/
theorem chk_chart {c : Plane → LiveLetter R} (hc : IsFullChart R c) (u : Plane) :
    chk R (fun u => some (c u)) u = some (c u) := by
  classical
  have hk : Keeps R (fun u => some (c u)) u :=
    ⟨c u, rfl, fun d hd => ⟨c (u + d), rfl, hc u d hd⟩⟩
  simp only [chk, hk, ↓reduceIte]

/-- **A legal chart cloned over `P` is fixed by `F_R`.** -/
theorem FR_cloned {c : Plane → LiveLetter R} (hc : IsFullChart R c) :
    FR R (fun w => some (c w.1)) = fun w => some (c w.1) := by
  funext w
  rw [FR_eq_some_iff]
  have : quorumCount R (fun w => some (c w.1)) w (c w.1) = UND.Param.q := by
    unfold quorumCount
    rw [Finset.filter_true_of_mem (fun π _ => chk_chart R hc w.1), Finset.card_univ, card_Prov]
  rw [this]
  have := UND.Param.q_lt_two_h
  simp only [UND.Param.q, UND.Param.h] at this ⊢
  omega

/-! ## Translations and locality -/

/-- The check commutes with planar translations. -/
theorem chk_translate (y : Plane → ChartSym R) (a u : Plane) :
    chk R (fun u' => y (u' + a)) u = chk R y (u + a) := by
  classical
  have e : ∀ d : Plane, u + d + a = u + a + d := fun d => add_right_comm u d a
  have hk : Keeps R (fun u' => y (u' + a)) u ↔ Keeps R y (u + a) := by
    unfold Keeps
    constructor
    · rintro ⟨s, hs, hall⟩
      refine ⟨s, hs, fun d hd => ?_⟩
      obtain ⟨s', h1, h2⟩ := hall d hd
      exact ⟨s', by rw [← e]; exact h1, h2⟩
    · rintro ⟨s, hs, hall⟩
      refine ⟨s, hs, fun d hd => ?_⟩
      obtain ⟨s', h1, h2⟩ := hall d hd
      exact ⟨s', by show y (u + d + a) = _; rw [e]; exact h1, h2⟩
  unfold chk
  by_cases h : Keeps R y (u + a)
  · simp only [hk.mpr h, h, ↓reduceIte]
  · simp only [show ¬ Keeps R (fun u' => y (u' + a)) u from fun h' => h (hk.mp h'), h,
      ↓reduceIte]

theorem quorumCount_translate (D : ISite → ChartSym R) (a w : ISite) :
    quorumCount R (fun w' => D (w' + a)) w = quorumCount R D (w + a) := by
  funext s
  unfold quorumCount
  congr 1
  refine Finset.filter_congr (fun π _ => ?_)
  have := chk_translate R (fun u => D (u, w.2 + a.2 + provOff π)) a.1 w.1
  have e : ∀ u : Plane, ((u, w.2 + provOff π) + a : ISite) = (u + a.1, w.2 + a.2 + provOff π) :=
    fun u => Prod.ext rfl (add_right_comm _ _ _)
  simp only [e]
  rw [this]
  rfl

/-- `F_R` commutes with every translation of `ℤ² × ℤ⁴`. -/
theorem FR_translate (D : ISite → ChartSym R) (a : ISite) :
    FR R (fun w => D (w + a)) = fun w => FR R D (w + a) := by
  funext w
  unfold FR
  rw [quorumCount_translate]

theorem FR_iter_translate (n : ℕ) (D : ISite → ChartSym R) (a : ISite) :
    (FR R)^[n] (fun w => D (w + a)) = fun w => (FR R)^[n] D (w + a) := by
  induction n generalizing D with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, FR_translate, ih]

/-- The check at `u` reads only `u + Mo`. -/
theorem chk_congr {x y : Plane → ChartSym R} {u : Plane}
    (h : ∀ d ∈ box 1, x (u + d) = y (u + d)) : chk R x u = chk R y u := by
  classical
  have h0 : x u = y u := by simpa using h 0 (by decide)
  have hm : ∀ d ∈ mooreDirs, x (u + d) = y (u + d) :=
    fun d hd => h d (Finset.mem_of_mem_erase hd)
  have hk : Keeps R x u ↔ Keeps R y u := by
    unfold Keeps
    constructor
    · rintro ⟨s, hs, hall⟩
      exact ⟨s, h0 ▸ hs, fun d hd => by rw [← hm d hd]; exact hall d hd⟩
    · rintro ⟨s, hs, hall⟩
      exact ⟨s, h0.symm ▸ hs, fun d hd => by rw [hm d hd]; exact hall d hd⟩
  unfold chk
  by_cases hx : Keeps R x u
  · simp only [hx, hk.mp hx, ↓reduceIte, h0]
  · simp only [hx, show ¬ Keeps R y u from fun h' => hx (hk.mpr h'), ↓reduceIte]

/-- **Locality of `F_R`**: `F_R(D)(u, P)` reads only `D` on `(u + Mo) × (P + S)`. -/
theorem FR_local {D D' : ISite → ChartSym R} {w : ISite}
    (h : ∀ d ∈ box 1, ∀ π : Prov, D (w.1 + d, w.2 + provOff π) = D' (w.1 + d, w.2 + provOff π)) :
    FR R D w = FR R D' w := by
  unfold FR
  congr 1
  funext s
  unfold quorumCount
  congr 1
  exact Finset.filter_congr (fun π _ => by
    rw [chk_congr R (x := fun u => D (u, w.2 + provOff π)) (y := fun u => D' (u, w.2 + provOff π))
      (fun d hd => h d hd π)])

/-- The cube `[0, c]⁴` of provider-coordinate offsets. -/
def InCube (c : ℤ) (o : Fin 4 → ℤ) : Prop := ∀ j, 0 ≤ o j ∧ o j ≤ c

theorem mem_box_add {n : ℕ} {d d' : Plane} (hd : d ∈ box 1) (hd' : d' ∈ box n) :
    d + d' ∈ box (n + 1) := by
  simp only [box, Finset.mem_product, Finset.mem_Icc] at hd hd' ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hd
  obtain ⟨⟨h5, h6⟩, h7, h8⟩ := hd'
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast at *
  omega

/-- **Locality of the iterates**: `F_R^n(D)(u, P)` reads only `D` on
`(u + [-n, n]²) × (P + [0, 175 n]⁴)`. -/
theorem FR_iter_local (n : ℕ) {D D' : ISite → ChartSym R} {w : ISite}
    (h : ∀ d ∈ box n, ∀ o, InCube (175 * n) o → D (w.1 + d, w.2 + o) = D' (w.1 + d, w.2 + o)) :
    (FR R)^[n] D w = (FR R)^[n] D' w := by
  induction n generalizing w with
  | zero =>
    have := h 0 (by decide) 0 (fun j => by simp)
    simpa using this
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine FR_local R (fun d hd π => ?_)
    refine ih (w := (w.1 + d, w.2 + provOff π)) (fun d' hd' o ho => ?_)
    have e1 : w.1 + d + d' = w.1 + (d + d') := add_assoc _ _ _
    have e2 : w.2 + provOff π + o = w.2 + (provOff π + o) := add_assoc _ _ _
    simp only [e1, e2]
    refine h _ (mem_box_add hd hd') _ (fun j => ?_)
    have := provOff_mem π j
    have := ho j
    simp only [Pi.add_apply]
    push_cast
    constructor <;> linarith [this.1, this.2]

end UND.Rule
