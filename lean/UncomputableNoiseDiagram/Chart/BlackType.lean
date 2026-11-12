/-
# Section 3.1: the black-type rank comparison, and the cutoff lemma (Lemma 3.2), abstract part

The paragraph after Prop 3.1: "At a finite-rank row/column intersection the black type is `A` for
equal ranks, `B` or `C` if the column rank is smaller, and `D` or `E` if it is larger. Indeed, the
substitution table makes child `(0,0)` keep the black type, child `(1,1)` have black `A`, child
`(1,0)` have black in `{B, C}` and child `(0,1)` in `{D, E}`. The letter descends through children
`(0,0)` from its ancestor at the first nonzero digit pair of the parent coordinate `u - ϖ`."

Proved on the hard-model core's towers (`UPD.Scaffold.TowerRel`, ranks `UPD.Scaffold.IsRank`,
children `UPD.Scaffold.Letter.child`), in the same style as its `app:rank-bits`
(`UPD.Scaffold.rank_bits_col`):
* `chain_black`: along a chain of children `(0,0)` the black type is kept;
* **`black_rank_compare`**: the printed comparison, for every tower of sufficient height (no
  typicality: only the finiteness of the smaller rank is used);
* `exists_rank`: every rank occurs in every phase (for every digit sequence);
* **`cutoff_of_filter`** (Lemma 3.2, first sentence, abstract form): if column and row bits obey
  the comparisons of (8) at every pair of finite ranks, and every rank occurs on both axes, then
  they are given by one common nonincreasing sequence `(b_r)`.
-/
import UndecidablePhaseDiagram.Scaffold.Tower

set_option autoImplicit false

namespace UND.Chart

open UPD UPD.Scaffold

/-- Child `(0,0)` keeps the black type. -/
theorem black_child_ff (x : Letter) : (x.child false false).base.black = x.base.black := rfl

/-- Child `(1,1)` has black type `A`. -/
theorem black_child_tt (x : Letter) : (x.child true true).base.black = .A := rfl

/-- Child `(1,0)` has black type in `{B, C}`. -/
theorem black_child_tf (x : Letter) :
    (x.child true false).base.black = .B ∨ (x.child true false).base.black = .C :=
  (se_spec x.base.black).1

/-- Child `(0,1)` has black type in `{D, E}`. -/
theorem black_child_ft (x : Letter) :
    (x.child false true).base.black = .D ∨ (x.child false true).base.black = .E :=
  (nw_spec x.base.black).1

/-- Along a chain `P_m = φ'(P_{m+1})(ς_m)` whose digit pairs vanish below `r`, the black type of
`P_0` is that of `P_r`. -/
theorem chain_black (r : ℕ) (P : ℕ → Letter) (s1 s2 : ℕ → Bool)
    (hP : ∀ m < r, P m = (P (m + 1)).child (s1 m) (s2 m))
    (h0 : ∀ m < r, s1 m = false ∧ s2 m = false) :
    (P 0).base.black = (P r).base.black := by
  induction r generalizing P s1 s2 with
  | zero => rfl
  | succ r ih =>
    have h := ih (fun m => P (m + 1)) (fun m => s1 (m + 1)) (fun m => s2 (m + 1))
      (fun m hm => hP (m + 1) (by omega)) (fun m hm => h0 (m + 1) (by omega))
    rw [hP 0 (Nat.succ_pos r), (h0 0 (Nat.succ_pos r)).1, (h0 0 (Nat.succ_pos r)).2,
      black_child_ff]
    exact h

/-- **The black-type rank comparison** (Section 3.1, after Prop 3.1). In a tower of height `h`,
at a site `x` whose column has rank `r` and whose row has rank `s` (parent ranks), with
`min r s < h`: the black type of `f_0(x)` is `A` if `r = s`, `B` or `C` if `r < s` (the column rank
is smaller), and `D` or `E` if `r > s`. -/
theorem black_rank_compare {υ : ℕ → Bool × Bool} {f : ℕ → Plane → Letter} {h r s : ℕ}
    (hf : TowerRel υ f h) {x : Plane} (hx : IsRank (col υ) x.1 r) (hy : IsRank (row υ) x.2 s)
    (hh : min r s < h) :
    (r = s → (f 0 x).base.black = .A) ∧
      (r < s → (f 0 x).base.black = .B ∨ (f 0 x).base.black = .C) ∧
      (s < r → (f 0 x).base.black = .D ∨ (f 0 x).base.black = .E) := by
  set P : ℕ → Letter := fun m => f m (ancP υ m x) with hPdef
  set s1 : ℕ → Bool := fun m => dig (col υ) m x.1
  set s2 : ℕ → Bool := fun m => dig (row υ) m x.2
  have hP : ∀ m < h, P m = (P (m + 1)).child (s1 m) (s2 m) := fun m hm => hf.chain hm x
  have hP0 : f 0 x = P 0 := by
    simp only [hPdef, ancP, anc]
  -- the black type at the first nonzero digit pair `t = min r s`
  have hfirst : ∀ t, t ≤ r → t ≤ s → t < h →
      (P 0).base.black = ((P (t + 1)).child (s1 t) (s2 t)).base.black := by
    intro t htr hts hth
    rw [chain_black t P s1 s2 (fun m hm => hP m (by omega))
      (fun m hm => ⟨hx.2 m (by omega), hy.2 m (by omega)⟩), hP t hth]
  rw [hP0]
  refine ⟨fun hrs => ?_, fun hrs => ?_, fun hrs => ?_⟩
  · subst hrs
    rw [hfirst r le_rfl le_rfl (by omega)]
    have e1 : s1 r = true := hx.1
    have e2 : s2 r = true := hy.1
    rw [e1, e2]; exact black_child_tt _
  · rw [hfirst r le_rfl hrs.le (by omega)]
    have e1 : s1 r = true := hx.1
    have e2 : s2 r = false := hy.2 r hrs
    rw [e1, e2]; exact black_child_tf _
  · rw [hfirst s hrs.le le_rfl (by omega)]
    have e1 : s1 s = false := hx.2 s hrs
    have e2 : s2 s = true := hy.1
    rw [e1, e2]; exact black_child_ft _

/-- Every rank occurs on every axis, in every phase: `z = (ϖ mod 2^{r+1}) + 2^r` has rank `r`. -/
theorem exists_rank (c : ℕ → Bool) (r : ℕ) : ∃ z : ℤ, IsRank c z r := by
  refine ⟨wsum c (r + 1) + 2 ^ r, isRank_of_emod le_rfl ?_⟩
  rw [add_sub_cancel_left]
  exact Int.emod_eq_of_lt (by positivity) (by rw [pow_succ]; have := pow_pos (two_pos (α := ℤ)) r; linarith)

/-- **Lemma 3.2, first sentence (abstract form).** Column bits `bc` and row bits `br`, indexed by
coordinates with finite ranks (`rkC z r`: column `z` has rank `r`; `rkR y s` likewise), obey the
rank filter (8) as forced by the black types: equal ranks give equal bits, a smaller column rank
gives `V ≥ H_row`, a larger one `V ≤ H_row`. If every rank occurs on both axes, the bits are given
by one common nonincreasing sequence `(b_r)`. -/
theorem cutoff_of_filter (rkC rkR : ℤ → ℕ → Prop) (bc br : ℤ → Bool)
    (hfilter : ∀ z y r s, rkC z r → rkR y s →
      (r = s → bc z = br y) ∧ (r < s → br y ≤ bc z) ∧ (s < r → bc z ≤ br y))
    (hexC : ∀ r, ∃ z, rkC z r) (hexR : ∀ s, ∃ y, rkR y s) :
    ∃ b : ℕ → Bool, Antitone b ∧ (∀ z r, rkC z r → bc z = b r) ∧
      (∀ y s, rkR y s → br y = b s) := by
  choose zc hzc using hexC
  choose yr hyr using hexR
  refine ⟨fun r => bc (zc r), ?_, ?_, ?_⟩
  · intro r s hrs
    rcases hrs.lt_or_eq with hlt | heq
    · -- `b_s = br (yr s) ≤ bc (zc r) = b_r`
      have h1 := ((hfilter (zc r) (yr s) r s (hzc r) (hyr s)).2.1 hlt)
      have h2 := (hfilter (zc s) (yr s) s s (hzc s) (hyr s)).1 rfl
      simp only
      rw [h2]; exact h1
    · subst heq; exact le_rfl
  · intro z r hz
    have h1 := (hfilter z (yr r) r r hz (hyr r)).1 rfl
    have h2 := (hfilter (zc r) (yr r) r r (hzc r) (hyr r)).1 rfl
    simp only; rw [h1, h2]
  · intro y s hy
    have h1 := (hfilter (zc s) y s s (hzc s) hy).1 rfl
    simp only; rw [h1]

end UND.Chart
