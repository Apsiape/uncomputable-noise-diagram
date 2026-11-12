/-
# Lemma 9.1: literal encoding bounds

Node Q4 of `BLUEPRINT.md` (Part A.9). Lemma 9.1 (`lem:counts`): "A connected embedded edge set
with `e` edges can be encoded by a deterministic traversal of its doubled edges, of length at most
`2e`, and a marked source subset. Its count is bounded by `Δ^{2e} 2^{e+1}`. Summing `e ≤ 256g`
gives `2 Σ_{e=0}^{256g} (2Δ²)^e ≤ 4(2Δ²)^{256g} ≤ K_mem^g`."

The traversal count is the forgetting core's `FNE.EdgeCount.card_le_pow` (REUSE). Here:

* `finite_connected`: in a graph of degree `≤ Δ` (`nbr : V → Finset V`), the connected `n`-edge
  sets at a vertex `z` form a finite set with at most `Δ^{2n}` elements (generic port of
  `FNE.finite_connected`);
* `vertsOf`, `vertsOf_spec`: at most `n + 1` vertices (generic port of `FNE.vertsOf`);
* **literal encodings** `IsEncoding nbr z N K A`: `K` has at most `N` edges of the graph and is
  connected at `z`, and `A` is a set of vertices of `K` (or `z`), the marked sources;
  `encLe nbr z N` is a finset containing every encoding (`mem_encLe`), with
  **`card_encLe_le`**: `|encLe N| ≤ 2 Σ_{e ≤ N} (2Δ²)^e ≤ 4 (2Δ²)^N`;
* the constants: **`card_encLe_Kmem`** (`≤ K_mem^g` for `N = 256 g`, `Δ ≤ Δ_paper`) and
  `card_encLe_KrareOf` (`≤ K_rare^g` for `N = 512 g`, `Δ ≤ Δ_rare`), from
  `four_mul_pow_le` (`4 X^{cg} ≤ (2²⁰ X^{c+1})^g`);
* the union bound over encodings, **`measure_le_tsum_groups`**: if every outcome of `Ev` has,
  for some `g ≥ 1`, an encoding with at most `c g` edges whose event has probability `≤ x^g`, and
  `4(2Δ²)^{cg} ≤ K^g`, then `μ(Ev) ≤ Σ_{g≥1} (K x)^g`; and its real form `measure_le_ofReal_tsum`;
* the hook to Lemma 5.1: `witness_card_le` (the copied-arm witness has at most `Σ pLen + |links|`
  edges), `pLen_le_two_pBin` (if no unary link is followed by another, an arm has at most twice
  as many edges as binary edges, Lemma 7.2's "two unary links per positive support edge" with the
  corridor merged into one link), `connectedAt_image` and `connectedAt_filter_not_diag`
  (projection keeps connectivity; collapsed group links are loops and may be dropped), and
  `witness_isEncoding`: a projected witness inside a graph of degree `≤ Δ` is an encoding.

Kernel discipline D13: the closed constants enter only through `four_le_Kmem_pow` and lemmas over
a variable `B`.
-/
import UncomputableNoiseDiagram.Contour.Grouped
import UncomputableNoiseDiagram.Parameters.Threshold
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped ENNReal
open MeasureTheory Relation

namespace UND.Counting

open FNE.EdgeCount

variable {V : Type*} [DecidableEq V]

/-! ## Connected edge sets in a graph of bounded degree -/

/-- Every edge of `K` joins neighbours of the graph `nbr`. -/
def InGraph (nbr : V → Finset V) (K : Finset (Sym2 V)) : Prop := ∀ a b, s(a, b) ∈ K → b ∈ nbr a

/-- The connected `n`-edge sets of the graph at `z`. -/
def ConnSet (nbr : V → Finset V) (z : V) (n : ℕ) : Set (Finset (Sym2 V)) :=
  {K | K.card = n ∧ InGraph nbr K ∧ ConnectedAt K z}

/-- In a graph of degree `≤ Δ`, the connected `n`-edge sets at `z` form a finite set with at most
`Δ^{2n}` elements (generic port of `FNE.finite_connected`). -/
theorem finite_connected (nbr : V → Finset V) (Δ : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ) (z : V)
    (n : ℕ) : (ConnSet nbr z n).Finite ∧ (ConnSet nbr z n).ncard ≤ Δ ^ (2 * n) := by
  have hfin : (ConnSet nbr z n).Finite := by
    by_contra hinf
    obtain ⟨S, hSA, hScard⟩ := Set.Infinite.exists_subset_card_eq hinf (Δ ^ (2 * n) + 1)
    have := card_le_pow nbr Δ hΔ z n S (fun K hK => hSA hK)
    omega
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact card_le_pow nbr Δ hΔ z n _ (fun K hK => (Set.Finite.mem_toFinset hfin).mp hK)

open Classical in
/-- The connected `n`-edge sets at `z`, as a finset (empty if the set were infinite). -/
def connSets (nbr : V → Finset V) (z : V) (n : ℕ) : Finset (Finset (Sym2 V)) :=
  if h : (ConnSet nbr z n).Finite then h.toFinset else ∅

theorem mem_connSets (nbr : V → Finset V) (Δ : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ) (z : V)
    {n : ℕ} {K : Finset (Sym2 V)} (hK : K ∈ ConnSet nbr z n) : K ∈ connSets nbr z n := by
  have hfin := (finite_connected nbr Δ hΔ z n).1
  rw [connSets, dite_eq_left hfin]
  exact (Set.Finite.mem_toFinset hfin).mpr hK

theorem connSets_spec {nbr : V → Finset V} {z : V} {n : ℕ} {K : Finset (Sym2 V)}
    (hK : K ∈ connSets nbr z n) : K ∈ ConnSet nbr z n := by
  unfold connSets at hK
  split_ifs at hK with hfin
  · exact (Set.Finite.mem_toFinset hfin).mp hK
  · simp at hK

theorem card_connSets_le (nbr : V → Finset V) (Δ : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ) (z : V)
    (n : ℕ) : (connSets nbr z n).card ≤ Δ ^ (2 * n) := by
  obtain ⟨hfin, hcard⟩ := finite_connected nbr Δ hΔ z n
  rw [connSets, dite_eq_left hfin, ← Set.ncard_eq_toFinset_card _ hfin]
  exact hcard

open Classical in
/-- A finite set of at most `|K| + 1` vertices containing `z` and both ends of every edge of `K`,
when `K` is connected at `z` (`FNE.EdgeCount.exists_vertices`); `∅` otherwise. -/
def vertsOf (z : V) (K : Finset (Sym2 V)) : Finset V :=
  if h : ConnectedAt K z then (exists_vertices h).choose else ∅

theorem vertsOf_spec {z : V} {K : Finset (Sym2 V)} (h : ConnectedAt K z) :
    (vertsOf z K).card ≤ K.card + 1 ∧ z ∈ vertsOf z K ∧ ∀ e ∈ K, ∀ v ∈ e, v ∈ vertsOf z K := by
  rw [vertsOf, dite_eq_left h]
  exact (exists_vertices h).choose_spec

/-! ## Literal encodings -/

/-- A literal encoding of size at most `N` at `z`: a connected set `K` of at most `N` graph edges
and a marked source subset `A` of its vertices. -/
def IsEncoding (nbr : V → Finset V) (z : V) (N : ℕ) (K : Finset (Sym2 V)) (A : Finset V) :
    Prop :=
  K.card ≤ N ∧ InGraph nbr K ∧ ConnectedAt K z ∧ ∀ v ∈ A, v = z ∨ ∃ e ∈ K, v ∈ e

/-- The encodings with exactly `n` edges. -/
def enc (nbr : V → Finset V) (z : V) (n : ℕ) : Finset (Finset (Sym2 V) × Finset V) :=
  (connSets nbr z n).biUnion (fun K => (vertsOf z K).powerset.image (fun A => (K, A)))

/-- The encodings with at most `N` edges. -/
def encLe (nbr : V → Finset V) (z : V) (N : ℕ) : Finset (Finset (Sym2 V) × Finset V) :=
  (Finset.range (N + 1)).biUnion (enc nbr z)

/-- **Lemma 9.1, one size**: at most `Δ^{2n} 2^{n+1}` encodings with `n` edges. -/
theorem card_enc_le (nbr : V → Finset V) (Δ : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ) (z : V) (n : ℕ) :
    (enc nbr z n).card ≤ Δ ^ (2 * n) * 2 ^ (n + 1) := by
  unfold enc
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ K ∈ connSets nbr z n, ((vertsOf z K).powerset.image (fun A => (K, A))).card
      ≤ ∑ _K ∈ connSets nbr z n, 2 ^ (n + 1) := by
        refine Finset.sum_le_sum (fun K hK => ?_)
        obtain ⟨hcard, -, hconn⟩ := connSets_spec hK
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_powerset]
        exact Nat.pow_le_pow_right (by norm_num) (hcard ▸ (vertsOf_spec hconn).1)
    _ = (connSets nbr z n).card * 2 ^ (n + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Δ ^ (2 * n) * 2 ^ (n + 1) :=
        Nat.mul_le_mul_right _ (card_connSets_le nbr Δ hΔ z n)

/-- `Δ^{2n} 2^{n+1} = 2 (2Δ²)^n`. -/
theorem enc_term (Δ n : ℕ) : Δ ^ (2 * n) * 2 ^ (n + 1) = 2 * (2 * Δ ^ 2) ^ n := by
  rw [mul_pow, pow_mul, pow_succ]
  ring

/-- **Lemma 9.1**: at most `2 Σ_{e ≤ N} (2Δ²)^e ≤ 4(2Δ²)^N` encodings with at most `N` edges
(`Δ ≥ 1`). -/
theorem card_encLe_le (nbr : V → Finset V) (Δ : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (z : V) (N : ℕ) : (encLe nbr z N).card ≤ 4 * (2 * Δ ^ 2) ^ N := by
  unfold encLe
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ n ∈ Finset.range (N + 1), (enc nbr z n).card
      ≤ ∑ n ∈ Finset.range (N + 1), 2 * (2 * Δ ^ 2) ^ n :=
        Finset.sum_le_sum (fun n _ => (card_enc_le nbr Δ hΔ z n).trans (enc_term Δ n).le)
    _ = 2 * ∑ n ∈ Finset.range (N + 1), (2 * Δ ^ 2) ^ n := by rw [Finset.mul_sum]
    _ ≤ 4 * (2 * Δ ^ 2) ^ N := UND.Param.two_geom_le _ N (by nlinarith)

/-- Every encoding lies in `encLe`. -/
theorem mem_encLe (nbr : V → Finset V) (Δ : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ) {z : V} {N : ℕ}
    {K : Finset (Sym2 V)} {A : Finset V} (h : IsEncoding nbr z N K A) : (K, A) ∈ encLe nbr z N := by
  obtain ⟨hcard, hG, hconn, hA⟩ := h
  refine Finset.mem_biUnion.mpr ⟨K.card, Finset.mem_range.mpr (by omega), ?_⟩
  refine Finset.mem_biUnion.mpr ⟨K, mem_connSets nbr Δ hΔ z ⟨rfl, hG, hconn⟩, ?_⟩
  refine Finset.mem_image.mpr ⟨A, Finset.mem_powerset.mpr (fun v hv => ?_), rfl⟩
  obtain ⟨-, hz, hall⟩ := vertsOf_spec hconn
  rcases hA v hv with rfl | ⟨e, he, hve⟩
  · exact hz
  · exact hall e he v hve

/-! ## The constants -/

/-- `4 X^{cg} ≤ (2²⁰ X^{c+1})^g` for `X ≥ 1`, `g ≥ 1`. -/
theorem four_mul_pow_le (X c g : ℕ) (hX : 1 ≤ X) (hg : 1 ≤ g) :
    4 * X ^ (c * g) ≤ (2 ^ 20 * X ^ (c + 1)) ^ g := by
  rw [mul_pow, ← pow_mul X]
  have h1 : 4 ≤ (2 ^ 20) ^ g :=
    calc 4 ≤ 2 ^ 20 := by norm_num
      _ ≤ (2 ^ 20) ^ g := Nat.le_self_pow (by omega) _
  exact Nat.mul_le_mul h1 (Nat.pow_le_pow_right hX (Nat.mul_le_mul_right _ (by omega)))

/-- Lemma 9.1, memory: for a graph of degree `≤ Δ ≤ Δ_paper`, at most `K_mem^g` encodings with at
most `256 g` edges. -/
theorem card_encLe_Kmem (nbr : V → Finset V) (Δ : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ)
    (hΔ1 : 1 ≤ Δ) (hΔD : Δ ≤ UND.Param.Delta) (z : V) (g : ℕ) (hg : 1 ≤ g) :
    (encLe nbr z (256 * g)).card ≤ UND.Param.Kmem ^ g := by
  refine (card_encLe_le nbr Δ hΔ hΔ1 z _).trans ?_
  refine le_trans ?_ (UND.Param.four_le_Kmem_pow g hg)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hΔD 2)) _)

/-- Lemma 9.1, memory constant: `4(2Δ²)^{256g} ≤ K_mem^g` for `1 ≤ Δ ≤ Δ_paper`. -/
theorem four_le_Kmem_pow_of_le {Δ : ℕ} (hΔD : Δ ≤ UND.Param.Delta) (g : ℕ) (hg : 1 ≤ g) :
    4 * (2 * Δ ^ 2) ^ (256 * g) ≤ UND.Param.Kmem ^ g :=
  le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hΔD 2)) _)) (UND.Param.four_le_Kmem_pow g hg)

/-- Lemma 9.1, rare groups: `4(2Δ²)^{512g} ≤ K_rare^g` for `Δ ≤ Δ_rare` (every `B`). -/
theorem four_le_KrareOf_pow (B : ℕ) {Δ : ℕ} (hΔD : Δ ≤ UND.Param.DeltaRareOf B)
    (g : ℕ) (hg : 1 ≤ g) :
    4 * (2 * Δ ^ 2) ^ (512 * g) ≤ UND.Param.KrareOf B ^ g := by
  refine le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hΔD 2)) _)) ?_
  have hX : 1 ≤ 2 * UND.Param.DeltaRareOf B ^ 2 := by
    have := UND.Param.DeltaRareOf_pos B
    have : 1 ≤ UND.Param.DeltaRareOf B ^ 2 := Nat.one_le_pow _ _ this
    omega
  have := four_mul_pow_le (2 * UND.Param.DeltaRareOf B ^ 2) 512 g hX hg
  rw [show (512 : ℕ) + 1 = 513 from rfl] at this
  exact this

/-- Lemma 9.1, rare groups: for a graph of degree `≤ Δ ≤ Δ_rare`, at most `K_rare^g` encodings
with at most `512 g` edges. -/
theorem card_encLe_KrareOf (B : ℕ) (nbr : V → Finset V) (Δ : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ)
    (hΔ1 : 1 ≤ Δ) (hΔD : Δ ≤ UND.Param.DeltaRareOf B) (z : V) (g : ℕ) (hg : 1 ≤ g) :
    (encLe nbr z (512 * g)).card ≤ UND.Param.KrareOf B ^ g :=
  (card_encLe_le nbr Δ hΔ hΔ1 z _).trans (four_le_KrareOf_pow B hΔD g hg)

/-! ## The union bound over encodings -/

/-- The union bound over a finite index set. -/
theorem measure_biUnion_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset ι) (E : ι → Set Ω) (b : ℝ≥0∞) (hb : ∀ i ∈ s, μ (E i) ≤ b) :
    μ (⋃ i ∈ s, E i) ≤ s.card * b :=
  calc μ (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, μ (E i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ s, b := Finset.sum_le_sum hb
    _ = s.card * b := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Lemma 9.1 with the union bound** (the form used in Lemmas 5.2, 7.2, 8.4). In a graph of
degree `≤ Δ`, `Δ ≥ 1`, let `4(2Δ²)^{cg} ≤ K^g` for `g ≥ 1`. If every outcome of `Ev` has, for some
`g ≥ 1`, an encoding `(K, A)` with at most `c g` edges at `z` whose event `E g K A` it lies in,
and every such event has probability at most `x^g`, then `μ(Ev) ≤ Σ_{g≥1} (K x)^g`. -/
theorem measure_le_tsum_groups {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (nbr : V → Finset V) (Δ c Kc : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (hK : ∀ g, 1 ≤ g → 4 * (2 * Δ ^ 2) ^ (c * g) ≤ Kc ^ g) (z : V)
    (E : ℕ → Finset (Sym2 V) → Finset V → Set Ω) (x : ℝ≥0∞)
    (hE : ∀ g, 1 ≤ g → ∀ K A, IsEncoding nbr z (c * g) K A → μ (E g K A) ≤ x ^ g)
    (Ev : Set Ω)
    (hEv : ∀ ω ∈ Ev, ∃ g, 1 ≤ g ∧ ∃ K A, IsEncoding nbr z (c * g) K A ∧ ω ∈ E g K A) :
    μ Ev ≤ ∑' g : ℕ, ((Kc : ℝ≥0∞) * x) ^ (g + 1) := by
  classical
  set F : ℕ → Set Ω := fun g => ⋃ p ∈ (encLe nbr z (c * (g + 1))).filter
    (fun p => IsEncoding nbr z (c * (g + 1)) p.1 p.2), E (g + 1) p.1 p.2 with hF
  have hsub : Ev ⊆ ⋃ g, F g := by
    intro ω hω
    obtain ⟨g, hg, K, A, henc, hωE⟩ := hEv ω hω
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    refine Set.mem_iUnion.mpr ⟨g, ?_⟩
    simp only [hF, Set.mem_iUnion]
    exact ⟨(K, A), Finset.mem_filter.mpr ⟨mem_encLe nbr Δ hΔ henc, henc⟩, hωE⟩
  have hFg : ∀ g, μ (F g) ≤ ((Kc : ℝ≥0∞) * x) ^ (g + 1) := by
    intro g
    refine (measure_biUnion_le_card_mul μ _ _ (x ^ (g + 1))
      (fun p hp => hE (g + 1) (by omega) p.1 p.2 (Finset.mem_filter.mp hp).2)).trans ?_
    rw [mul_pow]
    gcongr
    have h1 := (Finset.card_filter_le (encLe nbr z (c * (g + 1)))
      (fun p => IsEncoding nbr z (c * (g + 1)) p.1 p.2)).trans
      ((card_encLe_le nbr Δ hΔ hΔ1 z _).trans (hK (g + 1) (by omega)))
    exact_mod_cast h1
  calc μ Ev ≤ μ (⋃ g, F g) := measure_mono hsub
    _ ≤ ∑' g, μ (F g) := measure_iUnion_le _
    _ ≤ ∑' g : ℕ, ((Kc : ℝ≥0∞) * x) ^ (g + 1) := ENNReal.tsum_le_tsum hFg

/-- `Σ_{g ≥ 1} (ofReal r)^g = ofReal (Σ_{g ≥ 1} r^g)` for `0 ≤ r < 1`. -/
theorem tsum_ofReal_pow_succ {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    ∑' g : ℕ, (ENNReal.ofReal r) ^ (g + 1) = ENNReal.ofReal (∑' g : ℕ, r ^ (g + 1)) := by
  have hsum : Summable (fun g : ℕ => r ^ (g + 1)) := by
    simp_rw [pow_succ']
    exact (summable_geometric_of_lt_one h0 h1).mul_left r
  rw [ENNReal.ofReal_tsum_of_nonneg (fun g => pow_nonneg h0 _) hsum]
  congr 1
  funext g
  rw [ENNReal.ofReal_pow h0]

/-- **Lemma 9.1 with the union bound, real form**: with `x = ofReal y`, `0 ≤ y`, `K y < 1`,
`μ(Ev) ≤ ofReal (Σ_{g≥1} (K y)^g)` (the form of Theorem 7.3: `Σ_{g≥1}(K_mem γ)^g < 1/4`). -/
theorem measure_le_ofReal_tsum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (nbr : V → Finset V) (Δ c Kc : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (hK : ∀ g, 1 ≤ g → 4 * (2 * Δ ^ 2) ^ (c * g) ≤ Kc ^ g) (z : V)
    (E : ℕ → Finset (Sym2 V) → Finset V → Set Ω) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : (Kc : ℝ) * y < 1)
    (hE : ∀ g, 1 ≤ g → ∀ K A, IsEncoding nbr z (c * g) K A →
      μ (E g K A) ≤ ENNReal.ofReal (y ^ g))
    (Ev : Set Ω)
    (hEv : ∀ ω ∈ Ev, ∃ g, 1 ≤ g ∧ ∃ K A, IsEncoding nbr z (c * g) K A ∧ ω ∈ E g K A) :
    μ Ev ≤ ENNReal.ofReal (∑' g : ℕ, ((Kc : ℝ) * y) ^ (g + 1)) := by
  have h := measure_le_tsum_groups μ nbr Δ c Kc hΔ hΔ1 hK z E (ENNReal.ofReal y)
    (fun g hg K A henc => (hE g hg K A henc).trans_eq (ENNReal.ofReal_pow hy0 g)) Ev hEv
  have heq : (Kc : ℝ≥0∞) * ENNReal.ofReal y = ENNReal.ofReal ((Kc : ℝ) * y) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [heq, tsum_ofReal_pow_succ (by positivity) hy1] at h
  exact h

/-! ## Projection and loops -/

/-- The image of a connected edge set under a vertex map is connected at the image of the
root. -/
theorem connectedAt_image {W : Type*} [DecidableEq W] (f : V → W) {K : Finset (Sym2 V)} {z : V}
    (h : ConnectedAt K z) : ConnectedAt (K.image (Sym2.map f)) (f z) := by
  have hreach : ∀ v, Reach K z v → Reach (K.image (Sym2.map f)) (f z) (f v) := by
    intro v hv
    induction hv with
    | refl => exact ReflTransGen.refl
    | @tail b c _ hbc ih =>
      refine ih.tail ?_
      exact Finset.mem_image.mpr ⟨s(b, c), hbc, by simp⟩
  intro e he w hw
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
  obtain ⟨v, hv, rfl⟩ := Sym2.mem_map.mp hw
  exact hreach v (h e' he' v hv)

/-- Dropping loops keeps connectivity (a loop never helps to reach a new vertex). -/
theorem connectedAt_filter_not_diag {K : Finset (Sym2 V)} {z : V} (h : ConnectedAt K z) :
    ConnectedAt (K.filter (fun e => ¬ e.IsDiag)) z := by
  have hreach : ∀ v, Reach K z v → Reach (K.filter (fun e => ¬ e.IsDiag)) z v := by
    intro v hv
    induction hv with
    | refl => exact ReflTransGen.refl
    | @tail b c _ hbc ih =>
      by_cases hd : b = c
      · subst hd
        exact ih
      · exact ih.tail (Finset.mem_filter.mpr ⟨hbc, by simpa using hd⟩)
  intro e he v hv
  exact hreach v (h e (Finset.mem_filter.mp he).1 v hv)

/-- Projected witnesses keep the edge budget. -/
theorem card_image_filter_le {W : Type*} [DecidableEq W] (f : V → W) (K : Finset (Sym2 V)) :
    ((K.image (Sym2.map f)).filter (fun e => ¬ e.IsDiag)).card ≤ K.card :=
  (Finset.card_filter_le _ _).trans Finset.card_image_le

end UND.Counting

/-! ## The hook to Lemma 5.1 -/

namespace UND.Contour.GroupedSystem

open Relation

variable {V C Γ : Type*} (S : GroupedSystem V C Γ)

/-- If no unary link is followed by another, a greedy arm has at most `2b + 1` edges, `b` its
binary edges; at a non-unary start at most `2b`. -/
theorem gLen_le_two_gBin (hUU : ∀ θ, S.UN θ → ¬ S.UN (S.un θ)) (c : C) (θ : V) :
    (¬ S.UN θ → S.gLen c θ ≤ 2 * S.gBin c θ) ∧ S.gLen c θ ≤ 2 * S.gBin c θ + 1 := by
  refine S.g_induction c (P := fun θ => (¬ S.UN θ → S.gLen c θ ≤ 2 * S.gBin c θ) ∧
    S.gLen c θ ≤ 2 * S.gBin c θ + 1) (fun θ h ih => ?_) (fun θ h => ?_) θ
  · rw [S.gLen_of_step c h]
    rcases h with h | h
    · rw [S.gBin_of_NF c h]
      have := ih.2
      exact ⟨fun _ => by omega, by omega⟩
    · rw [S.gBin_of_UN c h]
      have := ih.1 (by rw [S.g_of_UN h]; exact hUU θ h)
      exact ⟨fun h' => absurd h h', by omega⟩
  · rw [S.gLen_of_isTerm c h, S.gBin_of_isTerm c h]
    exact ⟨fun _ => le_refl _, by omega⟩

/-- If no unary link is followed by another, every arm of a source has at most twice as many edges
as binary edges (the merged-corridor form; Lemma 7.2 as printed keeps an entry link and a corridor
link, see `pLen_le_three_pBin`, D17). -/
theorem pLen_le_two_pBin (hUU : ∀ θ, S.UN θ → ¬ S.UN (S.un θ)) (σ : Pole V C) (c : C) :
    S.pLen σ c ≤ 2 * S.pBin σ c := by
  have := (S.gLen_le_two_gBin hUU c (S.pFirst σ c)).2
  unfold pLen pBin
  omega

/-- If no unary link is followed by two more (chains of at most two unary links), a greedy arm has
at most `3b + 2` edges, `b` its binary edges; at a non-unary start at most `3b`. -/
theorem gLen_le_three_gBin (hUUU : ∀ θ, S.UN θ → S.UN (S.un θ) → ¬ S.UN (S.un (S.un θ)))
    (c : C) (θ : V) :
    (¬ S.UN θ → S.gLen c θ ≤ 3 * S.gBin c θ) ∧
      (S.UN θ → ¬ S.UN (S.un θ) → S.gLen c θ ≤ 3 * S.gBin c θ + 1) ∧
      S.gLen c θ ≤ 3 * S.gBin c θ + 2 := by
  refine S.g_induction c (P := fun θ => (¬ S.UN θ → S.gLen c θ ≤ 3 * S.gBin c θ) ∧
    (S.UN θ → ¬ S.UN (S.un θ) → S.gLen c θ ≤ 3 * S.gBin c θ + 1) ∧
    S.gLen c θ ≤ 3 * S.gBin c θ + 2) (fun θ h ih => ?_) (fun θ h => ?_) θ
  · rw [S.gLen_of_step c h]
    rcases h with h | h
    · rw [S.gBin_of_NF c h]
      have := ih.2.2
      exact ⟨fun _ => by omega, fun _ _ => by omega, by omega⟩
    · rw [S.gBin_of_UN c h]
      have hg : S.g c θ = S.un θ := S.g_of_UN h
      refine ⟨fun h' => absurd h h', fun _ hn => ?_, ?_⟩
      · have := ih.1 (by rw [hg]; exact hn)
        omega
      · by_cases hn : S.UN (S.un θ)
        · have := ih.2.1 (by rw [hg]; exact hn) (by rw [hg]; exact hUUU θ h hn)
          omega
        · have := ih.1 (by rw [hg]; exact hn)
          omega
  · rw [S.gLen_of_isTerm c h, S.gBin_of_isTerm c h]
    exact ⟨fun _ => le_refl _, fun _ _ => by omega, by omega⟩

/-- **Lemma 7.2 as printed (D17, QB s4)**: "Suppress each maximal source-free characteristic
corridor to a corridor link and its entry link … at most two unary entry/corridor links per positive
support edge". With chains of at most two unary links, every arm of a source has at most three
times as many edges as binary edges (so `≤ 3·48(g-1) + 5g < 149g` edges, the printed count). -/
theorem pLen_le_three_pBin (hUUU : ∀ θ, S.UN θ → S.UN (S.un θ) → ¬ S.UN (S.un (S.un θ)))
    (σ : Pole V C) (c : C) : S.pLen σ c ≤ 3 * S.pBin σ c := by
  have := (S.gLen_le_three_gBin hUUU c (S.pFirst σ c)).2.2
  unfold pLen pBin
  omega

variable [DecidableEq V] [Fintype C]

/-- The copied-arm witness has at most `Σ pLen + |group links|` edges. -/
theorem witness_card_le (P : Finset (Pole V C)) :
    (S.witness P).card ≤ ∑ σ ∈ P, ∑ c, S.pLen σ c + (S.grpEdges P).card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_right (S.armEdges_card_le P) _)

/-- The group links number at most `(|P| |C|)²`. -/
theorem grpEdges_card_le (P : Finset (Pole V C)) :
    (S.grpEdges P).card ≤ (P.card * Fintype.card C) ^ 2 := by
  classical
  unfold grpEdges
  refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
  simp [Finset.card_product, sq]

/-- **The hook to Lemma 9.1.** A projected copied-arm witness — the image of the witness under a
vertex map `f`, loops dropped — whose edges lie in a graph `nbr`, with at most `N` edges, and a
marked source set `A` of witness vertices (or the root), is a literal encoding at `f ρ`. -/
theorem witness_isEncoding {W : Type*} [DecidableEq W] (nbr : W → Finset W) (f : V → W)
    {ρ : V} {P : Finset (Pole V C)}
    (hlink : ∀ σ ∈ P, ReflTransGen (S.Linked P) (S.rootPole ρ) σ) {N : ℕ}
    (hN : (S.witness P).card ≤ N)
    (hG : UND.Counting.InGraph nbr
      (((S.witness P).image (Sym2.map f)).filter (fun e => ¬ e.IsDiag)))
    {A : Finset W}
    (hA : ∀ v ∈ A, v = f ρ ∨
      ∃ e ∈ ((S.witness P).image (Sym2.map f)).filter (fun e => ¬ e.IsDiag), v ∈ e) :
    UND.Counting.IsEncoding nbr (f ρ) N
      (((S.witness P).image (Sym2.map f)).filter (fun e => ¬ e.IsDiag)) A :=
  ⟨(UND.Counting.card_image_filter_le f _).trans hN, hG,
    UND.Counting.connectedAt_filter_not_diag
      (UND.Counting.connectedAt_image f (S.witness_connected hlink)), hA⟩

end UND.Contour.GroupedSystem
