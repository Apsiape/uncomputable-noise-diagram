/-
# The PCA layer, part 7: complete trajectories and pullbacks (Lemma 8.5, first assertion)

Nodes P9 and the first half of F5 of `BLUEPRINT.md`, NEW. Lemma 8.5: "For a fixed good two-sided
noise realization, the images `K_j = Ψ_{-j,0}(Σ^{ℤ⁶})` are nested nonempty compact sets. Their
intersection consists precisely of the time-zero states of complete trajectories. To see the
nontrivial direction, choose histories from successively earlier starting times and use product
compactness to preserve each finite update constraint; then extend forwards. Uniqueness makes the
intersection a singleton. Projecting nested compact sets onto any finite window commutes with
intersection. The finite projected sets must therefore become singletons after some finite random
time."

* `IsComplete ω X`: a complete trajectory of the common noise `ω` (`X_{t+1} = update(ω_{t+1}, X_t)`
  for every `t ∈ ℤ`);
* `flow_succ'`, `pullback_succ`, `pullback_mono`: `K_{j'} ⊆ K_j` for `j ≤ j'` (nested images);
* **`exists_complete_of_pullback`**: if every `K_j` meets a closed set `F`, some complete trajectory
  has its time-zero state in `F` (product compactness of histories `ℤ → Σ^{ℤ^d}`);
  `exists_complete`: complete trajectories exist;
* **`pullback_eventually_singleton_of_unique`** (deterministic): if all complete trajectories agree
  at time zero on a finite window `O`, the projections of the `K_j` to `O` are singletons for all
  large `j` (finitely many patterns, pigeonhole, nestedness, compactness);
* **`pullbackEventuallySingleton_of_unique`**: if complete trajectories are almost surely unique
  at time zero, the pullback clause of Theorem 9.3 (`PullbackEventuallySingleton`) holds.
-/
import UncomputableNoiseDiagram.PCA.ForgetErgodic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false

noncomputable section

namespace UND.CA

open MeasureTheory Filter Topology

variable {d : ℕ} (A : CA d)

/-- Lemma 8.5: a complete trajectory of the common noise `ω`: `X_{t+1}` is the update of `X_t`
driven by the noise at time `t + 1`, for every integer time `t`. -/
def IsComplete (ω : A.Noise₂) (X : ℤ → A.Config) : Prop :=
  ∀ t : ℤ, X (t + 1) = A.update (fun w => ω (t + 1, w)) (X t)

/-- One update is continuous in the configuration. -/
theorem continuous_update (e : Site d → Bool × A.Sym) : Continuous (A.update e) := by
  refine continuous_pi (fun v => ?_)
  by_cases h : (e v).1 = true
  · have : (fun x : A.Config => A.update e x v) = fun _ => (e v).2 := by
      funext x
      simp [update, h]
    rw [this]
    exact continuous_const
  · have : (fun x : A.Config => A.update e x v) = fun x => A.apply x v := by
      funext x
      simp [update, h]
    rw [this]
    exact A.continuous_apply_apply v

/-- The flow splits off its first step. -/
theorem flow_succ' (ω : A.Noise₂) (s : ℤ) (n : ℕ) (x : A.Config) :
    A.flow ω s (n + 1) x = A.flow ω (s + 1) n (A.update (fun w => ω (s + 1, w)) x) := by
  induction n with
  | zero =>
    show A.update (fun w => ω (s + ((0 : ℕ) : ℤ) + 1, w)) x = _
    simp
    rfl
  | succ n ih =>
    have e1 : A.flow ω s (n + 1 + 1) x =
        A.update (fun w => ω (s + ((n + 1 : ℕ) : ℤ) + 1, w)) (A.flow ω s (n + 1) x) := rfl
    have e2 : A.flow ω (s + 1) (n + 1) (A.update (fun w => ω (s + 1, w)) x) =
        A.update (fun w => ω (s + 1 + (n : ℤ) + 1, w))
          (A.flow ω (s + 1) n (A.update (fun w => ω (s + 1, w)) x)) := rfl
    rw [e1, e2, ih]
    have e3 : s + ((n + 1 : ℕ) : ℤ) + 1 = s + 1 + (n : ℤ) + 1 := by push_cast; ring
    rw [e3]

/-- `Ψ_{-(j+1),0} = Ψ_{-j,0} ∘ (one update at time -j)`. -/
theorem pullback_succ (ω : A.Noise₂) (j : ℕ) (x : A.Config) :
    A.pullback ω (j + 1) x = A.pullback ω j (A.update (fun w => ω (-((j + 1 : ℕ) : ℤ) + 1, w)) x) := by
  unfold pullback
  rw [A.flow_succ']
  have e : -((j + 1 : ℕ) : ℤ) + 1 = -(j : ℤ) := by push_cast; ring
  rw [e]

/-- The images are nested: `K_{j'} ⊆ K_j` for `j ≤ j'`. -/
theorem pullback_mono (ω : A.Noise₂) {j j' : ℕ} (h : j ≤ j') (x : A.Config) :
    ∃ y, A.pullback ω j' x = A.pullback ω j y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ k ih =>
    rw [show j + (k + 1) = (j + k) + 1 by omega, A.pullback_succ]
    exact ih _

/-- The forward flow from `x` at time `-j`, read at every time `t ≥ -j` (and `x` before). -/
def history (ω : A.Noise₂) (j : ℕ) (x : A.Config) (t : ℤ) : A.Config :=
  A.flow ω (-(j : ℤ)) (t + j).toNat x

theorem history_succ (ω : A.Noise₂) (j : ℕ) (x : A.Config) {t : ℤ} (ht : -(j : ℤ) ≤ t) :
    A.history ω j x (t + 1) = A.update (fun w => ω (t + 1, w)) (A.history ω j x t) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, t + j = m := ⟨(t + j).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have h1 : (t + 1 + j).toNat = m + 1 := by omega
  have h2 : (t + j).toNat = m := by omega
  unfold history
  rw [h1, h2]
  show A.update (fun w => ω (-(j : ℤ) + (m : ℤ) + 1, w)) (A.flow ω (-(j : ℤ)) m x) = _
  have e : -(j : ℤ) + (m : ℤ) + 1 = t + 1 := by omega
  rw [e]

theorem history_zero (ω : A.Noise₂) (j : ℕ) (x : A.Config) :
    A.history ω j x 0 = A.pullback ω j x := by
  unfold history pullback
  congr 1
  simp

/-- **Lemma 8.5, compactness.** If every pullback image `K_j` meets a closed set `F`, some complete
trajectory has its time-zero state in `F`: "choose histories from successively earlier starting
times and use product compactness to preserve each finite update constraint". -/
theorem exists_complete_of_pullback (ω : A.Noise₂) {F : Set A.Config} (hF : IsClosed F)
    (h : ∀ j : ℕ, ∃ x, A.pullback ω j x ∈ F) : ∃ X, A.IsComplete ω X ∧ X 0 ∈ F := by
  let T : ℕ → Set (ℤ → A.Config) := fun j =>
    {X | X 0 ∈ F} ∩ ⋂ (t : ℤ) (_ : -(j : ℤ) ≤ t),
      {X | X (t + 1) = A.update (fun w => ω (t + 1, w)) (X t)}
  have hclosed : ∀ j, IsClosed (T j) := by
    intro j
    refine (hF.preimage (continuous_apply 0)).inter
      (isClosed_iInter fun t => isClosed_iInter fun _ => ?_)
    exact isClosed_eq (continuous_apply (t + 1))
      ((A.continuous_update _).comp (continuous_apply t))
  have hne : ∀ j, (T j).Nonempty := by
    intro j
    obtain ⟨x, hx⟩ := h j
    refine ⟨A.history ω j x, ?_, ?_⟩
    · show A.history ω j x 0 ∈ F
      rw [A.history_zero]
      exact hx
    · rw [Set.mem_iInter₂]
      intro t ht
      exact A.history_succ ω j x ht
  have hdec : ∀ j, T (j + 1) ⊆ T j := by
    intro j X hX
    obtain ⟨h0, h1⟩ := hX
    refine ⟨h0, ?_⟩
    rw [Set.mem_iInter₂] at h1 ⊢
    intro t ht
    exact h1 t (by push_cast; omega)
  obtain ⟨X, hX⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hX
  refine ⟨X, fun t => ?_, (hX 0).1⟩
  have := (hX (-t).toNat).2
  rw [Set.mem_iInter₂] at this
  exact this t (by omega)

/-- Complete trajectories exist (Lemma 8.5: the `K_j` are nonempty, so is their intersection). -/
theorem exists_complete (ω : A.Noise₂) : ∃ X, A.IsComplete ω X := by
  obtain ⟨X, hX, -⟩ := A.exists_complete_of_pullback ω isClosed_univ
    (fun j => ⟨A.zeroConfig, Set.mem_univ _⟩)
  exact ⟨X, hX⟩

/-- **Lemma 8.5, deterministic core.** If all complete trajectories of `ω` agree at time zero on
a finite window `O`, then for all large `j` the pullback image `K_j` projects to a single point
of `Σ^O`. -/
theorem pullback_eventually_singleton_of_unique (ω : A.Noise₂) (O : Finset (Site d))
    (huniq : ∀ X Y : ℤ → A.Config, A.IsComplete ω X → A.IsComplete ω Y →
      ∀ w ∈ O, X 0 w = Y 0 w) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ x x' : A.Config, ∀ w ∈ O,
      A.pullback ω j x w = A.pullback ω j x' w := by
  classical
  by_contra hne
  push Not at hne
  -- every `K_j` contains two points that differ on `O`
  have hall : ∀ j : ℕ, ∃ x x' : A.Config,
      (fun w : O => A.pullback ω j x w) ≠ (fun w : O => A.pullback ω j x' w) := by
    intro j
    obtain ⟨j', hj', x, x', w, hw, hne'⟩ := hne j
    obtain ⟨y, hy⟩ := A.pullback_mono ω hj' x
    obtain ⟨y', hy'⟩ := A.pullback_mono ω hj' x'
    refine ⟨y, y', fun h => hne' ?_⟩
    rw [hy, hy']
    exact congrFun h ⟨w, hw⟩
  choose xs xs' hxs using hall
  -- pigeonhole: one pair of distinct patterns occurs for infinitely many `j`
  let f : ℕ → (O → A.Sym) × (O → A.Sym) := fun j =>
    ((fun w : O => A.pullback ω j (xs j) w), (fun w : O => A.pullback ω j (xs' j) w))
  obtain ⟨⟨p, p'⟩, hinf⟩ := Finite.exists_infinite_fiber f
  have hinf' : (f ⁻¹' {(p, p')}).Infinite := Set.infinite_coe_iff.mp hinf
  -- nestedness: both patterns occur in every `K_j`
  have hocc : ∀ j : ℕ, (∃ y, (fun w : O => A.pullback ω j y w) = p) ∧
      (∃ y, (fun w : O => A.pullback ω j y w) = p') := by
    intro j
    obtain ⟨j', hj'f, hjj'⟩ := hinf'.exists_gt j
    have hfj : f j' = (p, p') := hj'f
    obtain ⟨y, hy⟩ := A.pullback_mono ω hjj'.le (xs j')
    obtain ⟨y', hy'⟩ := A.pullback_mono ω hjj'.le (xs' j')
    refine ⟨⟨y, ?_⟩, ⟨y', ?_⟩⟩
    · rw [← hy]
      exact (Prod.mk.inj hfj).1
    · rw [← hy']
      exact (Prod.mk.inj hfj).2
  have hpp : p ≠ p' := by
    obtain ⟨j', hj'f, -⟩ := hinf'.exists_gt 0
    have hfj : f j' = (p, p') := hj'f
    have := hxs j'
    rw [(Prod.mk.inj hfj).1.symm, (Prod.mk.inj hfj).2.symm] at *
    exact this
  -- compactness: complete trajectories realize both patterns at time zero
  have hcl : ∀ q : O → A.Sym, IsClosed {y : A.Config | (fun w : O => y w) = q} := fun q =>
    (isClosed_discrete {q}).preimage (A.continuous_restrictWindow O)
  obtain ⟨X, hX, hX0⟩ := A.exists_complete_of_pullback ω (hcl p) (fun j => (hocc j).1)
  obtain ⟨Y, hY, hY0⟩ := A.exists_complete_of_pullback ω (hcl p') (fun j => (hocc j).2)
  apply hpp
  rw [← show (fun w : O => X 0 w) = p from hX0, ← show (fun w : O => Y 0 w) = p' from hY0]
  funext w
  exact huniq X Y hX hY w.1 w.2

/-- **Lemma 8.5, first assertion.** If complete common-noise trajectories are almost surely unique
(at time zero), then every finite-window pullback image is almost surely eventually a singleton:
the last clause of Theorem 9.3. -/
theorem pullbackEventuallySingleton_of_unique {ε : ℝ}
    (h : ∀ᵐ ω ∂(A.noiseLaw₂ ε), ∀ X Y : ℤ → A.Config, A.IsComplete ω X → A.IsComplete ω Y →
      X 0 = Y 0) :
    A.PullbackEventuallySingleton ε := by
  intro O
  filter_upwards [h] with ω hω
  exact A.pullback_eventually_singleton_of_unique ω O
    (fun X Y hX hY w _ => congrFun (hω X Y hX hY) w)

end UND.CA

end
