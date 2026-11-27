import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# OEIS A172572 Supercongruence and Its General `m`-Family

This file proves Peter Bala's Conjecture 1 on OEIS A172572 (Oct 2024):
for every prime `p`, the number `a(p)` of `3p × 6` 0-1 arrays with row sums `2` and
column sums `p` satisfies `a(p) ≡ 90 (mod p^2)`.

We prove the full infinite family for all `m ≥ 1` and all primes `p`:
the number `a_m(p)` of `(mp) × (2m)` 0-1 arrays with row sums `2` and column sums `p`
satisfies
`a_m(p) ≡ (2m)! / 2^m (mod p^2)`.
Specializing to `m = 3` gives `6! / 2^3 = 90`, settling OEIS A172572 Conjecture 1.

## Proof Architecture

1. **Babbage's Congruence (`choose_mul_prime_mod_sq`)**: For every prime `p` and `j ≥ 1`,
   `Nat.choose (j * p) p ≡ j [MOD p^2]`, proved via the exact integer pairing identity
   `(jp - t)(jp - (p - t)) = t(p - t) + j(j - 1)p^2` for odd `p` and directly for `p = 2`.
2. **Fiber Decomposition (`aArray_eq_sum_multinomial`)**: Grouping arrays by their
   edge-multiplicity vector `k : Edge m → ℕ` expresses `a_m(n)` as the sum of
   `Nat.multinomial Finset.univ k` over all `n`-regular multigraphs on `2m` vertices.
3. **Graph Gap Lemma (`card_full_edges_ne_sub_one`)**: Any `p`-regular multigraph on `2m`
   vertices cannot have exactly `m - 1` edges of multiplicity `p` (since the remaining `2`
   vertices force the `m`-th edge to also have multiplicity `p`). Thus every non-matching
   multigraph has at most `m - 2` edges of multiplicity `p`.
4. **p-adic Valuation (`dvd_multinomial_of_nonMatching`)**: For any non-matching multigraph,
   `v_p((mp)!) ≥ m` while `v_p(∏ (k e)!) ≤ m - 2`, so `p^2 ∣ Nat.multinomial univ k`.
5. **Perfect Matchings (`card_perfectMatchings`)**: The `(2m - 1)!!` perfect matchings of
   `K_{2m}` each contribute `(mp)! / (p!)^m = ∏_{j=1}^m C(jp, p) ≡ m! (mod p^2)`, yielding
   `a_m(p) ≡ (2m - 1)!! * m! = (2m)! / 2^m (mod p^2)`.
-/

set_option maxHeartbeats 2000000

open scoped BigOperators
open Finset Nat

namespace OEIS_A172572

/-! ### Part 1: Babbage's Congruence `C(j * p, p) ≡ j [MOD p^2]` for all primes `p` -/

lemma prod_Icc_pair_shift (h : ℕ) (f : ℕ → ℤ) :
    (∏ t ∈ Icc 1 (2 * h), f t) = ∏ t ∈ Icc 1 h, (f t * f (2 * h + 1 - t)) := by
  have hsplit : Icc 1 (2 * h) = Icc 1 h ∪ Icc (h + 1) (2 * h) := by
    ext x; simp only [mem_Icc, mem_union]; omega
  have hdisj : Disjoint (Icc 1 h) (Icc (h + 1) (2 * h)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [mem_Icc] at hx1 hx2
    omega
  rw [hsplit, Finset.prod_union hdisj, Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_bij (fun x _ => 2 * h + 1 - x) ?_ ?_ ?_ ?_
  · intro x hx; simp only [mem_Icc] at hx ⊢; omega
  · intro x₁ hx₁ x₂ hx₂ heq; simp only [mem_Icc] at hx₁ hx₂; omega
  · intro y hy
    refine ⟨2 * h + 1 - y, ?_, ?_⟩
    · simp only [mem_Icc] at hy ⊢; omega
    · simp only [mem_Icc] at hy; omega
  · intro x hx
    simp only [mem_Icc] at hx
    have : 2 * h + 1 - (2 * h + 1 - x) = x := by omega
    rw [this]

lemma descFactorial_eq_prod_Icc (n k : ℕ) (hk : k ≤ n) :
    (n.descFactorial k : ℤ) = ∏ t ∈ Icc 1 k, ((n + 1 : ℤ) - t) := by
  rw [Nat.descFactorial_eq_prod_range]
  push_cast
  refine Finset.prod_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_range, mem_Icc] at hi ⊢; omega
  · intro i₁ _ i₂ _ h; omega
  · intro t ht
    refine ⟨t - 1, ?_, ?_⟩
    · simp only [mem_Icc, mem_range] at ht ⊢; omega
    · simp only [mem_Icc] at ht; omega
  · intro i hi
    simp only [mem_range] at hi
    have hle : i ≤ n := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring

lemma factorial_eq_prod_Icc (k : ℕ) :
    ((k ! : ℕ) : ℤ) = ∏ t ∈ Icc 1 k, (t : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.factorial_succ, Nat.cast_mul, ih]
      have hsplit : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hsplit, Finset.prod_insert (by simp), mul_comm]

lemma int_modEq_prod_Icc {n : ℤ} {s : Finset ℕ} {f g : ℕ → ℤ}
    (h : ∀ t ∈ s, f t ≡ g t [ZMOD n]) :
    (∏ t ∈ s, f t) ≡ (∏ t ∈ s, g t) [ZMOD n] := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact Int.ModEq.mul (h a (Finset.mem_insert_self _ _))
        (ih (fun t ht => h t (Finset.mem_insert_of_mem ht)))

lemma babbage_odd_prime {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (j : ℕ) (hj : 1 ≤ j) :
    (j * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le; omega
  obtain ⟨h, hh⟩ : ∃ h : ℕ, p - 1 = 2 * h := by
    rcases hp.eq_two_or_odd with rfl | hmod
    · exact absurd rfl hodd
    · exact ⟨(p - 1) / 2, by omega⟩
  have hjp : p - 1 ≤ j * p - 1 := by
    have : p ≤ j * p := Nat.le_mul_of_pos_left p (by omega)
    omega
  have hprod_congr :
      (((p - 1)! * (j * p - 1).choose (p - 1) : ℕ) : ℤ) ≡ (((p - 1)! : ℕ) : ℤ) [ZMOD (p ^ 2 : ℤ)] := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, descFactorial_eq_prod_Icc _ _ hjp,
      factorial_eq_prod_Icc]
    have hjp1 : ((j * p - 1 + 1 : ℕ) : ℤ) = (j * p : ℤ) := by
      have : 1 ≤ j * p := by nlinarith
      omega
    have hjp1' : ((↑(j * p - 1) + 1 : ℤ) = (j * p : ℤ)) := by
      have h1 : 1 ≤ j * p := by nlinarith [hj, hp3]
      rw [Nat.cast_sub h1, Nat.cast_one, Nat.cast_mul]
      ring
    simp_rw [hjp1', hh]
    rw [prod_Icc_pair_shift h (fun t => (j * p : ℤ) - t),
      prod_Icc_pair_shift h (fun t => (t : ℤ))]
    refine int_modEq_prod_Icc (s := Icc 1 h) (fun t ht => ?_)
    have h2h : 2 * h + 1 = p := by omega
    rw [h2h]
    have ht_le : t ≤ p := by simp only [mem_Icc] at ht; omega
    have hcast : ((p - t : ℕ) : ℤ) = (p : ℤ) - t := Nat.cast_sub ht_le
    rw [hcast]
    rw [Int.modEq_iff_dvd]
    refine ⟨-(j * (j - 1) : ℤ), ?_⟩
    ring
  have hnat : (p - 1)! * (j * p - 1).choose (p - 1) ≡ (p - 1)! * 1 [MOD p ^ 2] := by
    rw [mul_one]
    exact Int.natCast_modEq_iff.mp (by simpa using hprod_congr)
  have hcop : Nat.Coprime (p - 1)! (p ^ 2) := by
    apply Nat.Coprime.pow_right
    exact (hp.coprime_iff_not_dvd.mpr (by
      intro hdvd
      have := hp.dvd_factorial.mp hdvd
      omega)).symm
  exact Nat.ModEq.cancel_left_of_coprime hcop.symm hnat

lemma choose_mul_prime_mod_sq {p : ℕ} (hp : p.Prime) (j : ℕ) (hj : 1 ≤ j) :
    (j * p).choose p ≡ j [MOD p ^ 2] := by
  by_cases hp2 : p = 2
  · subst hp2
    have hval : (j * 2).choose 2 = j * (2 * j - 1) := by
      rw [Nat.choose_two_right]
      have : j * 2 * (j * 2 - 1) = 2 * (j * (2 * j - 1)) := by
        cases j with
        | zero => omega
        | succ k => ring
      rw [this, Nat.mul_div_right _ (by omega)]
    rw [hval, Nat.modEq_iff_dvd]
    have hsub : ((j * (2 * j - 1) : ℕ) : ℤ) - (j : ℤ) = 2 * (j : ℤ) * ((j : ℤ) - 1) := by
      have h1 : 1 ≤ 2 * j := by omega
      push_cast [Nat.cast_sub h1]
      ring
    have heven : (2 : ℤ) ∣ (j : ℤ) * ((j : ℤ) - 1) := by
      rcases Int.even_or_odd (j : ℤ) with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨k * (2 * k - 1), by rw [hk]; ring⟩
      · exact ⟨(2 * k + 1) * k, by rw [hk]; ring⟩
    rcases heven with ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    have h4 : ((2 ^ 2 : ℕ) : ℤ) = 4 := by norm_num
    rw [h4]
    linarith
  · have hstep : (j * p).choose p = j * (j * p - 1).choose (p - 1) := by
      have h1 := Nat.add_one_mul_choose_eq (j * p - 1) (p - 1)
      have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
      have hjp1 : j * p - 1 + 1 = j * p := Nat.sub_add_cancel (by nlinarith [hp.one_le])
      rw [hp1, hjp1] at h1
      have h2 : p * (j * p).choose p = p * (j * (j * p - 1).choose (p - 1)) := by
        linarith
      exact Nat.eq_of_mul_eq_mul_left hp.pos h2
    rw [hstep]
    simpa [mul_one] using (babbage_odd_prime hp hp2 j hj).mul_left j

lemma prod_choose_mul_prime_eq (m p : ℕ) :
    (p !) ^ m * (∏ j ∈ Icc 1 m, (j * p).choose p) = (m * p)! := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hsplit : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hsplit, Finset.prod_insert (by simp), pow_succ]
      calc
        (p !) ^ m * p ! * (((m + 1) * p).choose p * ∏ j ∈ Icc 1 m, (j * p).choose p)
            = ((p !) ^ m * ∏ j ∈ Icc 1 m, (j * p).choose p) * (p ! * ((m + 1) * p).choose p) := by
                ring
        _ = (m * p)! * (p ! * ((m + 1) * p).choose p) := by rw [ih]
        _ = ((m + 1) * p).choose p * p ! * (m * p)! := by ring
        _ = ((m + 1) * p)! := by
              have hle : p ≤ (m + 1) * p := Nat.le_mul_of_pos_left p (Nat.succ_pos m)
              have hsub : (m + 1) * p - p = m * p := by
                rw [add_mul, one_mul, Nat.add_sub_cancel]
              rw [← hsub]
              exact Nat.choose_mul_factorial_mul_factorial hle

lemma prod_choose_mul_prime_mod_sq {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (∏ j ∈ Icc 1 m, (j * p).choose p) ≡ m ! [MOD p ^ 2] := by
  induction m with
  | zero => exact Nat.ModEq.refl 1
  | succ m ih =>
      have hsplit : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hsplit, Finset.prod_insert (by simp), Nat.factorial_succ]
      exact (choose_mul_prime_mod_sq hp (m + 1) (Nat.succ_pos m)).mul ih

/-! ### Part 2: `mn × 2m` 0-1 Arrays, Edge Multiplicities, and Multinomial Decomposition -/

/-- The undirected edges of the complete graph `K_{2m}`, represented as ordered pairs `i < j`. -/
abbrev Edge (m : ℕ) := { e : Fin (2 * m) × Fin (2 * m) // e.1 < e.2 }

/-- Incidence predicate: vertex `v` is an endpoint of edge `e`. -/
def incident {m : ℕ} (v : Fin (2 * m)) (e : Edge m) : Prop :=
  v = e.1.1 ∨ v = e.1.2

instance {m : ℕ} (v : Fin (2 * m)) (e : Edge m) : Decidable (incident v e) :=
  inferInstanceAs (Decidable (v = e.1.1 ∨ v = e.1.2))

/-- An `(mn) × (2m)` 0-1 array with row sums `2` and column sums `n`, encoded by specifying
for each of the `m * n` rows the unique edge `{i, j}` (`i < j`) where the two `1`s lie. -/
def ValidArray (m n : ℕ) (f : Fin (m * n) → Edge m) : Prop :=
  ∀ v : Fin (2 * m), (Finset.univ.filter fun r => incident v (f r)).card = n

instance (m n : ℕ) (f : Fin (m * n) → Edge m) : Decidable (ValidArray m n f) :=
  inferInstanceAs (Decidable (∀ v, _))

/-- The count `a_m(n)` of `(mn) × (2m)` 0-1 arrays with row sums `2` and column sums `n`.
For `m = 3`, this is OEIS A172572(n). -/
def aArray (m n : ℕ) : ℕ :=
  (Finset.univ.filter (ValidArray m n)).card

/-- A degree-valid edge multiplicity function `k : Edge m → ℕ` (an `n`-regular multigraph on `K_{2m}`). -/
def ValidDeg (m n : ℕ) (k : Edge m → ℕ) : Prop :=
  ∀ v : Fin (2 * m), (∑ e : Edge m, if incident v e then k e else 0) = n

instance (m n : ℕ) (k : Edge m → ℕ) : Decidable (ValidDeg m n k) :=
  inferInstanceAs (Decidable (∀ v, _))

lemma validDeg_le_n {m n : ℕ} {k : Edge m → ℕ} (hk : ValidDeg m n k) (e : Edge m) :
    k e ≤ n := by
  have hv := hk e.1.1
  have hle : (if incident e.1.1 e then k e else 0) ≤
      ∑ e' : Edge m, if incident e.1.1 e' then k e' else 0 :=
    Finset.single_le_sum (f := fun e' => if incident e.1.1 e' then k e' else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
  simp only [incident, true_or, ↓reduceIte] at hle
  simp only [incident] at hv
  rw [hv] at hle
  exact hle

lemma validDeg_sum {m n : ℕ} {k : Edge m → ℕ} (hk : ValidDeg m n k) :
    (∑ e : Edge m, k e) = m * n := by
  have hdouble : 2 * (∑ e : Edge m, k e) = 2 * (m * n) := by
    calc
      2 * (∑ e : Edge m, k e)
          = ∑ e : Edge m, (k e + k e) := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _; ring
      _ = ∑ e : Edge m, ∑ v : Fin (2 * m), (if incident v e then k e else 0) := by
            apply Finset.sum_congr rfl
            intro e _
            have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2
            have hfilt : (Finset.univ.filter fun v : Fin (2 * m) => incident v e) =
                {e.1.1, e.1.2} := by
              ext v
              constructor
              · intro hv
                have h := (Finset.mem_filter.mp hv).2
                simpa [incident, Finset.mem_insert, Finset.mem_singleton] using h
              · intro hv
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                simpa [incident, Finset.mem_insert, Finset.mem_singleton] using hv
            rw [← Finset.sum_filter, hfilt, Finset.sum_pair hne]
      _ = ∑ v : Fin (2 * m), ∑ e : Edge m, (if incident v e then k e else 0) :=
            Finset.sum_comm
      _ = ∑ _v : Fin (2 * m), n := by
            apply Finset.sum_congr rfl; intro v _; exact hk v
      _ = 2 * (m * n) := by simp [mul_assoc]
  omega

/-- General fiber-counting lemma: the number of functions `f : α → β` with prescribed fiber
sizes `k b` equals `Nat.multinomial Finset.univ k`. -/
lemma card_functions_with_fiber {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (s : Finset β) (k : β → ℕ) (hcard : Fintype.card α = ∑ b ∈ s, k b) :
    (Finset.univ.filter fun f : α → β =>
      (∀ a, f a ∈ s) ∧ ∀ b ∈ s, (Finset.univ.filter fun a => f a = b).card = k b).card =
    Nat.multinomial s k := by
  induction s using Finset.induction_on generalizing α with
  | empty =>
      simp only [Finset.sum_empty] at hcard
      haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp hcard
      simp [Nat.multinomial_empty]
  | @insert b₀ s hb₀ ih =>
      rw [Finset.sum_insert hb₀] at hcard
      rw [Nat.multinomial_insert hb₀]
      -- Partition by the subset `A = f⁻¹({b₀})` of size `k b₀`
      let P := (Finset.univ : Finset α).powersetCard (k b₀)
      have hbi :
          (Finset.univ.filter fun f : α → β =>
            (∀ a, f a ∈ insert b₀ s) ∧
              ∀ b ∈ insert b₀ s, (Finset.univ.filter fun a => f a = b).card = k b).card =
          ∑ A ∈ P,
            (Finset.univ.filter fun f : α → β =>
              (Finset.univ.filter fun a => f a = b₀) = A ∧
              (∀ a, f a ∈ insert b₀ s) ∧
              ∀ b ∈ s, (Finset.univ.filter fun a => f a = b).card = k b).card := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext f
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, P,
            Finset.mem_powersetCard, Finset.subset_univ]
          constructor
          · rintro ⟨hmem, hfib⟩
            refine ⟨Finset.univ.filter fun a => f a = b₀, hfib b₀ (mem_insert_self _ _), rfl,
              hmem, fun b hb => hfib b (mem_insert_of_mem hb)⟩
          · rintro ⟨A, hAcard, hAeq, hmem, hfib⟩
            refine ⟨hmem, fun b hb => ?_⟩
            rcases mem_insert.mp hb with rfl | hb'
            · rw [hAeq, hAcard]
            · exact hfib b hb'
        · intro A₁ _ A₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro f hf₁ hf₂
          simp only [Finset.mem_filter] at hf₁ hf₂
          exact hne (hf₁.2.1.symm.trans hf₂.2.1)
      rw [hbi]
      have heach : ∀ A ∈ P,
          (Finset.univ.filter fun f : α → β =>
            (Finset.univ.filter fun a => f a = b₀) = A ∧
            (∀ a, f a ∈ insert b₀ s) ∧
            ∀ b ∈ s, (Finset.univ.filter fun a => f a = b).card = k b).card =
          Nat.multinomial s k := by
        intro A hA
        have hAcard : A.card = k b₀ := (Finset.mem_powersetCard.mp hA).2
        let α' := { a : α // a ∉ A }
        have hcard' : Fintype.card α' = ∑ b ∈ s, k b := by
          dsimp only [α']
          rw [Fintype.card_subtype_compl, Fintype.card_coe, hAcard, hcard, Nat.add_sub_cancel_left]
        rw [← ih (α := α') hcard']
        refine Finset.card_bij (fun f _ => fun x : α' => f x.1) ?_ ?_ ?_
        · intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
          rcases hf with ⟨hAeq, hmem, hfib⟩
          refine ⟨fun x => ?_, fun b hb => ?_⟩
          · rcases mem_insert.mp (hmem x.1) with hfb | hfs
            · exfalso
              have hxA : x.1 ∈ A := by
                have h : x.1 ∈ ({a | f a = b₀} : Finset α) := by
                  simp [hfb]
                simpa [hAeq] using h
              exact x.2 hxA
            · exact hfs
          · rw [← hfib b hb]
            refine Finset.card_bij (fun (x : α') _ => x.1) ?_ ?_ ?_
            · intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact hx
            · intro x₁ _ x₂ _ h; exact Subtype.ext h
            · intro a ha
              simp only [mem_filter, mem_univ, true_and] at ha
              have haA : a ∉ A := by
                rw [← hAeq]; simp only [mem_filter, mem_univ, true_and]
                intro hab₀; exact hb₀ (hab₀ ▸ ha ▸ hb)
              exact ⟨⟨a, haA⟩, by simp [ha], rfl⟩
        · intro f₁ hf₁ f₂ hf₂ heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
          ext a
          by_cases ha : a ∈ A
          · have h1 : f₁ a = b₀ := by
              have := ha; rw [← hf₁.1] at this; exact (Finset.mem_filter.mp this).2
            have h2 : f₂ a = b₀ := by
              have := ha; rw [← hf₂.1] at this; exact (Finset.mem_filter.mp this).2
            rw [h1, h2]
          · exact congr_fun heq ⟨a, ha⟩
        · intro g hg
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
          refine ⟨fun a => if ha : a ∈ A then b₀ else g ⟨a, ha⟩, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, ?_, ?_⟩
            · ext a
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases ha : a ∈ A
              · simp [ha]
              · simp only [ha, ↓reduceDIte, iff_false]
                intro hgb; exact hb₀ (hgb ▸ hg.1 ⟨a, ha⟩)
            · intro a
              by_cases ha : a ∈ A
              · simp [ha]
              · simp [ha, mem_insert_of_mem (hg.1 ⟨a, ha⟩)]
            · intro b hb
              rw [← hg.2 b hb]
              refine Finset.card_bij (fun a ha => ⟨a, by
                simp only [mem_filter, mem_univ, true_and] at ha
                intro haA
                simp only [haA, ↓reduceDIte] at ha
                exact hb₀ (ha ▸ hb)⟩) ?_ ?_ ?_
              · intro a ha
                simp only [mem_filter, mem_univ, true_and] at ha ⊢
                by_cases haA : a ∈ A
                · simp only [haA, ↓reduceDIte] at ha; exact absurd (ha ▸ hb) hb₀
                · simpa [haA] using ha
              · intro a₁ _ a₂ _ h; exact congr_arg Subtype.val h
              · intro x hx
                simp only [mem_filter, mem_univ, true_and] at hx
                exact ⟨x.1, by simp [x.2, hx], rfl⟩
          · ext x; simp [x.2]
      rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul]
      simp only [P, Finset.card_powersetCard, Finset.card_univ, hcard]


/-- Finite bounding set of all edge-multiplicity functions `k : Edge m → ℕ` with `k e ≤ n`. -/
def boundedDegs (m n : ℕ) : Finset (Edge m → ℕ) :=
  Fintype.piFinset fun _ : Edge m => Finset.range (n + 1)

lemma mem_boundedDegs_of_valid {m n : ℕ} {k : Edge m → ℕ} (hk : ValidDeg m n k) :
    k ∈ boundedDegs m n := by
  simp only [boundedDegs, Fintype.mem_piFinset, Finset.mem_range]
  intro e
  exact Nat.lt_succ_of_le (validDeg_le_n hk e)

lemma aArray_eq_sum_multinomial (m n : ℕ) :
    aArray m n = ∑ k ∈ (boundedDegs m n).filter (ValidDeg m n), Nat.multinomial Finset.univ k := by
  unfold aArray
  let fiberOf : (Fin (m * n) → Edge m) → (Edge m → ℕ) :=
    fun f e => (Finset.univ.filter fun r => f r = e).card
  have hpart :
      (Finset.univ.filter (ValidArray m n)).card =
      ∑ k ∈ (boundedDegs m n).filter (ValidDeg m n),
        (Finset.univ.filter fun f : Fin (m * n) → Edge m => fiberOf f = k).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hf
        have hvd : ValidDeg m n (fiberOf f) := by
          intro v
          rw [← hf v]
          calc
            (∑ e : Edge m, if incident v e then (Finset.univ.filter fun r => f r = e).card else 0)
                = ∑ e ∈ Finset.univ.filter (incident v),
                    (Finset.univ.filter fun r => f r = e).card := by
                    rw [Finset.sum_filter]
            _ = (Finset.univ.filter fun r => incident v (f r)).card := by
                    rw [← Finset.card_biUnion]
                    · congr 1; ext r; simp
                    · intro e₁ _ e₂ _ hne
                      change Disjoint _ _
                      rw [Finset.disjoint_left]
                      intro r hr₁ hr₂
                      simp only [mem_filter] at hr₁ hr₂
                      exact hne (hr₁.2.symm.trans hr₂.2)
        exact ⟨fiberOf f, ⟨mem_boundedDegs_of_valid hvd, hvd⟩, rfl⟩
      · rintro ⟨k, ⟨_, hvd⟩, rfl⟩
        intro v
        calc
          (Finset.univ.filter fun r => incident v (f r)).card
              = ∑ e ∈ Finset.univ.filter (incident v),
                  (Finset.univ.filter fun r => f r = e).card := by
                  rw [← Finset.card_biUnion]
                  · congr 1; ext r; simp
                  · intro e₁ _ e₂ _ hne
                    change Disjoint _ _
                    rw [Finset.disjoint_left]
                    intro r hr₁ hr₂
                    simp only [mem_filter] at hr₁ hr₂
                    exact hne (hr₁.2.symm.trans hr₂.2)
          _ = ∑ e : Edge m, if incident v e then (Finset.univ.filter fun r => f r = e).card else 0 := by
                  rw [Finset.sum_filter]
          _ = n := by simpa only [fiberOf] using hvd v
    · intro k₁ _ k₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro f hf₁ hf₂
      simp only [mem_filter] at hf₁ hf₂
      exact hne (hf₁.2.symm.trans hf₂.2)
  rw [hpart]
  apply Finset.sum_congr rfl
  intro k hk
  have hvd : ValidDeg m n k := (Finset.mem_filter.mp hk).2
  have hsum : Fintype.card (Fin (m * n)) = ∑ e ∈ (Finset.univ : Finset (Edge m)), k e := by
    rw [Fintype.card_fin, validDeg_sum hvd]
  rw [← card_functions_with_fiber (Finset.univ : Finset (Edge m)) k hsum]
  congr 1
  ext f
  simp [fiberOf, funext_iff]

/-! ### Part 3: Graph Gap Lemma and `p^2`-Divisibility of Non-Matchings -/

/-- Edges of multiplicity `p` in `k`. -/
def fullEdges {m : ℕ} (p : ℕ) (k : Edge m → ℕ) : Finset (Edge m) :=
  Finset.univ.filter fun e => k e = p

lemma fullEdges_disjoint_endpoints {m p : ℕ} (hp : 0 < p) {k : Edge m → ℕ} (hk : ValidDeg m p k)
    {e₁ e₂ : Edge m} (h₁ : e₁ ∈ fullEdges p k) (h₂ : e₂ ∈ fullEdges p k) (hne : e₁ ≠ e₂)
    (v : Fin (2 * m)) (hv₁ : incident v e₁) (hv₂ : incident v e₂) : False := by
  have h1 : k e₁ = p := (Finset.mem_filter.mp h₁).2
  have h2 : k e₂ = p := (Finset.mem_filter.mp h₂).2
  have hsub : ({e₁, e₂} : Finset (Edge m)) ⊆ Finset.univ := Finset.subset_univ _
  have hle : ∑ e ∈ ({e₁, e₂} : Finset (Edge m)), (if incident v e then k e else 0) ≤
      ∑ e : Edge m, (if incident v e then k e else 0) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair hne, hk v] at hle
  simp only [hv₁, hv₂, ↓reduceIte, h1, h2] at hle
  omega

/-- The set of vertices covered by the full edges of `k`. -/
def coveredVerts {m : ℕ} (p : ℕ) (k : Edge m → ℕ) : Finset (Fin (2 * m)) :=
  (fullEdges p k).biUnion fun e => {e.1.1, e.1.2}

lemma card_coveredVerts {m p : ℕ} (hp : 0 < p) {k : Edge m → ℕ} (hk : ValidDeg m p k) :
    (coveredVerts p k).card = 2 * (fullEdges p k).card := by
  unfold coveredVerts
  rw [Finset.card_biUnion]
  · calc
      ∑ e ∈ fullEdges p k, ({e.1.1, e.1.2} : Finset (Fin (2 * m))).card
          = ∑ _e ∈ fullEdges p k, 2 := by
              apply Finset.sum_congr rfl
              intro e _
              exact Finset.card_pair (ne_of_lt e.2)
      _ = 2 * (fullEdges p k).card := by simp [mul_comm]
  · intro e₁ h₁ e₂ h₂ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    simp only [mem_insert, mem_singleton] at hv₁ hv₂
    exact fullEdges_disjoint_endpoints hp hk h₁ h₂ hne v hv₁ hv₂

lemma card_fullEdges_le {m p : ℕ} (hp : 0 < p) {k : Edge m → ℕ} (hk : ValidDeg m p k) :
    (fullEdges p k).card ≤ m := by
  have hle : (coveredVerts p k).card ≤ Fintype.card (Fin (2 * m)) := Finset.card_le_univ _
  rw [card_coveredVerts hp hk, Fintype.card_fin] at hle
  omega

/-- Key Graph Gap Lemma: a `p`-regular multigraph on `2m` vertices cannot have
exact `m - 1` edges of multiplicity `p`. -/
lemma card_fullEdges_ne_sub_one {m p : ℕ} (hp : 0 < p) {k : Edge m → ℕ} (hk : ValidDeg m p k)
    (hm : 1 ≤ m) :
    (fullEdges p k).card ≠ m - 1 := by
  intro hcard
  have hrem_card : (Finset.univ \ coveredVerts p k).card = 2 := by
    have hadd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (coveredVerts p k))
    rw [Finset.card_univ, Fintype.card_fin, card_coveredVerts hp hk, hcard] at hadd
    omega
  obtain ⟨u, w, huw, hrem_eq⟩ := Finset.card_eq_two.mp hrem_card
  -- Order the two uncovered vertices as `a < b`
  have hu_mem : u ∈ Finset.univ \ coveredVerts p k := by rw [hrem_eq]; simp
  have hw_mem : w ∈ Finset.univ \ coveredVerts p k := by rw [hrem_eq]; simp
  let a : Fin (2 * m) := if u < w then u else w
  let b : Fin (2 * m) := if u < w then w else u
  have hab : a < b := by
    dsimp [a, b]
    split_ifs with h
    · exact h
    · exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm huw)
  let eStar : Edge m := ⟨(a, b), hab⟩
  have ha_uncov : a ∉ coveredVerts p k := by
    dsimp [a]; split_ifs
    · exact (Finset.mem_sdiff.mp hu_mem).2
    · exact (Finset.mem_sdiff.mp hw_mem).2
  have hb_uncov : b ∉ coveredVerts p k := by
    dsimp [b]; split_ifs
    · exact (Finset.mem_sdiff.mp hw_mem).2
    · exact (Finset.mem_sdiff.mp hu_mem).2
  -- Any edge `e` incident to a covered vertex `v` that is not in `fullEdges p k` has `k e = 0`
  have hzero_of_cov : ∀ e : Edge m, ∀ v : Fin (2 * m),
      v ∈ coveredVerts p k → incident v e → e ∉ fullEdges p k → k e = 0 := by
    intro e v hv hve he_not
    obtain ⟨e₀, he₀, hve₀⟩ := Finset.mem_biUnion.mp hv
    have hne : e ≠ e₀ := fun h => he_not (h ▸ he₀)
    have h1 : k e₀ = p := (Finset.mem_filter.mp he₀).2
    have hve₀' : incident v e₀ := by simpa [incident] using hve₀
    have hle : ∑ e' ∈ ({e, e₀} : Finset (Edge m)), (if incident v e' then k e' else 0) ≤
        ∑ e' : Edge m, (if incident v e' then k e' else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hne, hk v] at hle
    simp only [hve, hve₀', ↓reduceIte, h1] at hle
    omega
  -- Every edge incident to `a` other than `eStar` has `k e = 0`
  have hsum_a : (∑ e : Edge m, if incident a e then k e else 0) = k eStar := by
    rw [Finset.sum_eq_single eStar]
    · simp [eStar, incident]
    · intro e _ hne
      by_cases hae : incident a e
      · simp only [hae, ↓reduceIte]
        have he_not : e ∉ fullEdges p k := by
          intro hmem
          apply ha_uncov
          exact Finset.mem_biUnion.mpr ⟨e, hmem, by simpa [incident] using hae⟩
        -- The other endpoint `v` of `e` is not `a` and not `b`, so `v ∈ coveredVerts p k`
        rcases hae with ha1 | ha2
        · have hv_ne_a : e.1.2 ≠ a := (ne_of_lt (ha1 ▸ e.2) : a ≠ e.1.2).symm
          have hv_ne_b : e.1.2 ≠ b := by
            intro h
            apply hne
            exact Subtype.ext (Prod.ext ha1.symm h)
          have hv_cov : e.1.2 ∈ coveredVerts p k := by
            by_contra hnot
            have hmem : e.1.2 ∈ Finset.univ \ coveredVerts p k :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
            rw [hrem_eq] at hmem
            simp only [mem_insert, mem_singleton] at hmem
            dsimp [a, b] at hv_ne_a hv_ne_b
            split_ifs at hv_ne_a hv_ne_b <;> rcases hmem with h | h <;> contradiction
          exact hzero_of_cov e e.1.2 hv_cov (Or.inr rfl) he_not
        · have hv_ne_a : e.1.1 ≠ a := ne_of_lt (ha2 ▸ e.2)
          have hv_ne_b : e.1.1 ≠ b := by
            intro h
            have : b < a := h ▸ ha2 ▸ e.2
            exact lt_asymm hab this
          have hv_cov : e.1.1 ∈ coveredVerts p k := by
            by_contra hnot
            have hmem : e.1.1 ∈ Finset.univ \ coveredVerts p k :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
            rw [hrem_eq] at hmem
            simp only [mem_insert, mem_singleton] at hmem
            dsimp [a, b] at hv_ne_a hv_ne_b
            split_ifs at hv_ne_a hv_ne_b <;> rcases hmem with h | h <;> contradiction
          exact hzero_of_cov e e.1.1 hv_cov (Or.inl rfl) he_not
      · simp [hae]
    · intro h; exact absurd (Finset.mem_univ eStar) h
  have keStar : k eStar = p := by
    rw [← hsum_a, hk a]
  have heStar_mem : eStar ∈ fullEdges p k := Finset.mem_filter.mpr ⟨Finset.mem_univ _, keStar⟩
  apply ha_uncov
  exact Finset.mem_biUnion.mpr ⟨eStar, heStar_mem, by simp [eStar]⟩

lemma prime_pow_dvd_mul_factorial (p m : ℕ) (hp : 0 < p) : p ^ m ∣ (m * p)! := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h1 : (m * p)! * ((m + 1) * p) ∣ ((m + 1) * p)! := by
        cases p with
        | zero => omega
        | succ p' =>
            have hlt : m * (p' + 1) < (m + 1) * (p' + 1) := by nlinarith
            have hle : m * (p' + 1) ≤ (m + 1) * (p' + 1) - 1 := by omega
            have hfac := Nat.factorial_dvd_factorial hle
            have hmul := Nat.mul_dvd_mul_right hfac ((m + 1) * (p' + 1))
            have hsucc : ((m + 1) * (p' + 1) - 1)! * ((m + 1) * (p' + 1)) =
                ((m + 1) * (p' + 1))! := by
              have hN : ((m + 1) * (p' + 1) - 1 + 1) = ((m + 1) * (p' + 1)) :=
                Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos p')))
              rw [← hN, Nat.factorial_succ, mul_comm]
              congr 1
            have hpos' : 1 ≤ (m + 1) * (p' + 1) :=
              Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos p'))
            simpa [hsucc, Nat.sub_add_cancel hpos', Nat.succ_eq_add_one] using hmul
      have h2 : p ^ m * p ∣ (m * p)! * ((m + 1) * p) :=
        Nat.mul_dvd_mul ih (dvd_mul_left p (m + 1))
      rw [pow_succ]
      exact dvd_trans h2 h1

lemma padicValNat_prod {α : Type*} [Fintype α] (p : ℕ) [Fact p.Prime]
    (f : α → ℕ) (hf : ∀ a, f a ≠ 0) :
    padicValNat p (∏ a, f a) = ∑ a, padicValNat p (f a) := by
  classical
  induction (Finset.univ : Finset α) using Finset.induction_on with
  | empty => simp [padicValNat_def]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have h1 : f a ≠ 0 := hf a
      have h2 : (∏ x ∈ s, f x) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun b _ => hf b)
      simp only [padicValNat_def] at ih ⊢
      rw [Nat.multiplicity_mul h1 h2]
      rw [ih]

lemma dvd_multinomial_of_nonMatching {m p : ℕ} (hp : p.Prime) {k : Edge m → ℕ}
    (hk : ValidDeg m p k) (hnon : (fullEdges p k).card ≠ m) :
    p ^ 2 ∣ Nat.multinomial Finset.univ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hm_ge : 2 ≤ m := by
    have hle := card_fullEdges_le hp.pos hk
    by_cases hm0 : m = 0
    · omega
    · have hm1 : 1 ≤ m := by omega
      have hne := card_fullEdges_ne_sub_one hp.pos hk hm1
      omega
  have hle_m2 : (fullEdges p k).card ≤ m - 2 := by
    have hle := card_fullEdges_le hp.pos hk
    have hne := card_fullEdges_ne_sub_one hp.pos hk (by omega)
    omega
  have hspec := Nat.multinomial_spec Finset.univ k
  rw [validDeg_sum hk] at hspec
  have hprod_ne : (∏ e : Edge m, (k e)!) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun e _ => Nat.factorial_ne_zero (k e))
  have hmult_ne : Nat.multinomial Finset.univ k ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hspec
    exact Nat.factorial_ne_zero (m * p) hspec.symm
  have hval_eq :
      padicValNat p (∏ e : Edge m, (k e)!) + padicValNat p (Nat.multinomial Finset.univ k) =
      padicValNat p (m * p)! := by
    rw [padicValNat_def, padicValNat_def, padicValNat_def]
    rw [← padicValNat.mul hprod_ne hmult_ne, hspec]
  have hval_mp : m ≤ padicValNat p (m * p)! := by
    rw [padicValNat_def]
    exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero (m * p))).mp
      (prime_pow_dvd_mul_factorial p m hp.pos)
  have hval_prod : padicValNat p (∏ e : Edge m, (k e)!) = (fullEdges p k).card := by
    rw [padicValNat_prod p (fun e => (k e)!) (fun e => Nat.factorial_ne_zero (k e))]
    calc
      ∑ e : Edge m, padicValNat p (k e)!
          = ∑ e : Edge m, if k e = p then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro e _
              by_cases hke : k e = p
              · rw [if_pos hke, hke]
                have hd1 : p ^ 1 ∣ p ! := by simpa using Nat.dvd_factorial hp.pos le_rfl
                have hnd2 : ¬ p ^ 2 ∣ p ! := by
                  rw [pow_two]
                  intro hd
                  have hfac : p * (p - 1)! = p ! := Nat.mul_factorial_pred hp.pos.ne'
                  rw [← hfac] at hd
                  have hd' : p ∣ (p - 1)! := Nat.dvd_of_mul_dvd_mul_left hp.pos hd
                  have := hp.dvd_factorial.mp hd'
                  have hp2 : 2 ≤ p := hp.two_le
                  omega
                have hge1 : 1 ≤ padicValNat p p ! := by
                  rw [padicValNat_def]
                  exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero p)).mp hd1
                have hlt2 : padicValNat p p ! < 2 := by
                  rw [padicValNat_def]
                  by_contra hge2
                  exact hnd2 ((padicValNat_dvd_iff_le (Nat.factorial_ne_zero p)).mpr (not_lt.mp hge2))
                omega
              · rw [if_neg hke]
                have hlt : k e < p := lt_of_le_of_ne (validDeg_le_n hk e) hke
                rw [padicValNat_def]
                exact multiplicity_eq_zero_of_not_dvd (fun hd => by
                  have := hp.dvd_factorial.mp hd; omega)
      _ = (fullEdges p k).card := by
            simp [fullEdges, Finset.sum_boole]
  have hge2 : 2 ≤ padicValNat p (Nat.multinomial Finset.univ k) := by
    have h1 : padicValNat p (∏ e : Edge m, (k e)!) ≤ m - 2 := by
      rw [hval_prod]
      exact hle_m2
    have h2 : padicValNat p (∏ e : Edge m, (k e)!) +
        padicValNat p (Nat.multinomial Finset.univ k) = padicValNat p (m * p)! := hval_eq
    have h3 : m ≤ padicValNat p (m * p)! := hval_mp
    omega
  rw [padicValNat_def] at hge2
  exact (padicValNat_dvd_iff_le hmult_ne).mpr hge2

/-! ### Part 4: Counting Perfect Matchings of `K_{2m}` and Main Theorem -/

lemma multinomial_of_perfectMatching {m p : ℕ} (hp : 0 < p) {k : Edge m → ℕ}
    (hk : ValidDeg m p k) (hpm : (fullEdges p k).card = m) :
    Nat.multinomial Finset.univ k = ∏ j ∈ Icc 1 m, (j * p).choose p := by
  have hother_zero : ∀ e : Edge m, e ∉ fullEdges p k → k e = 0 := by
    intro e he
    have hsum : ∑ e' : Edge m, k e' = m * p := validDeg_sum hk
    have hfull_sum : ∑ e' ∈ fullEdges p k, k e' = m * p := by
      calc
        ∑ e' ∈ fullEdges p k, k e' = ∑ _e' ∈ fullEdges p k, p := by
            apply Finset.sum_congr rfl
            intro e' he'; exact (Finset.mem_filter.mp he').2
        _ = m * p := by rw [Finset.sum_const, smul_eq_mul, hpm]
    have hsplit : (∑ e' ∈ fullEdges p k, k e') + (∑ e' ∈ Finset.univ \ fullEdges p k, k e') =
        ∑ e' : Edge m, k e' := by
      rw [add_comm]
      exact Finset.sum_sdiff (Finset.subset_univ _)
    have hzero_sum : ∑ e' ∈ Finset.univ \ fullEdges p k, k e' = 0 := by omega
    exact Finset.sum_eq_zero_iff.mp hzero_sum e (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he⟩)
  have hprod_fac : (∏ e : Edge m, (k e)!) = (p !) ^ m := by
    rw [← Finset.prod_sdiff (Finset.subset_univ (fullEdges p k))]
    have h1 : ∏ e ∈ Finset.univ \ fullEdges p k, (k e)! = 1 := by
      apply Finset.prod_eq_one
      intro e he
      rw [hother_zero e (Finset.mem_sdiff.mp he).2, Nat.factorial_zero]
    have h2 : ∏ e ∈ fullEdges p k, (k e)! = (p !) ^ m := by
      calc
        ∏ e ∈ fullEdges p k, (k e)! = ∏ _e ∈ fullEdges p k, p ! := by
            apply Finset.prod_congr rfl
            intro e he; rw [(Finset.mem_filter.mp he).2]
        _ = (p !) ^ m := by rw [Finset.prod_const, hpm]
    rw [h1, h2, one_mul]
  have hspec := Nat.multinomial_spec Finset.univ k
  rw [validDeg_sum hk, hprod_fac] at hspec
  have hprod_eq := prod_choose_mul_prime_eq m p
  have hpos : 0 < (p !) ^ m := pow_pos (Nat.factorial_pos p) m
  exact Nat.eq_of_mul_eq_mul_left hpos (hspec.trans hprod_eq.symm)

/-- Perfect matchings of `Fin (2 * m)`, represented as sets of `m` pairwise-disjoint edges
covering all `2 * m` vertices. -/
def IsPerfectMatching (m : ℕ) (S : Finset (Edge m)) : Prop :=
  S.card = m ∧ ∀ v : Fin (2 * m), ∃! e ∈ S, incident v e

noncomputable instance (m : ℕ) (S : Finset (Edge m)) : Decidable (IsPerfectMatching m S) :=
  Classical.dec _

lemma card_perfectMatchings_mul (m : ℕ) :
    (Finset.univ.filter (IsPerfectMatching m)).card * m ! * 2 ^ m = (2 * m)! := by
  induction m with
  | zero =>
      have h1 : (Finset.univ.filter (IsPerfectMatching 0)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨∅, ?_⟩
        ext S
        simp only [mem_filter, mem_univ, true_and, mem_singleton, IsPerfectMatching]
        constructor
        · intro h; exact Finset.card_eq_zero.mp h.1
        · rintro rfl; exact ⟨rfl, fun v => Fin.elim0 v⟩
      simp [h1]
  | succ m ih =>
      -- Pair vertex `0 : Fin (2 * m + 2)` with one of the `2 * m + 1` other vertices `j ≠ 0`
      let partners : Finset (Fin (2 * (m + 1))) := Finset.univ.erase 0
      have hpart_card : partners.card = 2 * m + 1 := by
        simp [partners] <;> omega
      have hrec : (Finset.univ.filter (IsPerfectMatching (m + 1))).card =
          (2 * m + 1) * (Finset.univ.filter (IsPerfectMatching m)).card := by
        -- Partition matchings of `K_{2m+2}` by the unique partner `j` of vertex `0`
        have hsum : (Finset.univ.filter (IsPerfectMatching (m + 1))).card =
            ∑ j ∈ partners,
              (Finset.univ.filter fun S : Finset (Edge (m + 1)) =>
                IsPerfectMatching (m + 1) S ∧
                ∃ h0j : (0 : Fin (2 * (m + 1))) < j, (⟨(0, j), h0j⟩ : Edge (m + 1)) ∈ S).card := by
          rw [← Finset.card_biUnion]
          · congr 1
            ext S
            simp only [mem_filter, mem_univ, true_and, mem_biUnion, partners, mem_erase]
            constructor
            · intro hS
              obtain ⟨e, ⟨heS, h0e⟩, _⟩ := hS.2 0
              have he1 : e.1.1 = 0 := by
                rcases h0e with h1 | h2
                · exact h1.symm
                · exfalso; have := e.2; rw [← h2] at this; exact Fin.not_lt_zero _ this
              have h0j : (0 : Fin (2 * (m + 1))) < e.1.2 := he1 ▸ e.2
              refine ⟨e.1.2, by simp [ne_of_gt h0j], hS, h0j, ?_⟩
              have heq : (⟨(0, e.1.2), h0j⟩ : Edge (m + 1)) = e :=
                Subtype.ext (Prod.ext he1.symm rfl)
              rwa [heq]
            · rintro ⟨_, _, hS, _, _⟩; exact hS
          · intro j₁ _ j₂ _ hne
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro S hS₁ hS₂
            simp only [mem_filter] at hS₁ hS₂
            obtain ⟨h01, he₁⟩ := hS₁.2.2
            obtain ⟨h02, he₂⟩ := hS₂.2.2
            obtain ⟨e, _, huniq⟩ := hS₁.2.1.2 0
            have h1 := huniq ⟨(0, j₁), h01⟩ ⟨he₁, Or.inl rfl⟩
            have h2 := huniq ⟨(0, j₂), h02⟩ ⟨he₂, Or.inl rfl⟩
            have h12 := h1.trans h2.symm
            exact hne (congr_arg (fun x : Edge (m + 1) => x.1.2) h12)
        rw [hsum]
        have heach : ∀ j ∈ partners,
            (Finset.univ.filter fun S : Finset (Edge (m + 1)) =>
              IsPerfectMatching (m + 1) S ∧
              ∃ h0j : (0 : Fin (2 * (m + 1))) < j, (⟨(0, j), h0j⟩ : Edge (m + 1)) ∈ S).card =
            (Finset.univ.filter (IsPerfectMatching m)).card := by
          intro j hj
          have hj0 : (0 : Fin (2 * (m + 1))) < j :=
            Fin.pos_of_ne_zero (Finset.mem_erase.mp hj).1
          let e0j : Edge (m + 1) := ⟨(0, j), hj0⟩
          -- Order-preserving bijection `Fin (2 * m) ≃o {v : Fin (2 * m + 2) // v ≠ 0 ∧ v ≠ j}`
          let rem : Finset (Fin (2 * (m + 1))) := (Finset.univ.erase 0).erase j
          have hrem_card : rem.card = 2 * m := by
            have hj_mem : j ∈ Finset.univ.erase (0 : Fin (2 * (m + 1))) := hj
            rw [Finset.card_erase_of_mem hj_mem, Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_univ, Fintype.card_fin]
            omega
          let φrem : Fin (2 * m) ≃o rem := rem.orderIsoOfFin hrem_card
          let embEdge : Edge m → Edge (m + 1) := fun e =>
            ⟨((φrem e.1.1).1, (φrem e.1.2).1), φrem.strictMono e.2⟩
          have hemb_inj : Function.Injective embEdge := by
            intro e₁ e₂ h
            have h1 : (φrem e₁.1.1).1 = (φrem e₂.1.1).1 := congr_arg (fun x : Edge (m + 1) => x.1.1) h
            have h2 : (φrem e₁.1.2).1 = (φrem e₂.1.2).1 := congr_arg (fun x : Edge (m + 1) => x.1.2) h
            exact Subtype.ext (Prod.ext (φrem.injective (Subtype.ext h1)) (φrem.injective (Subtype.ext h2)))
          have hemb_ne : ∀ e : Edge m, embEdge e ≠ e0j := by
            intro e h
            have h1 : (φrem e.1.1).1 = 0 := congr_arg (fun x : Edge (m + 1) => x.1.1) h
            have hmem := (φrem e.1.1).2
            simp only [rem, mem_erase] at hmem
            exact hmem.2.1 h1
          symm
          refine Finset.card_bij (fun T _ => insert e0j (T.image embEdge)) ?_ ?_ ?_
          · intro T hT
            simp only [mem_filter, mem_univ, true_and] at hT ⊢
            refine ⟨⟨?_, ?_⟩, ⟨hj0, Finset.mem_insert_self _ _⟩⟩
            · rw [Finset.card_insert_of_notMem (by simp [hemb_ne]),
                Finset.card_image_of_injective _ hemb_inj, hT.1]
            · intro v
              by_cases hv0 : v = 0
              · subst hv0
                refine ⟨e0j, ⟨Finset.mem_insert_self _ _, Or.inl rfl⟩, ?_⟩
                rintro e ⟨he, hv⟩
                rcases Finset.mem_insert.mp he with rfl | himg
                · rfl
                · rcases Finset.mem_image.mp himg with ⟨e', _, rfl⟩
                  exfalso
                  rcases hv with h1 | h2
                  · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (φrem e'.1.1).2).2).1 h1.symm
                  · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (φrem e'.1.2).2).2).1 h2.symm
              · by_cases hvj : v = j
                · subst hvj
                  refine ⟨e0j, ⟨Finset.mem_insert_self _ _, Or.inr rfl⟩, ?_⟩
                  rintro e ⟨he, hv⟩
                  rcases Finset.mem_insert.mp he with rfl | himg
                  · rfl
                  · rcases Finset.mem_image.mp himg with ⟨e', _, rfl⟩
                    exfalso
                    rcases hv with h1 | h2
                    · exact (Finset.mem_erase.mp (φrem e'.1.1).2).1 h1.symm
                    · exact (Finset.mem_erase.mp (φrem e'.1.2).2).1 h2.symm
                · have hvrem : v ∈ rem := by simp [rem, hv0, hvj]
                  set u : Fin (2 * m) := φrem.symm ⟨v, hvrem⟩
                  have hφremu : (φrem u).1 = v := by simp [u]
                  obtain ⟨e', ⟨he'T, hue'⟩, huniq⟩ := hT.2 u
                  refine ⟨embEdge e', ⟨Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ he'T), ?_⟩, ?_⟩
                  · rcases hue' with h1 | h2
                    · exact Or.inl (by rw [← hφremu, h1])
                    · exact Or.inr (by rw [← hφremu, h2])
                  · rintro e ⟨he, hve⟩
                    rcases Finset.mem_insert.mp he with rfl | himg
                    · exfalso; rcases hve with h1 | h2 <;> contradiction
                    · rcases Finset.mem_image.mp himg with ⟨e₂, he₂T, rfl⟩
                      congr 1
                      apply huniq e₂
                      refine ⟨he₂T, ?_⟩
                      rcases hve with h1 | h2
                      · exact Or.inl (φrem.injective (Subtype.ext (hφremu.trans h1)))
                      · exact Or.inr (φrem.injective (Subtype.ext (hφremu.trans h2)))
          · intro T₁ _ T₂ _ heq
            have h1 : T₁.image embEdge = T₂.image embEdge := by
              have h := congr_arg (fun S => S.erase e0j) heq
              have h1 : e0j ∉ T₁.image embEdge := by
                intro hmem
                rcases Finset.mem_image.mp hmem with ⟨e, _, he⟩
                exact hemb_ne e he
              have h2 : e0j ∉ T₂.image embEdge := by
                intro hmem
                rcases Finset.mem_image.mp hmem with ⟨e, _, he⟩
                exact hemb_ne e he
              simpa [Finset.erase_eq_of_notMem h1, Finset.erase_eq_of_notMem h2] using h
            exact Finset.image_injective hemb_inj h1
          · intro S hS
            simp only [mem_filter, mem_univ, true_and] at hS
            obtain ⟨hpmS, _, he0jS⟩ := hS
            -- Pull back `S.erase e0j` along `embEdge`
            have hall_rem : ∀ e ∈ S.erase e0j, e.1.1 ∈ rem ∧ e.1.2 ∈ rem := by
              intro e he
              have heS : e ∈ S := (Finset.mem_erase.mp he).2
              have hene : e ≠ e0j := (Finset.mem_erase.mp he).1
              have hne01 : e.1.1 ≠ 0 := by
                intro h
                obtain ⟨_, _, huniq⟩ := hpmS.2 0
                exact hene ((huniq e ⟨heS, Or.inl h.symm⟩).trans (huniq e0j ⟨he0jS, Or.inl rfl⟩).symm)
              have hne02 : e.1.2 ≠ 0 := by
                intro h
                obtain ⟨_, _, huniq⟩ := hpmS.2 0
                exact hene ((huniq e ⟨heS, Or.inr h.symm⟩).trans (huniq e0j ⟨he0jS, Or.inl rfl⟩).symm)
              have hnej1 : e.1.1 ≠ j := by
                intro h
                obtain ⟨_, _, huniq⟩ := hpmS.2 j
                exact hene ((huniq e ⟨heS, Or.inl h.symm⟩).trans (huniq e0j ⟨he0jS, Or.inr rfl⟩).symm)
              have hnej2 : e.1.2 ≠ j := by
                intro h
                obtain ⟨_, _, huniq⟩ := hpmS.2 j
                exact hene ((huniq e ⟨heS, Or.inr h.symm⟩).trans (huniq e0j ⟨he0jS, Or.inr rfl⟩).symm)
              exact ⟨by simp [rem, hne01, hnej1], by simp [rem, hne02, hnej2]⟩
            let T : Finset (Edge m) := Finset.univ.filter fun e => embEdge e ∈ S.erase e0j
            have hTimg : T.image embEdge = S.erase e0j := by
              ext e
              simp only [Finset.mem_image, T, mem_filter, mem_univ, true_and]
              constructor
              · rintro ⟨e', he', rfl⟩; exact he'
              · intro he
                obtain ⟨h1, h2⟩ := hall_rem e he
                refine ⟨⟨(φrem.symm ⟨e.1.1, h1⟩, φrem.symm ⟨e.1.2, h2⟩), ?_⟩, ?_, ?_⟩
                · exact φrem.symm.strictMono e.2
                · convert he using 1; ext <;> simp [embEdge]
                · ext <;> simp [embEdge]
            refine ⟨T, ?_, ?_⟩
            · simp only [mem_filter, mem_univ, true_and]
              refine ⟨?_, ?_⟩
              · have hcard := congr_arg Finset.card hTimg
                rw [Finset.card_image_of_injective _ hemb_inj,
                  Finset.card_erase_of_mem he0jS, hpmS.1] at hcard
                omega
              · intro u
                obtain ⟨e, ⟨heS, hve⟩, huniq⟩ := hpmS.2 (φrem u).1
                have hene : e ≠ e0j := by
                  rintro rfl
                  rcases hve with h1 | h2
                  · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (φrem u).2).2).1 h1
                  · exact (Finset.mem_erase.mp (φrem u).2).1 h2
                have he_er : e ∈ S.erase e0j := Finset.mem_erase.mpr ⟨hene, heS⟩
                rw [← hTimg] at he_er
                rcases Finset.mem_image.mp he_er with ⟨e', he'T, rfl⟩
                refine ⟨e', ⟨he'T, ?_⟩, ?_⟩
                · rcases hve with h1 | h2
                  · exact Or.inl (φrem.injective (Subtype.ext h1))
                  · exact Or.inr (φrem.injective (Subtype.ext h2))
                · rintro e₂ ⟨he₂T, hue₂⟩
                  have he₂S : embEdge e₂ ∈ S :=
                    (Finset.mem_erase.mp (hTimg ▸ Finset.mem_image_of_mem embEdge he₂T)).2
                  have hv₂ : incident (φrem u).1 (embEdge e₂) := by
                    rcases hue₂ with h1 | h2
                    · exact Or.inl (by rw [h1])
                    · exact Or.inr (by rw [h2])
                  exact hemb_inj ((huniq (embEdge e₂) ⟨he₂S, hv₂⟩).trans
                    (huniq (embEdge e') ⟨heS, hve⟩).symm)
            · rw [hTimg, Finset.insert_erase he0jS]
        rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul, hpart_card]
      rw [hrec]
      calc
        (2 * m + 1) * (Finset.univ.filter (IsPerfectMatching m)).card * (m + 1)! * 2 ^ (m + 1)
            = (2 * m + 2) * (2 * m + 1) *
                ((Finset.univ.filter (IsPerfectMatching m)).card * m ! * 2 ^ m) := by
                rw [Nat.factorial_succ, pow_succ]; ring
        _ = (2 * m + 2) * (2 * m + 1) * (2 * m)! := by rw [ih]
        _ = (2 * (m + 1))! := by
              have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
              rw [h1, Nat.factorial_succ, Nat.factorial_succ]
              ring

lemma card_perfectMatching_validDegs (m p : ℕ) (hp : 0 < p) :
    ((boundedDegs m p).filter (fun k => ValidDeg m p k ∧ (fullEdges p k).card = m)).card =
    (Finset.univ.filter (IsPerfectMatching m)).card := by
  refine Finset.card_bij (fun k _ => fullEdges p k) ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    obtain ⟨_, hvd, hcard⟩ := hk
    refine ⟨hcard, fun v => ?_⟩
    have hcov : coveredVerts p k = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [card_coveredVerts hp hvd, hcard, Fintype.card_fin]
    have hv : v ∈ coveredVerts p k := hcov ▸ Finset.mem_univ v
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    refine ⟨e, ⟨he, by simpa [incident] using hve⟩, ?_⟩
    rintro e' ⟨he', hve'⟩
    by_contra hne
    exact fullEdges_disjoint_endpoints hp hvd he' he hne v hve' (by simpa [incident] using hve)
  · intro k₁ hk₁ k₂ hk₂ heq
    simp only [mem_filter] at hk₁ hk₂
    have hzero : ∀ (k : Edge m → ℕ), ValidDeg m p k → (fullEdges p k).card = m →
        ∀ e, e ∉ fullEdges p k → k e = 0 := by
      intro k hk hcard e he
      have hsum : ∑ e' : Edge m, k e' = m * p := validDeg_sum hk
      have hfull_sum : ∑ e' ∈ fullEdges p k, k e' = m * p := by
        calc
          ∑ e' ∈ fullEdges p k, k e' = ∑ _e' ∈ fullEdges p k, p := by
              apply Finset.sum_congr rfl; intro e' he'; exact (Finset.mem_filter.mp he').2
          _ = m * p := by rw [Finset.sum_const, smul_eq_mul, hcard]
      have hsplit : (∑ e' ∈ fullEdges p k, k e') + (∑ e' ∈ Finset.univ \ fullEdges p k, k e') =
          ∑ e' : Edge m, k e' := by
        rw [add_comm]
        exact Finset.sum_sdiff (Finset.subset_univ _)
      have hzero_sum : ∑ e' ∈ Finset.univ \ fullEdges p k, k e' = 0 := by omega
      exact Finset.sum_eq_zero_iff.mp hzero_sum e (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he⟩)
    ext e
    by_cases h1 : e ∈ fullEdges p k₁
    · have h2 : e ∈ fullEdges p k₂ := heq ▸ h1
      rw [(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2]
    · have h2 : e ∉ fullEdges p k₂ := heq ▸ h1
      rw [hzero k₁ hk₁.2.1 hk₁.2.2 e h1, hzero k₂ hk₂.2.1 hk₂.2.2 e h2]
  · intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    let k : Edge m → ℕ := fun e => if e ∈ S then p else 0
    have hvd : ValidDeg m p k := by
      intro v
      obtain ⟨e₀, ⟨he₀S, hve₀⟩, huniq⟩ := hS.2 v
      rw [Finset.sum_eq_single e₀]
      · simp [k, he₀S, hve₀]
      · intro e _ hne
        by_cases hve : incident v e
        · by_cases heS : e ∈ S
          · exact absurd (huniq e ⟨heS, hve⟩) hne
          · simp [k, heS]
        · simp [hve]
      · intro h; exact absurd (Finset.mem_univ e₀) h
    have hfe : fullEdges p k = S := by
      ext e
      simp only [fullEdges, mem_filter, mem_univ, true_and, k]
      by_cases he : e ∈ S
      · simp [he]
      · simp [he]
        exact fun h => hp.ne' h.symm
    refine ⟨k, ?_, hfe⟩
    simp only [mem_filter]
    exact ⟨mem_boundedDegs_of_valid hvd, hvd, hfe ▸ hS.1⟩

/-- **Main General Theorem**: For every `m ≥ 0` and every prime `p`, the number `a_m(p)` of
`(mp) × (2m)` 0-1 arrays with row sums `2` and column sums `p` satisfies
`a_m(p) ≡ (2m)! / 2^m [MOD p^2]`. -/
theorem aArray_prime_mod_sq (m p : ℕ) (hp : p.Prime) :
    aArray m p ≡ (2 * m)! / 2 ^ m [MOD p ^ 2] := by
  rw [aArray_eq_sum_multinomial]
  let S_all := (boundedDegs m p).filter (ValidDeg m p)
  let S_pm := S_all.filter fun k => (fullEdges p k).card = m
  let S_non := S_all.filter fun k => (fullEdges p k).card ≠ m
  have hsplit : ∑ k ∈ S_all, Nat.multinomial Finset.univ k =
      (∑ k ∈ S_pm, Nat.multinomial Finset.univ k) +
      (∑ k ∈ S_non, Nat.multinomial Finset.univ k) :=
    (Finset.sum_filter_add_sum_filter_not S_all (fun k => (fullEdges p k).card = m) _).symm
  rw [hsplit]
  have hnon_mod : ∑ k ∈ S_non, Nat.multinomial Finset.univ k ≡ 0 [MOD p ^ 2] := by
    rw [Nat.modEq_zero_iff_dvd]
    apply Finset.dvd_sum
    intro k hk
    simp only [S_non, S_all, mem_filter] at hk
    exact dvd_multinomial_of_nonMatching hp hk.1.2 hk.2
  have hpm_eq : ∑ k ∈ S_pm, Nat.multinomial Finset.univ k =
      (Finset.univ.filter (IsPerfectMatching m)).card * (∏ j ∈ Icc 1 m, (j * p).choose p) := by
    have heach : ∀ k ∈ S_pm,
        Nat.multinomial Finset.univ k = ∏ j ∈ Icc 1 m, (j * p).choose p := by
      intro k hk
      simp only [S_pm, S_all, mem_filter] at hk
      exact multinomial_of_perfectMatching hp.pos hk.1.2 hk.2
    rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul]
    congr 1
    have hSpm : S_pm = (boundedDegs m p).filter (fun k => ValidDeg m p k ∧ (fullEdges p k).card = m) := by
      ext k; simp [S_pm, S_all, and_assoc]
    rw [hSpm, card_perfectMatching_validDegs m p hp.pos]
  have htarget : (Finset.univ.filter (IsPerfectMatching m)).card * m ! = (2 * m)! / 2 ^ m := by
    have hmul := card_perfectMatchings_mul m
    rw [← hmul, Nat.mul_div_cancel _ (pow_pos (by omega) m)]
  have hpm_mod : ∑ k ∈ S_pm, Nat.multinomial Finset.univ k ≡ (2 * m)! / 2 ^ m [MOD p ^ 2] := by
    rw [hpm_eq, ← htarget]
    exact (prod_choose_mul_prime_mod_sq hp m).mul_left _
  simpa [add_zero] using hpm_mod.add hnon_mod

/-- **OEIS A172572 Conjecture 1** (Peter Bala, Oct 28, 2024):
For every prime `p`, the number of `3p × 6` 0-1 arrays with row sums `2` and column sums `p`
satisfies `a(p) ≡ 90 [MOD p^2]`. -/
theorem oeis_A172572_conj1 (p : ℕ) (hp : p.Prime) :
    aArray 3 p ≡ 90 [MOD p ^ 2] := by
  have h := aArray_prime_mod_sq 3 p hp
  norm_num at h
  exact h

end OEIS_A172572
