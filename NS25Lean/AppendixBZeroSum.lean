import NS25Lean.AppendixBReduced

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A

/-- The source definition: positive elements indecomposable into two positive elements. -/
def minimalPositiveGenerators (S : AddSubmonoid ℕ) : Set ℕ :=
  {r | r ∈ S ∧ 0 < r ∧ ¬ ∃ x y, x ∈ S ∧ y ∈ S ∧ 0 < x ∧ 0 < y ∧ r = x + y}

/-- Partial sums modulo `w` give a proper positive divisible block and complement. -/
theorem positive_divisible_partition (S : AddSubmonoid ℕ) (w N : ℕ) (t : ℕ → ℕ)
    (hw : 0 < w) (hN : w < N)
    (ht : ∀ k < N, t k ∈ S ∧ 0 < t k)
    (hs : w ∣ ∑ k ∈ Finset.range N, t k) :
    ∃ x y : ℕ, x ∈ S ∧ y ∈ S ∧ 0 < x ∧ 0 < y ∧ w ∣ x ∧ w ∣ y ∧
      (∑ k ∈ Finset.range N, t k) = x + y := by
  classical
  let p (n : ℕ) := ∑ k ∈ Finset.range n, t k
  let f : Fin (w + 1) → Fin w := fun i => ⟨p i % w, Nat.mod_lt _ hw⟩
  obtain ⟨i, j, hij, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have hiN : i.val < N := by omega
  have hjN : j.val < N := by omega
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hmod : p i.val % w = p j.val % w := congrArg Fin.val he
  suffices hp : ∀ i j : ℕ, i < j → j < N → p i % w = p j % w →
      ∃ x y : ℕ, x ∈ S ∧ y ∈ S ∧ 0 < x ∧ 0 < y ∧ w ∣ x ∧ w ∣ y ∧
        p N = x + y by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hp i.val j.val hlt hjN hmod
    · exact hp j.val i.val hlt hiN hmod.symm
  intro i j hij hjN hmod
  let block := Finset.range j \ Finset.range i
  let rest := Finset.range N \ block
  have hsub : block ⊆ Finset.range N := by
    intro k hk
    exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp (Finset.mem_sdiff.mp hk).1) hjN)
  have hbi : i ∈ block := by simp [block, hij]
  have hrj : j ∈ rest := by simp [rest, block, hjN]
  have hbmem : ∀ k ∈ block, t k ∈ S := fun k hk => (ht k (Finset.mem_range.mp (hsub hk))).1
  have hrmem : ∀ k ∈ rest, t k ∈ S := fun k hk =>
    (ht k (Finset.mem_range.mp (Finset.mem_sdiff.mp hk).1)).1
  have hbpos : 0 < ∑ k ∈ block, t k := Finset.sum_pos
    (fun k hk => (ht k (Finset.mem_range.mp (hsub hk))).2) ⟨i, hbi⟩
  have hrpos : 0 < ∑ k ∈ rest, t k := Finset.sum_pos
    (fun k hk => (ht k (Finset.mem_range.mp (Finset.mem_sdiff.mp hk).1)).2) ⟨j, hrj⟩
  have hprefix : (∑ k ∈ block, t k) + p i = p j :=
    Finset.sum_sdiff (Finset.range_mono hij.le)
  have hbdiv : w ∣ ∑ k ∈ block, t k := by
    have hd : w ∣ p j - p i := Nat.ModEq.dvd' hmod
    have he : p j - p i = ∑ k ∈ block, t k := by omega
    exact he ▸ hd
  have hsum : (∑ k ∈ rest, t k) + (∑ k ∈ block, t k) = p N :=
    Finset.sum_sdiff hsub
  have hrdiv : w ∣ ∑ k ∈ rest, t k :=
    (Nat.dvd_add_left hbdiv).mp (by rw [hsum]; exact hs)
  exact ⟨_, _, S.sum_mem hbmem, S.sum_mem hrmem, hbpos, hrpos, hbdiv, hrdiv, by omega⟩

/-- The paper's sequence of `b` copies of `a`, followed by `w-a` copies of `b`. -/
theorem zero_sum_exclusion_lt (a b w : ℕ) (ha : 0 < a) (hab : a < b) (haw : a < w) :
    b ∉ minimalPositiveGenerators (twoQuotient a b w) := by
  classical
  let t : ℕ → ℕ := fun k => if k < b then a else b
  have hN : w < b + (w - a) := by omega
  have ht : ∀ k < b + (w - a), t k ∈ twoGenerator a b ∧ 0 < t k := by
    intro k hk
    dsimp [t]
    split_ifs
    · exact ⟨(mem_twoGenerator a b a).mpr ⟨1, 0, by ring⟩, ha⟩
    · exact ⟨(mem_twoGenerator a b b).mpr ⟨0, 1, by ring⟩, by omega⟩
  have hsum : (∑ k ∈ Finset.range (b + (w - a)), t k) = w * b := by
    rw [Finset.sum_range_add]
    have hfirst : (∑ k ∈ Finset.range b, t k) = b * a := by
      calc
        _ = ∑ _k ∈ Finset.range b, a := Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))
        _ = _ := by simp
    have hsecond : (∑ k ∈ Finset.range (w - a), t (b + k)) = (w - a) * b := by
      calc
        _ = ∑ _k ∈ Finset.range (w - a), b := Finset.sum_congr rfl (fun k _ => if_neg (by omega))
        _ = _ := by simp
    rw [hfirst, hsecond]
    have hw : w - a + a = w := Nat.sub_add_cancel haw.le
    nlinarith
  obtain ⟨x, y, hx, hy, hxpos, hypos, hdx, hdy, he⟩ :=
    positive_divisible_partition (twoGenerator a b) w _ t (by omega) hN ht
      (by rw [hsum]; exact dvd_mul_right w b)
  obtain ⟨r, hr⟩ := hdx
  obtain ⟨s, hs⟩ := hdy
  intro hb
  apply hb.2.2
  refine ⟨r, s, ?_, ?_, ?_, ?_, ?_⟩
  · change w * r ∈ twoGenerator a b
    rw [← hr]; exact hx
  · change w * s ∈ twoGenerator a b
    rw [← hs]; exact hy
  · nlinarith
  · nlinarith
  · rw [hsum, hr, hs] at he
    nlinarith

theorem twoQuotient_comm (a b w : ℕ) : twoQuotient a b w = twoQuotient b a w := by
  ext r
  simp only [mem_twoQuotient, mem_twoGenerator]
  constructor <;> rintro ⟨R, S, he⟩ <;> exact ⟨S, R, by omega⟩

theorem zero_sum_exclusion_gt (a b w : ℕ) (hb : 0 < b) (hba : b < a) (hbw : b < w) :
    a ∉ minimalPositiveGenerators (twoQuotient a b w) := by
  rw [twoQuotient_comm]
  exact zero_sum_exclusion_lt b a w hb hba hbw

/-- A positive minimal generator divisible by a positive member must equal that member. -/
theorem minimal_generator_eq_of_dvd (S : AddSubmonoid ℕ) (b r : ℕ)
    (hb : b ∈ S) (hbpos : 0 < b) (hr : r ∈ minimalPositiveGenerators S) (hd : b ∣ r) :
    r = b := by
  obtain ⟨k, hk⟩ := hd
  have hkpos : 0 < k := by nlinarith [hr.2.1]
  by_contra hne
  have hkbig : 1 < k := by
    by_contra hn
    have he : k = 1 := by omega
    exact hne (by simpa [he] using hk)
  apply hr.2.2
  refine ⟨b, (k - 1) * b, hb, ?_, hbpos, ?_, ?_⟩
  · simpa using S.nsmul_mem hb (k - 1)
  · exact Nat.mul_pos (by omega) hbpos
  · have he : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    nlinarith

theorem minimal_generator_not_dvd (S : AddSubmonoid ℕ) (b r : ℕ)
    (hb : b ∈ S) (hbpos : 0 < b) (hbn : b ∉ minimalPositiveGenerators S)
    (hr : r ∈ minimalPositiveGenerators S) : ¬ b ∣ r := by
  intro hd
  exact hbn ((minimal_generator_eq_of_dvd S b r hb hbpos hr hd) ▸ hr)

end NS25Lean.L4A
