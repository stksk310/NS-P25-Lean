import NS25Lean.DilationSemigroup

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase FourGeneratedBridge
variable {Gamma : NumericalSemigroup}

/-- Guarded form of the exact integer boundary equivalence; no truncated-subtraction shortcut. -/
theorem dilation_boundary_iff (B : Data Gamma) (D : ℕ) (hD : 0 < D)
    (hcop : Nat.Coprime D B.q.val) (h : ℕ) :
    (B.q.val ≤ D * h ∧ D * h - B.q.val ∈ dilatedMonoid B D) ↔
      (B.q.val ≤ h ∧ h - B.q.val ∈ Gamma.toAddSubmonoid) := by
  constructor
  · rintro ⟨hq, r, g, hg, he⟩
    have heq : D * h = (r + 1) * B.q.val + D * g := by
      simp only [Nat.add_mul, one_mul]
      omega
    have hdprod : D ∣ (r + 1) * B.q.val := by
      have hh := Nat.dvd_sub (dvd_mul_right D h) (dvd_mul_right D g)
      have he' : D * h - D * g = (r + 1) * B.q.val := by omega
      exact he' ▸ hh
    obtain ⟨l, hl⟩ := hcop.dvd_of_dvd_mul_right hdprod
    have hlpos : 0 < l := by
      by_contra hn
      have he : l = 0 := by omega
      simp [he] at hl
    have hcancel : h = l * B.q.val + g := by
      apply Nat.eq_of_mul_eq_mul_left hD
      calc
        D * h = (r + 1) * B.q.val + D * g := heq
        _ = D * (l * B.q.val + g) := by rw [hl]; ring
    have hql : B.q.val ≤ l * B.q.val := Nat.le_mul_of_pos_left _ hlpos
    refine ⟨by omega, ?_⟩
    have hg' := Gamma.toAddSubmonoid.add_mem
      (Gamma.toAddSubmonoid.nsmul_mem B.q.property (l - 1)) (B.H_le hg)
    have he' : h - B.q.val = (l - 1) * B.q.val + g := by
      rw [hcancel, Nat.sub_mul, one_mul]
      omega
    simpa [he', nsmul_eq_mul] using hg'
  · rintro ⟨hq, hh⟩
    obtain ⟨r, g, hg, he⟩ := B.generatedOver (h - B.q.val) hh
    have heq : h = (r + 1) * B.q.val + g := by
      simp only [Nat.add_mul, one_mul]
      omega
    have hDl : 1 ≤ D * (r + 1) := by nlinarith
    have he' : D * h = D * (r + 1) * B.q.val + D * g := by rw [heq]; ring
    have hq' : B.q.val ≤ D * h := by
      have : B.q.val ≤ D * (r + 1) * B.q.val := Nat.le_mul_of_pos_left _ hDl
      omega
    refine ⟨hq', D * (r + 1) - 1, g, hg, ?_⟩
    rw [Nat.sub_mul, one_mul]
    change D * h - B.q.val = D * (r + 1) * B.q.val - B.q.val + D * g
    have hprod : B.q.val ≤ D * (r + 1) * B.q.val := Nat.le_mul_of_pos_left _ hDl
    omega

def scaleHom (D : ℕ) : ℕ →+ ℕ where
  toFun n := D * n
  map_zero' := by simp
  map_add' := Nat.mul_add D

def dilatedTail (B : Data Gamma) (D : ℕ) : AddSubmonoid ℕ := B.H.map (scaleHom D)

theorem mem_dilatedTail (B : Data Gamma) (D : ℕ) (hD : 0 < D) (h : ℕ) :
    D * h ∈ dilatedTail B D ↔ h ∈ B.H := by
  constructor
  · rintro ⟨g, hg, he⟩
    have : g = h := Nat.eq_of_mul_eq_mul_left hD he
    exact this ▸ hg
  · intro hh; exact ⟨h, hh, rfl⟩

theorem dilation_K_iff (B : Data Gamma) (D : ℕ) (hD : 0 < D)
    (hcop : Nat.Coprime D B.q.val) (h : ℕ) :
    D * h ∈ aperyTail (dilatedMonoid B D) (dilatedTail B D) B.q.val ↔ h ∈ B.K := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [mem_dilatedTail B D hD, dilation_boundary_iff B D hD hcop]

def tailScaleEquiv (B : Data Gamma) (D : ℕ) (hD : 0 < D) : B.H ≃+ dilatedTail B D where
  toFun h := ⟨D * h.val, (mem_dilatedTail B D hD h.val).mpr h.property⟩
  invFun h := ⟨Classical.choose h.property, (Classical.choose_spec h.property).1⟩
  left_inv h := by
    apply Subtype.ext
    exact Nat.eq_of_mul_eq_mul_left hD (Classical.choose_spec
      ((mem_dilatedTail B D hD h.val).mpr h.property)).2
  right_inv h := by
    apply Subtype.ext
    exact (Classical.choose_spec h.property).2
  map_add' a b := by apply Subtype.ext; exact Nat.mul_add D _ _

end NS25Lean.L2B
