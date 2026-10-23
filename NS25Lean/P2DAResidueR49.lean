import NS25Lean.P2DAMonomializationR49
import NS25Lean.P2SectorYFinalClosure

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2R49
open ChosenBase L2B L5A1 MvPolynomial
variable {Gamma : NumericalSemigroup}

theorem boundary_of_positive_shift (B : Data Gamma) (u : Fin 3 →₀ ℕ)
    (d ell : ℕ) (hell : 1 ≤ ell) (he : d = weight B u + ell * B.q.val)
    (hdH : d ∈ B.H) : d ∈ B.K := by
  refine ⟨hdH, ?_, ?_⟩
  · have := B.q_positive
    nlinarith
  · have hm : weight B u + (ell - 1) * B.q.val ∈ Gamma.toAddSubmonoid :=
      Gamma.toAddSubmonoid.add_mem (B.H_le (L3C.weight_mem_H B u))
        (by simpa [nsmul_eq_mul] using Gamma.toAddSubmonoid.nsmul_mem B.q.property (ell - 1))
    have he' : d - B.q.val = weight B u + (ell - 1) * B.q.val := by
      have : ell * B.q.val = (ell - 1) * B.q.val + B.q.val := by
        calc
          ell * B.q.val = (ell - 1 + 1) * B.q.val :=
            congrArg (fun n => n * B.q.val) (Nat.sub_add_cancel hell).symm
          _ = (ell - 1) * B.q.val + B.q.val := by rw [Nat.add_mul, one_mul]
      omega
    rwa [he']

theorem minimal_boundary_decomposition (k : Type*) [Field k] (B : Data Gamma)
    (u : Fin 3 →₀ ℕ) (hu : u ∈ L3A.minimalExponents (B.J k)) :
    ∃ v : Fin 3 →₀ ℕ, ∃ ell : ℕ,
      weight B v ∈ B.apery ∧ 1 ≤ ell ∧ weight B u = weight B v + ell * B.q.val := by
  have huk := (monomial_mem_chosen_iff_boundary k B u).mp hu.1
  obtain ⟨d, hd, ell, he⟩ := L3C.apery_decomposition B (weight B u) (B.H_le huk.1)
  obtain ⟨v⟩ := fiber_nonempty B ⟨d, (B.apery_eq_compl ▸ hd).1⟩
  refine ⟨v.val, ell, v.property.symm ▸ hd, ?_, ?_⟩
  · by_contra hn
    have hell : ell = 0 := by omega
    have heq : weight B u = d := by simpa [hell] using he
    exact (B.apery_eq_compl ▸ hd).2 (heq ▸ huk)
  · simpa only [v.property] using he

/-- SUP for actual divisibility-minimal border monomials, without an endpoint premise. -/
theorem minimal_boundary_support_complement (k : Type*) [Field k] (B : Data Gamma)
    (u v : Fin 3 →₀ ℕ) (hu : u ∈ L3A.minimalExponents (B.J k))
    (ell : ℕ) (hell : 1 ≤ ell)
    (he : weight B u = weight B v + ell * B.q.val)
    (j : Fin 3) (huj : 0 < u j) : v j = 0 := by
  by_contra hn
  have hvj : 0 < v j := Nat.pos_of_ne_zero hn
  have hustd := minimal_predecessor_standard k B hu j huj
  have hua := (standard_iff_chosen_apery k B _).mp hustd
  have heu := L3B.removed_weight B _ (⟨u, rfl⟩ : FactorizationFiber B (weight B u)) j huj
  have hev := L3B.removed_weight B _ (⟨v, rfl⟩ : FactorizationFiber B (weight B v)) j hvj
  have hk := boundary_of_positive_shift B (v - Finsupp.single j 1)
    (weight B (u - Finsupp.single j 1)) ell hell (by dsimp at heu hev; omega)
    (B.apery_eq_compl ▸ hua).1
  exact (B.apery_eq_compl ▸ hua).2 hk

theorem standard_residue_unique_of_apery_unique (k : Type*) [Field k] (B : Data Gamma)
    (hu : ∀ d, d ∈ B.apery → Subsingleton (FactorizationFiber B d))
    {u v : Fin 3 →₀ ℕ}
    (hus : u ∈ L3A.standardExponents (B.J k))
    (hvs : v ∈ L3A.standardExponents (B.J k))
    (hr : Nat.ModEq B.q.val (weight B u) (weight B v)) : u = v := by
  have hua := (standard_iff_chosen_apery k B u).mp hus
  have hva := (standard_iff_chosen_apery k B v).mp hvs
  have he := apery_mod_unique B hua hva hr
  exact congrArg Subtype.val ((hu _ hua).elim ⟨u, rfl⟩ ⟨v, he.symm⟩)

theorem full_support_residue_zero (k : Type*) [Field k] (B : Data Gamma)
    (g : Fin 3 →₀ ℕ) (hg : g ∈ L3A.fullSupportGenerators (B.J k)) :
    Nat.ModEq B.q.val (weight B g) 0 := by
  obtain ⟨v, ell, _, hell, he⟩ := minimal_boundary_decomposition k B g hg.1
  have hv : v = 0 := by
    ext j
    exact minimal_boundary_support_complement k B g v hg.1 ell hell he j (hg.2 j)
  simp only [hv, map_zero, zero_add] at he
  rw [he]
  simp [Nat.ModEq]

/-- A pure residue-zero minimal border and a fully-supported minimal border
cannot coexist once actual Apéry factorizations are unique. -/
theorem pure_residue_zero_excludes_full_support (k : Type*) [Field k] (B : Data Gamma)
    (hu : ∀ d, d ∈ B.apery → Subsingleton (FactorizationFiber B d))
    (i : Fin 3) (a : ℕ) (ha : 0 < a)
    (hmin : Finsupp.single i a ∈ L3A.minimalExponents (B.J k))
    (hr : Nat.ModEq B.q.val (weight B (Finsupp.single i a)) 0)
    (g : Fin 3 →₀ ℕ) (hg : g ∈ L3A.fullSupportGenerators (B.J k)) : False := by
  let u : Fin 3 →₀ ℕ := Finsupp.single i a
  let e : Fin 3 →₀ ℕ := Finsupp.single i 1
  have heu : e ≤ u := Finsupp.single_le_iff.mpr (by dsimp [u]; simp; omega)
  have heg : e ≤ g := Finsupp.single_le_iff.mpr (hg.2 i)
  have hui : 0 < u i := by simpa [u] using ha
  have hus := minimal_predecessor_standard k B hmin i hui
  have hgs := minimal_predecessor_standard k B hg.1 i (hg.2 i)
  have hgu : Nat.ModEq B.q.val (weight B g) (weight B u) :=
    (full_support_residue_zero k B g hg).trans hr.symm
  have hgw : weight B (g - e) + weight B e = weight B g := by
    rw [← map_add, tsub_add_cancel_of_le heg]
  have huw : weight B (u - e) + weight B e = weight B u := by
    rw [← map_add, tsub_add_cancel_of_le heu]
  have hres := Nat.ModEq.sub (by omega : weight B e ≤ weight B g)
    (by omega : weight B e ≤ weight B u) hgu (Nat.ModEq.rfl : Nat.ModEq B.q.val _ _)
  have he : g - e = u - e := standard_residue_unique_of_apery_unique k B hu hgs hus (by
    have he1 : weight B (g - e) = weight B g - weight B e := by omega
    have he2 : weight B (u - e) = weight B u - weight B e := by omega
    rwa [he1, he2])
  have hge : g = u := by
    have := congrArg (fun w => w + e) he
    simpa only [tsub_add_cancel_of_le heg, tsub_add_cancel_of_le heu] using this
  let j : Fin 3 := if i = 0 then 1 else 0
  have hji : j ≠ i := by
    dsimp [j]
    split_ifs with hi
    · subst i; decide
    · simpa [Ne.symm hi]
  have hz : u j = 0 := by simp [u, Finsupp.single_eq_of_ne hji]
  have hp := hg.2 j
  rw [hge, hz] at hp
  omega

end NS25Lean.L5A2R49
