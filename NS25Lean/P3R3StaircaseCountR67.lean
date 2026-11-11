import NS25Lean.P3R3AntichainR67
import NS25Lean.GenericFloorStaircase
import NS25Lean.GenericFloorSentinel
import NS25Lean.P3R3FloorR67

set_option autoImplicit false
set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open L5A2C4OR3 L5A2C4OR4 P3R61
variable {Gamma : NumericalSemigroup}

/-- Distinct actual canonical cells have distinct residue bases. -/
theorem canonical_grid_residue_injective (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3) (i j i' j' : ℕ)
    (hi : i<criticalExponent M.base (e 1)) (hj : j<criticalExponent M.base (e 2))
    (hc : IsCanonicalTailGridPoint M.base e i j)
    (hc' : IsCanonicalTailGridPoint M.base e i' j')
    (he : (((i : ℤ)*routingB M.base e+j*routingC M.base e : ℤ) : ZMod (routingA M.base e)) =
      (((i' : ℤ)*routingB M.base e+j'*routingC M.base e : ℤ) : ZMod (routingA M.base e))) :
    i=i' ∧ j=j' := by
  have h := P3R60.canonical_grid_value M.base e i j hc
  have h' := P3R60.canonical_grid_value M.base e i' j' hc'
  dsimp only [P3R60.CanonicalValue] at h h'
  have hw := h.symm.trans ((congrArg (physicalAlpha M.base e) he).trans h')
  exact subcritical_bc_factorization_unique M.base e i j i' j' hi hj hw

/-- D5 staircase for a floor antichain which may include a boundary
sentinel with first coordinate zero. Adjacent right points remain positive
by strict ordering, so every subtraction is justified. -/
theorem floor_staircase_family_with_zero_first_coordinate (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (Imax Jmax : ℕ) (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    (hI : Imax ≤ criticalExponent M.base (e 1))
    (hJ : Jmax ≤ criticalExponent M.base (e 2))
    (hrect : Imax ≤ P3R57.roleCoefficient M hp e 0 1 ∨ Jmax ≤ P3R57.roleCoefficient M hp e 0 2)
    (hbounds : ∀ p ∈ S, p.1<Imax ∧ 0<p.2 ∧ p.2<Jmax)
    (hfloor : ∀ i j, i<Imax → j<Jmax →
      ((i : ℤ)*routingB M.base e+j*routingC M.base e ∈ routingI M.base e ↔
        ∃ p ∈ S, p.1 ≤ i ∧ p.2 ≤ j))
 :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    ∃ base : Fin ((coordinateMinima S).card-1) → ZMod (routingA M.base e),
      Function.Injective base ∧
      (∀ k, ResidueData.ExactUnusedMergeReverseBase (routingData M.base e) (base k)) ∧
      (∀ k, ∃ p ∈ S, ∃ q ∈ S, p.1<q.1 ∧ q.2<p.2 ∧
        base k = ((((q.1-1 : ℕ) : ℤ)*routingB M.base e+((p.2-1 : ℕ) : ℤ)*routingC M.base e : ℤ) : ZMod (routingA M.base e))) := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  apply GenericFloorStaircase.floor_staircase_family (routingI M.base e)
    (routingA M.base e) (routingB M.base e) (routingC M.base e)
    (routingHB M.base e) (routingHC M.base e) (P3R63.routing_ideal_subset M.base e)
    Imax Jmax S hS ?_ ?_ (fun p hpS => ⟨(hbounds p hpS).1,(hbounds p hpS).2.2⟩) hfloor
  · intro i j hi hj
    exact P3R60.canonical_grid_value M.base e i j
      (P3R58.p3_lshape_canonical M hp e i j (by omega) (by omega)
        (by rcases hrect with h | h <;> omega))
  · intro i j i' j' hi hj hi' hj' he
    exact canonical_grid_residue_injective M hp e i j i' j' (by omega) (by omega)
      (P3R58.p3_lshape_canonical M hp e i j (by omega) (by omega)
        (by rcases hrect with h | h <;> omega))
      (P3R58.p3_lshape_canonical M hp e i' j' (by omega) (by omega)
        (by rcases hrect with h | h <;> omega)) he



/-- An exact final floor gives one total merge between each consecutive
minimal point, including a sentinel at coordinate zero. -/
theorem floor_staircase_unused_bound (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (Imax Jmax : ℕ) (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    (hI : Imax ≤ criticalExponent M.base (e 1))
    (hJ : Jmax ≤ criticalExponent M.base (e 2))
    (hrect : Imax ≤ P3R57.roleCoefficient M hp e 0 1 ∨ Jmax ≤ P3R57.roleCoefficient M hp e 0 2)
    (hbounds : ∀ p ∈ S, p.1<Imax ∧ 0<p.2 ∧ p.2<Jmax)
    (hfloor : ∀ i j, i<Imax → j<Jmax →
      ((i : ℤ)*routingB M.base e+j*routingC M.base e ∈ routingI M.base e ↔
        ∃ p ∈ S, p.1 ≤ i ∧ p.2 ≤ j)) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    (coordinateMinima S).card-1 ≤
      Nat.card (ResidueData.ExactUnusedMergeBases (routingData M.base e)) := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  obtain ⟨base,hinj,hmem,_⟩ := floor_staircase_family_with_zero_first_coordinate M hp e
    Imax Jmax S hS hI hJ hrect hbounds hfloor
  have hc := unused_count_of_injective_bases (routingData M.base e) base hinj hmem
  simpa only [Nat.card_fin] using hc

/-- Adding an incomparable zero-column sentinel to a floor antichain adds
exactly one minimum. The top boundary is counted without a freshness claim. -/
theorem coordinate_minima_insert_sentinel (E : Finset (ℕ × ℕ)) (k : ℕ)
    (hanti : ∀ p ∈ E, ∀ q ∈ E, q.1≤p.1 → q.2≤p.2 → p=q)
    (hsep : ∀ p ∈ E, 0<p.1 ∧ p.2<k) :
    coordinateMinima (insert (0,k) E)=insert (0,k) E :=
  GenericFloorStaircase.minima_insert_sentinel E k hanti hsep

/-- D5's sentinel count: k ordinary floor minima and one incomparable top
sentinel give k distinct total merges. Unit widths and k=0 are included. -/
theorem floor_staircase_sentinel_bound (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (Imax Jmax k : ℕ) (E : Finset (ℕ × ℕ))
    (hI : Imax ≤ criticalExponent M.base (e 1))
    (hJ : Jmax ≤ criticalExponent M.base (e 2))
    (hrect : Imax ≤ P3R57.roleCoefficient M hp e 0 1 ∨ Jmax ≤ P3R57.roleCoefficient M hp e 0 2)
    (hI0 : 0<Imax) (hk0 : 0<k) (hkJ : k<Jmax)
    (hanti : ∀ p ∈ E, ∀ q ∈ E, q.1≤p.1 → q.2≤p.2 → p=q)
    (hbounds : ∀ p ∈ E, 0<p.1 ∧ p.1<Imax ∧ 0<p.2 ∧ p.2<k)
    (hfloor : ∀ i j, i<Imax → j<Jmax →
      ((i : ℤ)*routingB M.base e+j*routingC M.base e ∈ routingI M.base e ↔
        ∃ p ∈ insert (0,k) E, p.1 ≤ i ∧ p.2 ≤ j)) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    E.card ≤ Nat.card (ResidueData.ExactUnusedMergeBases (routingData M.base e)) := by
  classical
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have hsep : ∀ p ∈ E, 0<p.1 ∧ p.2<k := by
    intro p hpE; exact ⟨(hbounds p hpE).1,(hbounds p hpE).2.2.2⟩
  have hc := floor_staircase_unused_bound M hp e Imax Jmax (insert (0,k) E)
    (Finset.insert_nonempty _ _) hI hJ hrect (by
      intro p hpS
      rcases Finset.mem_insert.mp hpS with rfl | hpE
      · exact ⟨hI0,hk0,hkJ⟩
      · have hh := hbounds p hpE
        exact ⟨hh.2.1,hh.2.2.1,by omega⟩) hfloor
  rw [coordinate_minima_insert_sentinel E k hanti hsep] at hc
  have hn : (0,k) ∉ E := by
    intro hm; have hh := hsep (0,k) hm; omega
  simpa only [Finset.card_insert_of_notMem hn, Nat.add_sub_cancel] using hc

theorem rectangular_staircase_merge_family (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (Imax Jmax : ℕ) (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    (hI : Imax ≤ criticalExponent M.base (e 1))
    (hJ : Jmax ≤ criticalExponent M.base (e 2))
    (hrect : Imax ≤ P3R57.roleCoefficient M hp e 0 1 ∨ Jmax ≤ P3R57.roleCoefficient M hp e 0 2)
    (hbounds : ∀ p ∈ S, 0<p.1 ∧ p.1<Imax ∧ 0<p.2 ∧ p.2<Jmax)
    (hfloor : ∀ i j, i<Imax → j<Jmax →
      ((i : ℤ)*routingB M.base e+j*routingC M.base e ∈ routingI M.base e ↔
        ∃ p ∈ S, p.1 ≤ i ∧ p.2 ≤ j))
    (cj : ℕ) (hcj : cj<criticalExponent M.base (e 2))
    (hcornercan : Imax-1<P3R57.roleCoefficient M hp e 0 1 ∨ cj<P3R57.roleCoefficient M hp e 0 2)
    (hcorner :
      letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
      ResidueData.ExactUnusedMergeReverseBase (routingData M.base e)
        ((((Imax-1 : ℕ) : ℤ)*routingB M.base e+cj*routingC M.base e : ℤ) : ZMod (routingA M.base e))) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    ∃ base : Fin ((coordinateMinima S).card-1) → ZMod (routingA M.base e),
      Function.Injective base ∧
      (∀ k, ResidueData.ExactUnusedMergeReverseBase (routingData M.base e) (base k)) ∧
      (∀ k, base k ≠ ((((Imax-1 : ℕ) : ℤ)*routingB M.base e+cj*routingC M.base e : ℤ) : ZMod (routingA M.base e))) ∧
      (∀ k, ∃ p ∈ S, ∃ q ∈ S, p.1<q.1 ∧ q.2<p.2 ∧
        base k = ((((q.1-1 : ℕ) : ℤ)*routingB M.base e+((p.2-1 : ℕ) : ℤ)*routingC M.base e : ℤ) : ZMod (routingA M.base e))) := by
  classical
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  obtain ⟨base,hinj,hbase,hgeom⟩ := floor_staircase_family_with_zero_first_coordinate M hp e
    Imax Jmax S hS hI hJ hrect
    (by intro p hpS; exact ⟨(hbounds p hpS).2.1,(hbounds p hpS).2.2⟩) hfloor
  have hIp : 0<Imax := by obtain ⟨p,hpS⟩ := hS; have := hbounds p hpS; omega
  have hcorcan := P3R58.p3_lshape_canonical M hp e (Imax-1) cj (by omega) hcj hcornercan
  refine ⟨base,hinj,hbase,?_,hgeom⟩
  intro k he
  obtain ⟨p,hpS,q,hqS,hpq,hqp,hval⟩ := hgeom k
  have hpB := hbounds p hpS
  have hqB := hbounds q hqS
  have hcell := P3R58.p3_lshape_canonical M hp e (q.1-1) (p.2-1)
    (by omega) (by omega) (by rcases hrect with h | h <;> omega)
  rw [hval] at he
  have heq := canonical_grid_residue_injective M hp e (q.1-1) (p.2-1) (Imax-1) cj
    (by omega) (by omega) hcell hcorcan he
  omega

/-- TW.10/NF.10: a rectangular FINAL floor antichain contributes its staircase
and an actual occupied corner. Only TOTAL UM is counted. -/
theorem rectangular_staircase_unused_bound (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (Imax Jmax : ℕ) (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    (hI : Imax ≤ criticalExponent M.base (e 1))
    (hJ : Jmax ≤ criticalExponent M.base (e 2))
    (hrect : Imax ≤ P3R57.roleCoefficient M hp e 0 1 ∨ Jmax ≤ P3R57.roleCoefficient M hp e 0 2)
    (hbounds : ∀ p ∈ S, 0<p.1 ∧ p.1<Imax ∧ 0<p.2 ∧ p.2<Jmax)
    (hfloor : ∀ i j, i<Imax → j<Jmax →
      ((i : ℤ)*routingB M.base e+j*routingC M.base e ∈ routingI M.base e ↔
        ∃ p ∈ S, p.1 ≤ i ∧ p.2 ≤ j))
    (cj : ℕ) (hcj : cj<criticalExponent M.base (e 2))
    (hcornercan : Imax-1<P3R57.roleCoefficient M hp e 0 1 ∨ cj<P3R57.roleCoefficient M hp e 0 2)
    (hcorner :
      letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
      ResidueData.ExactUnusedMergeReverseBase (routingData M.base e)
        ((((Imax-1 : ℕ) : ℤ)*routingB M.base e+cj*routingC M.base e : ℤ) : ZMod (routingA M.base e))) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    (coordinateMinima S).card ≤ Nat.card (ResidueData.ExactUnusedMergeBases (routingData M.base e)) := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  obtain ⟨base,hinj,hbase,hdis,_⟩ := rectangular_staircase_merge_family M hp e
    Imax Jmax S hS hI hJ hrect hbounds hfloor cj hcj hcornercan hcorner
  have hc := unused_count_with_corner (routingData M.base e) base hinj hbase _ hcorner hdis
  simp only [Nat.card_fin] at hc
  have hn : 0<(coordinateMinima S).card := Finset.card_pos.mpr (coordinate_minima_nonempty S hS)
  omega

end NS25Lean.P3R67
