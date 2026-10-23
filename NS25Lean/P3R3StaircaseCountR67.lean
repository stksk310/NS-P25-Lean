import NS25Lean.P3R3AntichainR67
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

/-- TW.10/NF.10: a rectangular FINAL floor antichain contributes its staircase
and an actual occupied corner. Only TOTAL UM is counted. -/
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
  let a := routingA M.base e
  let b := routingB M.base e
  let c := routingC M.base e
  let n := (coordinateMinima S).card
  have hn : 0<n := Finset.card_pos.mpr (coordinate_minima_nonempty S hS)
  obtain ⟨f,hf,hmono,hanti⟩ := coordinate_minima_enumeration S
  have fmem : ∀ k : Fin n, f k ∈ coordinateMinima S := by
    intro k
    change f k ∈ (coordinateMinima S : Set (ℕ × ℕ))
    rw [← hf]
    exact ⟨k,rfl⟩
  have fbounds : ∀ k : Fin n, 0<(f k).1 ∧ (f k).1<Imax ∧ 0<(f k).2 ∧ (f k).2<Jmax := by
    intro k
    exact hbounds _ ((mem_coordinateMinima S _).mp (fmem k)).1
  let prev : Fin (n-1) → Fin n := fun k => ⟨k.val,by omega⟩
  let next : Fin (n-1) → Fin n := fun k => ⟨k.val+1,by omega⟩
  let px : Fin (n-1) → ℕ := fun k => (f (next k)).1-1
  let py : Fin (n-1) → ℕ := fun k => (f (prev k)).2-1
  let base : Fin (n-1) → ZMod a := fun k => (((px k : ℤ)*b+py k*c : ℤ) : ZMod a)
  have hxy : ∀ k, px k+1<Imax ∧ py k+1<Jmax := by
    intro k
    have h1 := fbounds (next k)
    have h2 := fbounds (prev k)
    dsimp only [px,py]
    omega
  have can : ∀ i j, i<Imax → j<Jmax → IsCanonicalTailGridPoint M.base e i j := by
    intro i j hi hj
    exact P3R58.p3_lshape_canonical M hp e i j (by omega) (by omega)
      (by rcases hrect with h | h <;> omega)
  have hbase : ∀ k, ResidueData.ExactUnusedMergeReverseBase (routingData M.base e) (base k) := by
    intro k
    have hxyk := hxy k
    have hstep : prev k < next k := Nat.lt_succ_self k.val
    have hmx : (f (prev k)).1 < (f (next k)).1 := hmono hstep
    have hmy : (f (next k)).2 < (f (prev k)).2 := hanti hstep
    have hnext := fbounds (next k)
    have hprev := fbounds (prev k)
    have c0 := P3R60.canonical_grid_value M.base e (px k) (py k) (can _ _ (by omega) (by omega))
    have c1 := P3R60.canonical_grid_value M.base e (px k+1) (py k) (can _ _ (by omega) (by omega))
    have c2 := P3R60.canonical_grid_value M.base e (px k) (py k+1) (can _ _ (by omega) (by omega))
    have c3 := P3R60.canonical_grid_value M.base e (px k+1) (py k+1) (can _ _ (by omega) (by omega))
    have hnmem : (px k : ℤ)*b+py k*c ∉ routingI M.base e := by
      intro hm
      obtain ⟨p,hpS,hpx,hpy⟩ := (hfloor (px k) (py k) (by omega) (by omega)).mp hm
      obtain ⟨q,hq,hqx,hqy⟩ := coordinate_minima_cover S p hpS
      obtain ⟨l,hl⟩ := (show q ∈ Set.range f by rw [hf]; exact hq)
      have hd := adjacent_corner_not_dominates n f hmono hanti k l
      apply hd
      rw [hl]
      exact ⟨le_trans hqx hpx,le_trans hqy hpy⟩
    have east : ((px k+1 : ℕ) : ℤ)*b+py k*c ∈ routingI M.base e := by
      apply (hfloor _ _ (by omega) (by omega)).mpr
      refine ⟨f (next k),((mem_coordinateMinima S _).mp (fmem (next k))).1,?_,?_⟩ <;>
        dsimp only [px,py] <;> omega
    have north : (px k : ℤ)*b+((py k+1 : ℕ) : ℤ)*c ∈ routingI M.base e := by
      apply (hfloor _ _ (by omega) (by omega)).mpr
      refine ⟨f (prev k),((mem_coordinateMinima S _).mp (fmem (prev k))).1,?_,?_⟩ <;>
        dsimp only [px,py] <;> omega
    have ne : ((px k+1 : ℕ) : ℤ)*b+((py k+1 : ℕ) : ℤ)*c ∈ routingI M.base e := by
      apply (hfloor _ _ (by omega) (by omega)).mpr
      refine ⟨f (next k),((mem_coordinateMinima S _).mp (fmem (next k))).1,?_,?_⟩ <;>
        dsimp only [px,py] <;> omega
    have e1 : ((px k+1 : ℕ) : ℤ)*b+py k*c = (px k : ℤ)*b+py k*c+b := by push_cast; ring
    have e2 : (px k : ℤ)*b+((py k+1 : ℕ) : ℤ)*c = (px k : ℤ)*b+py k*c+c := by push_cast; ring
    have e3 : ((px k+1 : ℕ) : ℤ)*b+((py k+1 : ℕ) : ℤ)*c = (px k : ℤ)*b+py k*c+b+c := by push_cast; ring
    dsimp only [P3R60.CanonicalValue] at c0 c1 c2 c3
    rw [e1] at east c1
    rw [e2] at north c2
    rw [e3] at ne c3
    exact unused_merge_of_final_square (routingI M.base e) a b c (routingHB M.base e) (routingHC M.base e)
      (P3R63.routing_ideal_subset M.base e) _ c0 c1 c2 c3 hnmem east north ne
  have hinj : Function.Injective base := by
    intro k l he
    have heq := canonical_grid_residue_injective M hp e (px k) (py k) (px l) (py l)
      (by have := hxy k; omega) (by have := hxy k; omega)
      (can _ _ (by have := hxy k; omega) (by have := hxy k; omega))
      (can _ _ (by have := hxy l; omega) (by have := hxy l; omega)) he
    have h1 := fbounds (next k)
    have h2 := fbounds (next l)
    have hfst : (f (next k)).1=(f (next l)).1 := by dsimp only [px] at heq; omega
    have hi := hmono.injective hfst
    apply Fin.ext
    have := congrArg Fin.val hi
    dsimp only [next] at this
    omega
  have hIp : 0<Imax := by obtain ⟨p,hpS⟩ := hS; have := hbounds p hpS; omega
  have hcorcan := P3R58.p3_lshape_canonical M hp e (Imax-1) cj (by omega) hcj hcornercan
  have hdis : ∀ k, base k ≠ ((((Imax-1 : ℕ) : ℤ)*b+cj*c : ℤ) : ZMod a) := by
    intro k he
    have heq := canonical_grid_residue_injective M hp e (px k) (py k) (Imax-1) cj
      (by have := hxy k; omega) (by have := hxy k; omega)
      (can _ _ (by have := hxy k; omega) (by have := hxy k; omega)) hcorcan he
    have := hxy k
    omega
  refine ⟨base,hinj,hbase,hdis,?_⟩
  intro k
  have hstep : prev k < next k := Nat.lt_succ_self k.val
  exact ⟨f (prev k),((mem_coordinateMinima S _).mp (fmem (prev k))).1,
    f (next k),((mem_coordinateMinima S _).mp (fmem (next k))).1,
    hmono hstep,hanti hstep,rfl⟩

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
