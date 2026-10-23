import NS25Lean.P3CommonArmR59

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R60
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2B4AR1
variable {Gamma : NumericalSemigroup}

/-- The actual normalized tail Apéry representative of the physical return q*m. -/
def returnPoint (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) : ℤ :=
  physicalAlpha B e ((q * B.q.val : ℕ) : ZMod (routingA B e))

/-- The exact signed defect, before restricting to a nonprincipal positive level. -/
def returnDefect (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) : ℤ :=
  (returnPoint B e q - (q : ℤ)*B.q.val) / routingA B e

def CanonicalValue (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (x : ℤ) : Prop :=
  physicalAlpha B e (x : ZMod (routingA B e)) = x

theorem return_point_defect_eq (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) :
    returnPoint B e q = (q : ℤ)*B.q.val + returnDefect B e q*routingA B e := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hmod : (returnPoint B e q : ZMod (routingA B e)) =
      (((q : ℤ)*B.q.val : ℤ) : ZMod (routingA B e)) := by
    simpa [returnPoint, physicalAlpha] using
      (routingH B e).asRelativeIdeal.aperyRepresentative_mod (routingA B e)
        ((q * B.q.val : ℕ) : ZMod (routingA B e))
  have hdvd : (routingA B e : ℤ) ∣ returnPoint B e q - (q : ℤ)*B.q.val :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hmod.symm
  have he := Int.ediv_mul_cancel hdvd
  change (returnPoint B e q - (q : ℤ)*B.q.val) / routingA B e * routingA B e =
    returnPoint B e q - (q : ℤ)*B.q.val at he
  change returnDefect B e q * routingA B e = returnPoint B e q - (q : ℤ)*B.q.val at he
  omega

theorem canonical_grid_value (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ)
    (hc : IsCanonicalTailGridPoint B e i j) :
    CanonicalValue B e ((i : ℤ)*routingB B e+j*routingC B e) := by
  change (normalizedGrid B e 0 i j : ℤ) = physicalAlpha B e (gridResidue B e i j) at hc
  dsimp only [CanonicalValue]
  have hres : (((i : ℤ)*routingB B e+j*routingC B e : ℤ) : ZMod (routingA B e)) =
      gridResidue B e i j := by
    simp only [gridResidue, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rw [hres]
  simpa only [normalizedGrid, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul] using hc.symm

theorem lshape_canonical_stencil (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (i j : ℕ)
    (hi : i < criticalExponent M.base (e 1))
    (hj : j < criticalExponent M.base (e 2))
    (hcorner : i < P3R57.roleCoefficient M hp e 0 1 ∨
      j < P3R57.roleCoefficient M hp e 0 2) (hip : 0 < i) (hjp : 0 < j) :
    let x := (i : ℤ)*routingB M.base e+j*routingC M.base e
    CanonicalValue M.base e x ∧
    CanonicalValue M.base e (x-routingB M.base e) ∧
    CanonicalValue M.base e (x-routingC M.base e) ∧
    CanonicalValue M.base e (x-routingB M.base e-routingC M.base e) := by
  dsimp only
  have h0 := canonical_grid_value M.base e i j
    (P3R58.p3_lshape_canonical M hp e i j hi hj hcorner)
  have hb := canonical_grid_value M.base e (i-1) j
    (P3R58.p3_lshape_canonical M hp e (i-1) j (by omega) hj
      (by rcases hcorner with h | h <;> omega))
  have hc := canonical_grid_value M.base e i (j-1)
    (P3R58.p3_lshape_canonical M hp e i (j-1) hi (by omega)
      (by rcases hcorner with h | h <;> omega))
  have hbc := canonical_grid_value M.base e (i-1) (j-1)
    (P3R58.p3_lshape_canonical M hp e (i-1) (j-1) (by omega) (by omega)
      (by rcases hcorner with h | h <;> omega))
  have hib : ((i-1 : ℕ) : ℤ)*routingB M.base e+j*routingC M.base e =
      (i : ℤ)*routingB M.base e+j*routingC M.base e-routingB M.base e := by
    rw [Nat.cast_sub (by omega : 1 ≤ i)]; push_cast; ring
  have hjc : (i : ℤ)*routingB M.base e+((j-1 : ℕ) : ℤ)*routingC M.base e =
      (i : ℤ)*routingB M.base e+j*routingC M.base e-routingC M.base e := by
    rw [Nat.cast_sub (by omega : 1 ≤ j)]; push_cast; ring
  have hij : ((i-1 : ℕ) : ℤ)*routingB M.base e+((j-1 : ℕ) : ℤ)*routingC M.base e =
      (i : ℤ)*routingB M.base e+j*routingC M.base e-routingB M.base e-routingC M.base e := by
    rw [Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_sub (by omega : 1 ≤ j)]; push_cast; ring
  exact ⟨h0, hib ▸ hb, hjc ▸ hc, hij ▸ hbc⟩

theorem return_point_eq_of_canonical (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (x d : ℤ) (hcan : CanonicalValue B e x)
    (he : x = (q : ℤ)*B.q.val+d*routingA B e) :
    returnPoint B e q = x ∧ returnDefect B e q = d := by
  have hmod : (x : ZMod (routingA B e)) =
      ((q*B.q.val : ℕ) : ZMod (routingA B e)) := by
    rw [he]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
      ZMod.natCast_self, mul_zero, add_zero]
  have hx : returnPoint B e q = x := by
    change physicalAlpha B e _ = x
    rw [← hmod]; exact hcan
  refine ⟨hx, ?_⟩
  have hspec := return_point_defect_eq B e q
  rw [hx, he] at hspec
  have ha : (0 : ℤ)<routingA B e := by exact_mod_cast routingA_pos B e
  nlinarith

theorem nonprincipal_canonical_stencil (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery)
    (q : ℕ) (hq : 0<q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) :
    0 < returnDefect M.base e q ∧
    returnDefect M.base e q < criticalExponent M.base (e 0) ∧
    CanonicalValue M.base e (returnPoint M.base e q) ∧
    CanonicalValue M.base e (returnPoint M.base e q-routingB M.base e) ∧
    CanonicalValue M.base e (returnPoint M.base e q-routingC M.base e) ∧
    CanonicalValue M.base e (returnPoint M.base e q-routingB M.base e-routingC M.base e) := by
  have hs := P3R58.p3_coefficient_sums M hp e
  rcases hs with ⟨h1,h2,h3⟩
  have hU := P3R58.p3_coefficients_positive M hp e 1 0 (by decide)
  have hW := P3R58.p3_coefficients_positive M hp e 2 0 (by decide)
  rcases P3R59.canonical_nonprincipal_return M hp e hlive q hq hpre with hRB | hLT
  · rcases hRB with ⟨s,t,d,hsp,hsl,htp,htl,hdp,hdl,he⟩
    have hst := lshape_canonical_stencil M hp e
      (P3R57.roleCoefficient M hp e 0 1+s) t (by omega) (by omega)
      (Or.inr htl) (by omega) htp
    obtain ⟨hb,hd⟩ := return_point_eq_of_canonical M.base e q _ d hst.1 he
    rw [hb, hd]
    exact ⟨by exact_mod_cast hdp, by exact_mod_cast (show d<criticalExponent M.base (e 0) by omega), hst⟩
  · rcases hLT with ⟨s,t,d,hsp,hsl,htp,htl,hdp,hdl,he⟩
    have hst := lshape_canonical_stencil M hp e
      s (P3R57.roleCoefficient M hp e 0 2+t) (by omega) (by omega)
      (Or.inl hsl) hsp (by omega)
    obtain ⟨hb,hd⟩ := return_point_eq_of_canonical M.base e q _ d hst.1 he
    rw [hb, hd]
    exact ⟨by exact_mod_cast hdp, by exact_mod_cast (show d<criticalExponent M.base (e 0) by omega), hst⟩

theorem gate_canonical_stencil (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) :
    let g := (criticalExponent M.base (e 0) : ℤ)*routingA M.base e
    CanonicalValue M.base e (g-routingB M.base e) ∧
    CanonicalValue M.base e (g-routingC M.base e) ∧
    CanonicalValue M.base e (g-routingB M.base e-routingC M.base e) := by
  dsimp only
  let P := P3R57.roleCoefficient M hp e 0 1
  let Q := P3R57.roleCoefficient M hp e 0 2
  have hP : 0 < P := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hQ : 0 < Q := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hZ := P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  have hV := P3R58.p3_coefficients_positive M hp e 1 2 (by decide)
  obtain ⟨_,h2,h3⟩ := P3R58.p3_coefficient_sums M hp e
  have hrel : (criticalExponent M.base (e 0) : ℤ)*routingA M.base e =
      (P : ℤ)*routingB M.base e+Q*routingC M.base e := by
    exact_mod_cast (L5A2C4OR5.coherent_normalized_relations M.base e
      (P3R58.p3_coherentHerzogData M hp e)).1
  have hb := canonical_grid_value M.base e (P-1) Q
    (P3R58.p3_lshape_canonical M hp e (P-1) Q
      (by dsimp [P]; omega) (by dsimp [Q]; omega)
      (Or.inl (by change P-1<P; omega)))
  have hc := canonical_grid_value M.base e P (Q-1)
    (P3R58.p3_lshape_canonical M hp e P (Q-1)
      (by dsimp [P]; omega) (by dsimp [Q]; omega)
      (Or.inr (by change Q-1<Q; omega)))
  have hbc := canonical_grid_value M.base e (P-1) (Q-1)
    (P3R58.p3_lshape_canonical M hp e (P-1) (Q-1)
      (by dsimp [P]; omega) (by dsimp [Q]; omega)
      (Or.inl (by change P-1<P; omega)))
  have hbEq : ((P-1 : ℕ) : ℤ)*routingB M.base e+Q*routingC M.base e =
      (criticalExponent M.base (e 0) : ℤ)*routingA M.base e-routingB M.base e := by
    rw [Nat.cast_sub (by omega : 1 ≤ P)]; norm_num only [Nat.cast_one]; nlinarith only [hrel]
  have hcEq : (P : ℤ)*routingB M.base e+((Q-1 : ℕ) : ℤ)*routingC M.base e =
      (criticalExponent M.base (e 0) : ℤ)*routingA M.base e-routingC M.base e := by
    rw [Nat.cast_sub (by omega : 1 ≤ Q)]; norm_num only [Nat.cast_one]; nlinarith only [hrel]
  have hbcEq : ((P-1 : ℕ) : ℤ)*routingB M.base e+((Q-1 : ℕ) : ℤ)*routingC M.base e =
      (criticalExponent M.base (e 0) : ℤ)*routingA M.base e-routingB M.base e-routingC M.base e := by
    rw [Nat.cast_sub (by omega : 1 ≤ P), Nat.cast_sub (by omega : 1 ≤ Q)]
    norm_num only [Nat.cast_one]; nlinarith only [hrel]
  exact ⟨hbEq ▸ hb, hcEq ▸ hc, hbcEq ▸ hbc⟩

end NS25Lean.P3R60
