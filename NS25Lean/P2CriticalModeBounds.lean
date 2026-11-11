import NS25Lean.P2CriticalShortFibers

set_option autoImplicit false
set_option linter.style.header false
namespace NS25Lean.CriticalModeBounds
open FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen PureInternalTransverse

/-- The coefficient bound in the positive presentation is a strict sum
identity; it is independent of any cap definition or count. -/
theorem positive_v_lt (L Q v : ℕ) (hQ : 0<Q) (hL : L=Q+v) : v<L := by omega

/-- In the pure-pair presentation, the live mixed predecessor forces the
strict coefficient bound. A failed bound would put it above the actual
killed pure-axis predecessor in the same cut. -/
theorem pure_pair_v_lt {H : NumericalSemigroup} (T : Triple H)
    (m R L u v : ℕ) (hR : 0<R) (hu : 0<u)
    (hpair : R*T.g 0=L*T.g 2)
    (hk : (R-1)*T.g 0∈cyclicCut H m)
    (hl : (u-1)*T.g 0+v*T.g 2∉cyclicCut H m) : v<L := by
  by_contra hn
  have hv : L≤v := by omega
  have hmem := cut_add H hk (T.member (vector u 0 (v-L)))
  have he : (R-1)*T.g 0+T.weight (vector u 0 (v-L))=
      (u-1)*T.g 0+v*T.g 2 := by
    rw [vector_weight,Triple.grid]
    have hR1 := congrArg (fun n => n*T.g 0) (Nat.sub_add_cancel hR)
    have hu1 := congrArg (fun n => n*T.g 0) (Nat.sub_add_cancel hu)
    have hv1 := congrArg (fun n => n*T.g 2) (Nat.sub_add_cancel hv)
    simp only [Nat.add_mul,one_mul] at hR1 hu1 hv1
    nlinarith only [hpair,hR1,hu1,hv1]
  exact hl (he ▸ hmem)

/-- A killed critical predecessor makes its actual critical degree cut;
the generator being added belongs to the same H. -/
theorem boundary_cut_of_killed_predecessor {H : NumericalSemigroup} (T : Triple H)
    (m L : ℕ) (hL : 0<L)
    (hk : (L-1)*T.g 2∈cyclicCut H m) : L*T.g 2∈cyclicCut H m := by
  have hmem := cut_add H hk (T.member (Finsupp.single 2 1))
  have he : (L-1)*T.g 2+T.weight (Finsupp.single 2 1)=L*T.g 2 := by
    rw [T.weight_single]
    have h := congrArg (fun n => n*T.g 2) (show L-1+1=L by omega)
    simpa only [Nat.add_mul,one_mul] using h
  exact he ▸ hmem

/-- The pure-pair boundary degree is also cut directly from the killed
opposite pure-axis predecessor and the actual pair relation. -/
theorem pure_pair_boundary_cut {H : NumericalSemigroup} (T : Triple H)
    (m R L : ℕ) (hR : 0<R) (hpair : R*T.g 0=L*T.g 2)
    (hk : (R-1)*T.g 0∈cyclicCut H m) : L*T.g 2∈cyclicCut H m := by
  have hmem := cut_add H hk (T.member (Finsupp.single 0 1))
  have he : (R-1)*T.g 0+T.weight (Finsupp.single 0 1)=L*T.g 2 := by
    rw [T.weight_single]
    have h := congrArg (fun n => n*T.g 0) (show R-1+1=R by omega)
    simp only [Nat.add_mul,one_mul] at h ⊢
    omega
  exact he ▸ hmem
end NS25Lean.CriticalModeBounds
