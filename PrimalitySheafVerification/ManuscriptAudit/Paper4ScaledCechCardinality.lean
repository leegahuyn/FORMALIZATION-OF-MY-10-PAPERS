import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.Index
import PrimalitySheafVerification.ManuscriptAudit.CyclicInclusionCokernel

/-! The literal additive inclusions into the lcm residue group determine
the kernel and each printed cardinality of the two-term overlap complex. -/

namespace ManuscriptAudit.Paper4ScaledCechCardinality

open CyclicInclusionCokernel (cyclicInclusion cyclicInclusion_int cyclicInclusion_injective
  lcmInclusionDifference lcmInclusionDifference_surjective paper4_lcmInclusionCokernel_subsingleton)

noncomputable section

/-- Residue-group inclusions compose along a divisibility chain. -/
theorem cyclicInclusion_comp {d m L : ℕ} (h : d ∣ m) (k : m ∣ L) (hd : 0 < d) :
    (cyclicInclusion k).comp (cyclicInclusion h) = cyclicInclusion (h.trans k) := by
  have hScale : L / m * (m / d) = L / d := by
    apply Nat.eq_of_mul_eq_mul_right hd
    rw [Nat.mul_assoc, Nat.div_mul_cancel h, Nat.div_mul_cancel k,
      Nat.div_mul_cancel (h.trans k)]
  apply AddMonoidHom.ext
  intro z
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective (n := d) z
  change cyclicInclusion k (cyclicInclusion h (x : ZMod d)) =
    cyclicInclusion (h.trans k) (x : ZMod d)
  have hInner : cyclicInclusion h (x : ZMod d) =
      ((((m / d : ℕ) : ℤ) * x : ℤ) : ZMod m) := by
    rw [cyclicInclusion_int, Int.cast_mul, Int.cast_natCast]
  rw [hInner, cyclicInclusion_int, cyclicInclusion_int, Int.cast_mul, Int.cast_natCast,
    ← mul_assoc, ← Nat.cast_mul, hScale]

variable (m n : ℕ)

private abbrev G := m.gcd n
private abbrev L := m.lcm n
abbrev difference := lcmInclusionDifference m n

private theorem card_residue (d : ℕ) (hd : 0 < d) : Nat.card (ZMod d) = d := by
  letI : NeZero d := ⟨hd.ne'⟩
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem card_range (hm : 0 < m) (hn : 0 < n) :
    Nat.card (difference m n).range = L m n := by
  let e : (difference m n).range ≃ ZMod (L m n) :=
    { toFun := Subtype.val
      invFun := fun x ↦ ⟨x, lcmInclusionDifference_surjective m n hm hn x⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }
  exact (Nat.card_congr e).trans (card_residue _ (Nat.lcm_pos hm hn))

theorem card_kernel (hm : 0 < m) (hn : 0 < n) :
    Nat.card (difference m n).ker = G m n := by
  have h := (difference m n).ker.card_mul_index
  rw [AddSubgroup.index_ker, card_range m n hm hn, Nat.card_prod,
    card_residue _ hm, card_residue _ hn, ← Nat.gcd_mul_lcm m n] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.lcm_pos hm hn) h

/-- The genuine kernel is the gcd residue group with its two canonical inclusions. -/
def kernelEquiv (hm : 0 < m) (hn : 0 < n) :
    ZMod (G m n) ≃+ (difference m n).ker := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  have hg : 0 < G m n := Nat.gcd_pos_of_pos_left n hm
  let a := cyclicInclusion (Nat.gcd_dvd_left m n)
  let b := cyclicInclusion (Nat.gcd_dvd_right m n)
  let j : ZMod (G m n) →+ (difference m n).ker :=
    (a.prod b).codRestrict _ (by
      intro x
      have h₁ := DFunLike.congr_fun
        (cyclicInclusion_comp (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n) hg) x
      have h₂ := DFunLike.congr_fun
        (cyclicInclusion_comp (Nat.gcd_dvd_right m n) (Nat.dvd_lcm_right m n) hg) x
      change cyclicInclusion (Nat.dvd_lcm_left m n) (a x) -
        cyclicInclusion (Nat.dvd_lcm_right m n) (b x) = 0
      exact sub_eq_zero.mpr (h₁.trans h₂.symm))
  refine AddEquiv.ofBijective j ((Nat.bijective_iff_injective_and_card j).mpr ⟨?_, ?_⟩)
  · intro x y hxy
    exact (cyclicInclusion_injective (Nat.gcd_dvd_left m n) hm hg)
      (congrArg (fun z : (difference m n).ker ↦ z.val.1) hxy)
  · rw [card_residue _ hg, card_kernel m n hm hn]

theorem card_cokernel (hm : 0 < m) (hn : 0 < n) :
    Nat.card (ZMod (L m n) ⧸ (difference m n).range) = 1 := by
  letI := paper4_lcmInclusionCokernel_subsingleton m n hm hn
  let e : (ZMod (L m n) ⧸ (difference m n).range) ≃ PUnit.{1} :=
    { toFun := fun _ ↦ PUnit.unit
      invFun := fun _ ↦ 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
  simpa using Nat.card_congr e

/-- Each printed cardinality fails for nontrivial gcd in this overlap model. -/
theorem printed_cardinalities_fail (hm : 0 < m) (hn : 0 < n) (hg : 1 < G m n) :
    Nat.card (difference m n).range ≠ L m n / G m n ∧
      Nat.card (difference m n).ker ≠ (G m n)^2 ∧
      Nat.card (ZMod (L m n) ⧸ (difference m n).range) ≠ G m n := by
  rw [card_range m n hm hn, card_kernel m n hm hn, card_cokernel m n hm hn]
  have hL : 0 < L m n := Nat.lcm_pos hm hn
  have hg' : 0 < G m n := Nat.zero_lt_of_lt hg
  have hSquare : G m n < (G m n)^2 := by
    simpa only [pow_two, Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hg hg'
  exact ⟨(Nat.div_lt_self hL hg).ne', hSquare.ne, hg.ne⟩

end
end ManuscriptAudit.Paper4ScaledCechCardinality

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4ScaledCechCardinality.cyclicInclusion_comp,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.card_range,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.card_kernel,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.kernelEquiv,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.card_cokernel,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.printed_cardinalities_fail] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
