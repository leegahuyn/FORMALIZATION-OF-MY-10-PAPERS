import Lean.Util.CollectAxioms
import Mathlib.Order.Monotone.Basic
import PrimalitySheafVerification.ManuscriptAudit.MonotoneCardinalFactors
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionTower

/-! Torsion cardinalities and transition surjectivity from eventual exact cardinalities. -/

namespace ManuscriptAudit.PowerTorsionTailCard

open TorsionFrobeniusModule PowerTorsionTower MonotoneCardinalFactors

noncomputable section

variable (l : ℕ) (G : Type*) [AddCommGroup G]

private theorem subgroup_le {n k : ℕ} (h : n ≤ k) :
    subgroup (l ^ n) G ≤ subgroup (l ^ k) G := by
  intro P hP
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  apply (mem_iff (l ^ (n + d)) G P).mpr
  rw [pow_add, mul_nsmul', (mem_iff (l ^ n) G P).mp hP, nsmul_zero]

/-- Multiplication by l^n from level n+1 into the first torsion subgroup. -/
def scaleToFirst (n : ℕ) : PowerTorsion l G (n + 1) →+ Torsion l G where
  toFun P := ⟨(l ^ n) • (P : G), (mem_iff l G _).mpr (by
    rw [← mul_nsmul', ← pow_succ]
    exact (mem_iff (l ^ (n + 1)) G _).mp P.property)⟩
  map_zero' := Subtype.ext (nsmul_zero _)
  map_add' P Q := Subtype.ext (nsmul_add (P : G) (Q : G) _)

def scaleToFirstKernelEquiv (n : ℕ) :
    (scaleToFirst l G n).ker ≃ PowerTorsion l G n where
  toFun P := ⟨(P.val : G), (mem_iff (l ^ n) G _).mpr (by
    have h : scaleToFirst l G n P.val = 0 := AddMonoidHom.mem_ker.mp P.property
    exact congrArg (fun Q : Torsion l G => (Q : G)) h)⟩
  invFun P := by
    let Q : PowerTorsion l G (n + 1) := ⟨P.val, subgroup_le l G (Nat.le_succ n) P.property⟩
    exact ⟨Q, AddMonoidHom.mem_ker.mpr (Subtype.ext ((mem_iff (l ^ n) G _).mp P.property))⟩
  left_inv P := Subtype.ext (Subtype.ext rfl)
  right_inv P := Subtype.ext rfl

theorem range_scaleToFirst_decreasing (n : ℕ) :
    (scaleToFirst l G (n + 1)).range ≤ (scaleToFirst l G n).range := by
  rintro _ ⟨P, rfl⟩
  refine ⟨transition l G (n + 1) P, Subtype.ext ?_⟩
  change (l ^ n) • (l • (P : G)) = (l ^ (n + 1)) • (P : G)
  rw [pow_succ, mul_nsmul]

theorem level_card_factor (n : ℕ) :
    Nat.card (PowerTorsion l G (n + 1)) =
      Nat.card (scaleToFirst l G n).range * Nat.card (PowerTorsion l G n) := by
  let f := scaleToFirst l G n
  calc
    _ = Nat.card (PowerTorsion l G (n + 1) ⧸ f.ker) * Nat.card f.ker :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
    _ = _ := congrArg₂ (· * ·)
      (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv)
      (Nat.card_congr (scaleToFirstKernelEquiv l G n))

theorem finite_of_eventually_exact {d N : ℕ} (hd : 0 < d)
    (hTail : ∀ n, N ≤ n → Nat.card (PowerTorsion l G n) = d ^ n) (n : ℕ) :
    Finite (PowerTorsion l G n) := by
  let k := max N n
  letI : Finite (PowerTorsion l G k) := Nat.finite_of_card_ne_zero (by
    rw [hTail k (le_max_left N n)]
    exact pow_ne_zero _ hd.ne')
  exact Finite.of_injective
    (fun P : PowerTorsion l G n => (⟨P.val, subgroup_le l G (le_max_right N n) P.property⟩ :
      PowerTorsion l G k))
    (fun _ _ h => Subtype.ext (congrArg Subtype.val h))

/-- Exact eventual cardinalities force the full tower cardinalities and onto transitions. -/
theorem card_and_surjective_of_eventually_exact {d N : ℕ} (hd : 0 < d)
    (hTail : ∀ n, N ≤ n → Nat.card (PowerTorsion l G n) = d ^ n) :
    (∀ n, Nat.card (PowerTorsion l G n) = d ^ n) ∧
      ∀ n, Function.Surjective (transition l G n) := by
  haveI : Finite (Torsion l G) := by
    simpa only [PowerTorsionTower.PowerTorsion, pow_one] using finite_of_eventually_exact l G hd hTail 1
  have h0 : Nat.card (PowerTorsion l G 0) = 1 := by
    letI : Unique (PowerTorsion l G 0) := ⟨⟨0⟩, fun P => Subtype.ext (by
      change (P : G) = 0
      simpa only [pow_zero, one_nsmul] using (mem_iff (l ^ 0) G _).mp P.property)⟩
    exact Nat.card_unique
  have hMono : Antitone (fun n => Nat.card (scaleToFirst l G n).range) := by
    apply antitone_nat_of_succ_le
    intro n
    let f (P : (scaleToFirst l G (n + 1)).range) : (scaleToFirst l G n).range :=
      ⟨P.val, range_scaleToFirst_decreasing l G n P.property⟩
    exact Nat.card_le_card_of_injective f (fun _ _ h => Subtype.ext (congrArg Subtype.val h))
  have hAll := (exact_of_eventually_exact
    (fun n => Nat.card (scaleToFirst l G n).range) (fun n => Nat.card (PowerTorsion l G n))
    hd h0 (level_card_factor l G) hMono hTail).2
  have hFirst : Nat.card (Torsion l G) = d := by
    simpa only [PowerTorsionTower.PowerTorsion, pow_one] using hAll 1
  refine ⟨hAll, fun n => ?_⟩
  letI : Finite (PowerTorsion l G n) := finite_of_eventually_exact l G hd hTail n
  let f := transition l G n
  have hFact : Nat.card (PowerTorsion l G (n + 1)) = Nat.card f.range * d := by
    calc
      _ = Nat.card (PowerTorsion l G (n + 1) ⧸ f.ker) * Nat.card f.ker :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
      _ = Nat.card f.range * Nat.card (Torsion l G) := congrArg₂ (· * ·)
        (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv)
        (Nat.card_congr (transitionKernelEquiv l G n))
      _ = _ := by rw [hFirst]
  have hRange : Nat.card f.range = Nat.card (PowerTorsion l G n) := by
    apply Nat.eq_of_mul_eq_mul_right hd
    rw [← hFact, hAll (n + 1), hAll n, pow_succ]
  have hs : Function.Surjective (fun P : f.range => (P : PowerTorsion l G n)) :=
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨Subtype.val_injective, hRange⟩).2
  intro P
  obtain ⟨Q, hQ⟩ := hs P
  obtain ⟨U, hU⟩ := Q.property
  exact ⟨U, hU.trans hQ⟩

end
end ManuscriptAudit.PowerTorsionTailCard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTorsionTailCard.range_scaleToFirst_decreasing,
      ``ManuscriptAudit.PowerTorsionTailCard.level_card_factor,
      ``ManuscriptAudit.PowerTorsionTailCard.finite_of_eventually_exact,
      ``ManuscriptAudit.PowerTorsionTailCard.card_and_surjective_of_eventually_exact] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
