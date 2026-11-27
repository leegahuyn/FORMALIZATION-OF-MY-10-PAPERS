import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.PointCoefficientSheaf

/-! Arbitrary-cover Čech degree one is zero for the actual point-coefficient sheaf. -/

namespace ManuscriptAudit.PointCoefficientCechOne

open CategoryTheory Opposite TopologicalSpace PointCoefficientSheaf
open scoped Pointwise

noncomputable section

variable {X : TopCat.{0}} (P : Set X) (A : P → Type)
variable [∀ p : P, AddCommGroup (A p)]
variable {I : Type} (U : I → Opens X)

abbrev CochainsZero := ∀ i : I, Sections P A (U i)
abbrev CochainsOne := ∀ i j : I, Sections P A (U i ⊓ U j)

def IsCocycle (c : CochainsOne P A U) : Prop :=
  ∀ (i j k : I) (p : P) (hi : p.val ∈ U i) (hj : p.val ∈ U j) (hk : p.val ∈ U k),
    c i j p ⟨hi, hj⟩ + c j k p ⟨hj, hk⟩ = c i k p ⟨hi, hk⟩

def cocycles : AddSubgroup (CochainsOne P A U) where
  carrier := {c | IsCocycle P A U c}
  zero_mem' := by intro i j k p hi hj hk; simp
  add_mem' := by
    intro c d hc hd i j k p hi hj hk
    change IsCocycle P A U c at hc
    change IsCocycle P A U d at hd
    change (c i j p ⟨hi, hj⟩ + d i j p ⟨hi, hj⟩) +
      (c j k p ⟨hj, hk⟩ + d j k p ⟨hj, hk⟩) =
      c i k p ⟨hi, hk⟩ + d i k p ⟨hi, hk⟩
    calc
      _ = (c i j p ⟨hi, hj⟩ + c j k p ⟨hj, hk⟩) +
          (d i j p ⟨hi, hj⟩ + d j k p ⟨hj, hk⟩) := by abel
      _ = _ := by rw [hc i j k p hi hj hk, hd i j k p hi hj hk]
  neg_mem' := by
    intro c hc i j k p hi hj hk
    change IsCocycle P A U c at hc
    change -c i j p ⟨hi, hj⟩ + -c j k p ⟨hj, hk⟩ = -c i k p ⟨hi, hk⟩
    rw [← neg_add, hc i j k p hi hj hk]

def delta : CochainsZero P A U →+ CochainsOne P A U where
  toFun s i j := restrict P A (inf_le_right : U i ⊓ U j ≤ U j) (s j) -
    restrict P A (inf_le_left : U i ⊓ U j ≤ U i) (s i)
  map_zero' := by
    funext i j p hp
    change (0 : A p) - 0 = 0
    exact sub_self _
  map_add' s t := by
    funext i j p hp
    change (s j p hp.2 + t j p hp.2) - (s i p hp.1 + t i p hp.1) =
      (s j p hp.2 - s i p hp.1) + (t j p hp.2 - t i p hp.1)
    abel

theorem delta_isCocycle (s : CochainsZero P A U) : IsCocycle P A U (delta P A U s) := by
  intro i j k p hi hj hk
  change (s j p hj - s i p hi) + (s k p hk - s j p hj) = s k p hk - s i p hi
  abel

def deltaToCocycles : CochainsZero P A U →+ cocycles P A U :=
  (delta P A U).codRestrict _ (delta_isCocycle P A U)

theorem deltaToCocycles_surjective : Function.Surjective (deltaToCocycles P A U) := by
  intro c
  have h : IsCocycle P A U c.val := c.property
  let index (p : P) (hp : p.val ∈ iSup U) : I := (Opens.mem_iSup.mp hp).choose
  have hit (p : P) (hp : p.val ∈ iSup U) : p.val ∈ U (index p hp) :=
    (Opens.mem_iSup.mp hp).choose_spec
  let s : CochainsZero P A U := fun i p hp =>
    c.val (index p ((le_iSup U i) hp)) i p ⟨hit p ((le_iSup U i) hp), hp⟩
  refine ⟨s, Subtype.ext ?_⟩
  funext i j p hp
  let H := (le_iSup U i) hp.1
  let k := index p H
  have hk : p.val ∈ U k := hit p H
  change c.val k j p ⟨hk, hp.2⟩ - c.val k i p ⟨hk, hp.1⟩ = c.val i j p hp
  apply sub_eq_iff_eq_add.mpr
  exact (h k i j p hk hp.1 hp.2).symm.trans (add_comm _ _)

abbrev HOne := (cocycles P A U) ⧸ (deltaToCocycles P A U).range

theorem HOne_subsingleton : Subsingleton (HOne P A U) := by
  have h : (deltaToCocycles P A U).range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr (deltaToCocycles_surjective P A U)
  change Subsingleton ((cocycles P A U) ⧸ (deltaToCocycles P A U).range)
  rw [h]
  exact QuotientAddGroup.subsingleton_quotient_top

end
end ManuscriptAudit.PointCoefficientCechOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PointCoefficientCechOne.delta_isCocycle,
      ``ManuscriptAudit.PointCoefficientCechOne.deltaToCocycles_surjective,
      ``ManuscriptAudit.PointCoefficientCechOne.HOne_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
