import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Actual abelian sheaves of independently restricted point coefficients. -/

namespace ManuscriptAudit.PointCoefficientSheaf

open CategoryTheory Opposite TopologicalSpace

noncomputable section

variable {X : TopCat.{0}} (P : Set X) (A : P → Type)
variable [∀ p : P, AddCommGroup (A p)]

abbrev Sections (U : Opens X) := ∀ p : P, p.val ∈ U → A p

def restrict {U V : Opens X} (h : V ≤ U) : Sections P A U →+ Sections P A V where
  toFun s p hp := s p (h hp)
  map_zero' := rfl
  map_add' _ _ := rfl

def presheaf : TopCat.Presheaf AddCommGrpCat.{0} X where
  obj U := AddCommGrpCat.of (Sections P A U.unop)
  map f := AddCommGrpCat.ofHom (restrict P A f.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

private def coverIndex {I : Type} (U : I → Opens X) (p : P) (hp : p.val ∈ iSup U) : I :=
  (Opens.mem_iSup.mp hp).choose

private theorem coverIndex_mem {I : Type} (U : I → Opens X) (p : P) (hp : p.val ∈ iSup U) :
    p.val ∈ U (coverIndex P U p hp) :=
  (Opens.mem_iSup.mp hp).choose_spec

theorem presheaf_isSheaf : (presheaf P A).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (presheaf P A)).mpr
  intro I U s hs
  let g : Sections P A (iSup U) :=
    fun p hp => s (coverIndex P U p hp) p (coverIndex_mem P U p hp)
  refine ⟨g, ?_, ?_⟩
  · intro i
    funext p hp
    let hUp := (le_iSup U i) hp
    let j := coverIndex P U p hUp
    have hj : p.val ∈ U j := coverIndex_mem P U p hUp
    have h := congrFun (congrFun (hs j i) p) (show p.val ∈ U j ⊓ U i from ⟨hj, hp⟩)
    change s j p hj = s i p hp at h
    exact h
  · intro v hv
    funext p hp
    let i := coverIndex P U p hp
    have hi : p.val ∈ U i := coverIndex_mem P U p hp
    have h := congrFun (congrFun (hv i) p) hi
    change v p hp = s i p hi at h
    exact h

def sheaf : TopCat.Sheaf AddCommGrpCat.{0} X :=
  ⟨presheaf P A, presheaf_isSheaf P A⟩

theorem restriction_surjective {U V : Opens X} (h : V ≤ U) :
    Function.Surjective (restrict P A h) := by
  classical
  intro s
  refine ⟨fun p _ => if hpV : p.val ∈ V then s p hpV else 0, ?_⟩
  funext p hp
  change (if hpV : p.val ∈ V then s p hpV else 0) = s p hp
  rw [dif_pos hp]

end
end ManuscriptAudit.PointCoefficientSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PointCoefficientSheaf.presheaf_isSheaf,
      ``ManuscriptAudit.PointCoefficientSheaf.sheaf,
      ``ManuscriptAudit.PointCoefficientSheaf.restriction_surjective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
