import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Actual abelian sheaves of independently restricted point coefficients. -/

namespace ManuscriptAudit.PointCoefficientSheaf

open CategoryTheory Opposite TopologicalSpace

noncomputable section

variable {X : TopCat.{0}} (P : Set X) (A : P → Type)
variable [∀ p : P, AddCommGroup (A p)]

abbrev PointsIn (U : Opens X) := {p : P // p.val ∈ U}

abbrev Sections (U : Opens X) := ∀ q : PointsIn P U, A q.val

def restrict {U V : Opens X} (h : V ≤ U) : Sections P A U →+ Sections P A V where
  toFun s q := s ⟨q.val, h q.property⟩
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
    fun q => s (coverIndex P U q.val q.property) ⟨q.val, coverIndex_mem P U q.val q.property⟩
  refine ⟨g, ?_, ?_⟩
  · intro i
    funext q
    obtain ⟨p, hp⟩ := q
    let hUp := (le_iSup U i) hp
    let j := coverIndex P U p hUp
    have hj : p.val ∈ U j := coverIndex_mem P U p hUp
    have h := congrFun (hs j i) (⟨p, ⟨hj, hp⟩⟩ : PointsIn P (U j ⊓ U i))
    change s j ⟨p, hj⟩ = s i ⟨p, hp⟩ at h
    exact h
  · intro v hv
    funext q
    obtain ⟨p, hp⟩ := q
    let i := coverIndex P U p hp
    have hi : p.val ∈ U i := coverIndex_mem P U p hp
    have h := congrFun (hv i) (⟨p, hi⟩ : PointsIn P (U i))
    change v ⟨p, hp⟩ = s i ⟨p, hi⟩ at h
    exact h

def sheaf : TopCat.Sheaf AddCommGrpCat.{0} X :=
  ⟨presheaf P A, presheaf_isSheaf P A⟩

theorem restriction_surjective {U V : Opens X} (h : V ≤ U) :
    Function.Surjective (restrict P A h) := by
  classical
  intro s
  refine ⟨fun q => if hV : q.val.val ∈ V then s ⟨q.val, hV⟩ else 0, ?_⟩
  funext q
  change (if hV : q.val.val ∈ V then s ⟨q.val, hV⟩ else 0) = s q
  rw [dif_pos q.property]

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
