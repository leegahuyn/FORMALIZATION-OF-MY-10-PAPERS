import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! A matching section on an actual singleton étale cover
descends, using the actual small étale topology. -/

namespace ManuscriptAudit.NativeEtaleSingletonSectionGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} {U V W : X.Etale}

private abbrev G := AddCommGrpCat.{u + 1}

set_option maxHeartbeats 3400000 in
/-- If the two restrictions of a section along the actual
self-pullback agree, it glues uniquely on the actual target. -/
theorem existsUnique_glue (I : Sheaf X.smallEtaleTopology G.{u})
    (f : V ⟶ U) (p q : W ⟶ V) (hpq : IsPullback p q f f)
    (hCov : Function.Surjective f.left)
    (x : I.obj.obj (op V)) (hx : I.obj.map p.op x = I.obj.map q.op x) :
    ∃! y : I.obj.obj (op U), I.obj.map f.op y = x := by
  let P := I.obj ⋙ CategoryTheory.forget G.{u}
  letI : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget G.{u}) :=
    AddCommGrpCat.adj.rightAdjoint_preservesLimits
  have hI : Presieve.IsSheaf X.smallEtaleTopology P :=
    (isSheaf_iff_isSheaf_of_type X.smallEtaleTopology _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (CategoryTheory.forget G.{u}) I.property)
  let M : Unit → X.Etale := fun _ ↦ V
  let g : ∀ i, M i ⟶ U := fun _ ↦ f
  have hg : Sieve.ofArrows M g ∈ X.smallEtaleTopology U := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr
    ext u
    constructor
    · intro _
      exact Set.mem_univ u
    · intro _
      exact Set.mem_iUnion.mpr ⟨(), hCov u⟩
  let z : ∀ i, P.obj (op (M i)) := fun _ ↦ x
  have hz : Presieve.Arrows.Compatible P g z := by
    intro i j T a b hab
    change a ≫ f = b ≫ f at hab
    let l := hpq.lift a b hab
    have hL : l ≫ p = a := hpq.lift_fst a b hab
    have hR : l ≫ q = b := hpq.lift_snd a b hab
    change P.map a.op x = P.map b.op x
    rw [← hL, ← hR, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
    exact congrArg (P.map l.op) hx
  obtain ⟨y, hy, huniq⟩ :=
    (Presieve.isSheafFor_arrows_iff (P := P) g).mp (hI.isSheafFor _ hg) z hz
  exact ⟨y, hy (), fun t ht ↦ huniq t (fun _ ↦ ht)⟩

end
end ManuscriptAudit.NativeEtaleSingletonSectionGluing

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeEtaleSingletonSectionGluing.existsUnique_glue
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
