import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Limits
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineSingletonLift
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Sections on a disjoint cover on the actual pro-étale site

An additive sheaf is separated on a jointly surjective family.
For disjoint monomorphic components, every family of sections is
compatible because the mixed overlaps have no points.
-/

namespace ManuscriptAudit.ProetaleDisjointSections

open AlgebraicGeometry CategoryTheory Opposite

universe u v w

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{w})
variable {W : X.ProEt} {I : Type v} {V : I → X.ProEt}
variable (f : ∀ i, V i ⟶ W)

private abbrev P := F.obj ⋙ forget AddCommGrpCat.{w}

/-- Restriction to a jointly surjective family detects equality of sections. -/
theorem restriction_injective
    (hCov : Sieve.ofArrows V f ∈ Scheme.ProEt.topology X W) :
    Function.Injective (fun a : F.obj.obj (op W) ↦ fun i ↦ F.obj.map (f i).op a) := by
  intro a b hab
  apply ((ProetaleAffineSingletonLift.underlying_types_isSheaf F).isSheafFor (Presieve.ofArrows V f) hCov).isSeparatedFor.ext
  rintro _ _ ⟨i⟩
  exact congrFun hab i

/-- Restriction identifies the actual sections over a disjoint
monomorphic cover with the product of sections over its components. -/
def sectionsEquivOfDisjointCover
    (hCov : Sieve.ofArrows V f ∈ Scheme.ProEt.topology X W)
    (hMono : ∀ i, Mono (f i).left)
    (hDis : ∀ i j, i ≠ j → Disjoint (Set.range (f i).left) (Set.range (f j).left)) :
    (F.obj.obj (op W)) ≃+ (∀ i, F.obj.obj (op (V i))) := by
  classical
  let m : (F.obj.obj (op W)) →+ (∀ i, F.obj.obj (op (V i))) :=
    { toFun := fun a i ↦ F.obj.map (f i).op a
      map_zero' := funext (fun i ↦ map_zero (F.obj.map (f i).op).hom)
      map_add' := fun a b ↦ funext (fun i ↦ map_add (F.obj.map (f i).op).hom a b) }
  refine AddEquiv.ofBijective m ⟨restriction_injective F f hCov, ?_⟩
  intro y
  have hCompat : Presieve.Arrows.Compatible (P F) f y := by
    intro i j T a b hab
    have hab' : a.left ≫ (f i).left = b.left ≫ (f j).left :=
      congrArg (fun g : T ⟶ W ↦ g.left) hab
    by_cases hij : i = j
    · subst j
      letI := hMono i
      have hEq : a = b := MorphismProperty.Over.Hom.ext ((cancel_mono (f i).left).mp hab')
      rw [hEq]
    · letI : IsEmpty T.left := ⟨fun z ↦ by
        have hz : (f i).left (a.left z) = (f j).left (b.left z) := by
          simpa only [Scheme.Hom.comp_apply] using
            (congrArg (fun g : T.left ⟶ W.left ↦ g z) hab')
        exact Set.disjoint_left.mp (hDis i j hij) ⟨a.left z, rfl⟩ ⟨b.left z, hz.symm⟩⟩
      exact (ProetaleAffineSingletonLift.sections_subsingleton_of_empty F T).elim _ _
  obtain ⟨a, ha, _⟩ := (Presieve.isSheafFor_arrows_iff (P := P F) (π := f)).mp
    ((ProetaleAffineSingletonLift.underlying_types_isSheaf F).isSheafFor (Presieve.ofArrows V f) hCov) y hCompat
  exact ⟨a, funext ha⟩

/-- The product equivalence acts on each coordinate by actual restriction. -/
@[simp] theorem sectionsEquivOfDisjointCover_apply
    (hCov : Sieve.ofArrows V f ∈ Scheme.ProEt.topology X W)
    (hMono : ∀ i, Mono (f i).left)
    (hDis : ∀ i j, i ≠ j → Disjoint (Set.range (f i).left) (Set.range (f j).left))
    (a : F.obj.obj (op W)) (i : I) :
    sectionsEquivOfDisjointCover F f hCov hMono hDis a i = F.obj.map (f i).op a :=
  rfl

end

end ManuscriptAudit.ProetaleDisjointSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleDisjointSections.restriction_injective,
      ``ManuscriptAudit.ProetaleDisjointSections.sectionsEquivOfDisjointCover,
      ``ManuscriptAudit.ProetaleDisjointSections.sectionsEquivOfDisjointCover_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
