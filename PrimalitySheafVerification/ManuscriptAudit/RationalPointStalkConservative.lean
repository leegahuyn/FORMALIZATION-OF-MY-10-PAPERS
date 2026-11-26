import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# A conservative geometric family with a selected rational point

One may use a chosen separably closed rational point over its
underlying point, and take the usual separable residue-field closures
at all other points.
-/

namespace ManuscriptAudit.SmallEtaleGeometricBaseChange

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- To detect an isomorphism of étale sheaves it suffices to test the chosen
rational geometric point and the geometric points with other underlying points. -/
theorem isIso_of_rationalOrigin_and_remaining_stalks {K : Type u} [Field K] [IsSepClosed K]
    {X : Scheme.{u}} (o : Spec (CommRingCat.of K) ⟶ X)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (f : F ⟶ G)
    (hOrigin : IsIso ((Scheme.pointSmallEtale o).sheafFiber.map f))
    (hRest : ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      s (default : Spec (.of Ω)) ≠ o (default : Spec (CommRingCat.of K)) →
      IsIso ((Scheme.pointSmallEtale s).sheafFiber.map f)) : IsIso f := by
  classical
  let x₀ := o (default : Spec (CommRingCat.of K))
  let I := Unit ⊕ {x : X // x ≠ x₀}
  let fields : I → Type u := fun
    | .inl _ => K
    | .inr x => SeparableClosure (X.residueField x.1)
  letI : ∀ a, Field (fields a) := fun a => by cases a <;> infer_instance
  letI : ∀ a, IsSepClosed (fields a) := fun a => by cases a <;> infer_instance
  let points : (a : I) → Spec (CommRingCat.of (fields a)) ⟶ X := fun
    | .inl _ => o
    | .inr x => (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x.1)) X).2
        ⟨x.1, CommRingCat.ofHom (algebraMap (X.residueField x.1) _)⟩
  have underlying (x : {x : X // x ≠ x₀}) :
      points (.inr x) (default : Spec (CommRingCat.of (fields (.inr x)))) = x.1 := by
    simp [points, Scheme.SpecToEquivOfField]
  have hCover : (⋃ a, Set.range (points a)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x = x₀
    · exact Set.mem_iUnion.mpr ⟨.inl (), ⟨default, hx.symm⟩⟩
    · exact Set.mem_iUnion.mpr ⟨.inr ⟨x, hx⟩, ⟨default, underlying ⟨x, hx⟩⟩⟩
  let P := ObjectProperty.ofObj (fun a => Scheme.pointSmallEtale (points a))
  have hP : P.IsConservativeFamilyOfPoints := Scheme.isConservative_pointSmallEtale points hCover
  letI : ∀ q : P.FullSubcategory, IsIso (q.obj.sheafFiber.map f) := fun q => by
    obtain ⟨a, ha⟩ :=
      (ObjectProperty.ofObj_iff (fun a => Scheme.pointSmallEtale (points a)) q.obj).mp q.property
    rw [← ha]
    cases a with
    | inl _ => exact hOrigin
    | inr x => exact hRest (points (.inr x)) (by rw [underlying]; exact x.property)
  exact (hP.jointlyReflectIsomorphisms AddCommGrpCat.{u}).isIso f

end

end ManuscriptAudit.SmallEtaleGeometricBaseChange

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SmallEtaleGeometricBaseChange.isIso_of_rationalOrigin_and_remaining_stalks
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
