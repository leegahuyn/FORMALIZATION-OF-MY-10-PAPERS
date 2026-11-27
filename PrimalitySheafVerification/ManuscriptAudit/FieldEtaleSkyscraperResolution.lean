import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.EnoughInjectives
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Injective presentations by geometric skyscrapers over a field

Any geometric point of a field covers its unique scheme point, so its
stalk reflects monomorphisms. An injective presentation of the stalk
therefore gives an actual injective presentation of any étale abelian
sheaf, using the right-adjoint skyscraper.
-/

namespace ManuscriptAudit.FieldEtaleSkyscraperResolution

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

variable (K : Type) [Field K]

private abbrev X := Spec (CommRingCat.of K)
private abbrev S := Sheaf (X K).smallEtaleTopology AddCommGrpCat.{0}

/-- The chosen geometric point uses the separable closure of the field. -/
abbrev geometricPoint : Spec (CommRingCat.of (SeparableClosure K)) ⟶ X K :=
  Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))

abbrev point := Scheme.pointSmallEtale (geometricPoint K)

set_option backward.isDefEq.respectTransparency false in
/-- The stalk at any single geometric point of a field reflects
monomorphisms on the full small étale site. -/
theorem stalk_reflectsMonomorphisms {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ X K) :
    ((Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{0})).ReflectsMonomorphisms where
  reflects {A B} f hf := by
    let P := ObjectProperty.ofObj (fun _ : Unit ↦ Scheme.pointSmallEtale x)
    have hP : P.IsConservativeFamilyOfPoints := Scheme.isConservative_pointSmallEtale
      (fun _ : Unit ↦ x) (by
        ext z
        simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
        exact ⟨(), default, Subsingleton.elim _ _⟩)
    letI : ∀ q : P.FullSubcategory, Mono (q.obj.sheafFiber.map f) := fun q ↦ by
      obtain ⟨_, hq⟩ := (ObjectProperty.ofObj_iff
        (fun _ : Unit ↦ Scheme.pointSmallEtale x) q.obj).mp q.property
      rw [← hq]
      exact hf
    exact (hP.jointlyReflectMonomorphisms AddCommGrpCat.{0}).mono f

/-- The coefficient of the injective skyscraper is a genuine injective
enlargement of the stalk. -/
def injectiveCoefficient (A : S K) : AddCommGrpCat.{0} :=
  Injective.under ((point K).sheafFiber.obj A)

private def stalkPresentation (A : S K) :
    InjectivePresentation ((point K).sheafFiber.obj A) where
  J := injectiveCoefficient K A
  injective := inferInstanceAs (Injective (Injective.under ((point K).sheafFiber.obj A)))
  f := Injective.ι ((point K).sheafFiber.obj A)
  mono := inferInstanceAs (Mono (Injective.ι ((point K).sheafFiber.obj A)))

/-- Every abelian sheaf on the actual field site embeds into an injective
geometric skyscraper. -/
def injectivePresentation (A : S K) : InjectivePresentation A := by
  letI := stalk_reflectsMonomorphisms K (geometricPoint K)
  exact (point K).skyscraperSheafAdjunction.injectivePresentationOfMap A
    (stalkPresentation K A)

@[simp] theorem injectivePresentation_J (A : S K) :
    (injectivePresentation K A).J = (point K).skyscraperSheaf (injectiveCoefficient K A) :=
  rfl

end

end ManuscriptAudit.FieldEtaleSkyscraperResolution

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FieldEtaleSkyscraperResolution.stalk_reflectsMonomorphisms,
      ``ManuscriptAudit.FieldEtaleSkyscraperResolution.injectivePresentation_J] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
