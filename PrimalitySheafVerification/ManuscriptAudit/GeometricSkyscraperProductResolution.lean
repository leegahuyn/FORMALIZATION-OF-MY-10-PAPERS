import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.EnoughInjectives
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! Injective presentations by products of actual geometric skyscrapers. -/

namespace ManuscriptAudit.GeometricSkyscraperProductResolution

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u})

private abbrev C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- The point at a separable closure of the residue field of a scheme point. -/
def geometricPoint (x : X) :
    Spec (CommRingCat.of (SeparableClosure (X.residueField x))) ⟶ X :=
  (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).2
    ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩

abbrev geometricFiber (x : X) := Scheme.pointSmallEtale (geometricPoint X x)

/-- Enlarge each geometric stalk into an injective abelian group. -/
def coefficient (A : C X) (x : X) : AddCommGrpCat.{u} :=
  Injective.under ((geometricFiber X x).sheafFiber.obj A)

abbrev skyscraper (A : C X) (x : X) : C X :=
  (geometricFiber X x).skyscraperSheaf (coefficient X A x)

private def component (A : C X) (x : X) : A ⟶ skyscraper X A x :=
  ((geometricFiber X x).skyscraperSheafAdjunction.homEquiv A (coefficient X A x))
    (Injective.ι ((geometricFiber X x).sheafFiber.obj A))

/-- The actual map into the product of injective geometric skyscrapers. -/
def embedding (A : C X) : A ⟶ (∏ᶜ (skyscraper X A)) :=
  Pi.lift (component X A)

private theorem stalkComponent_mono (A : C X) (x : X) :
    Mono ((geometricFiber X x).sheafFiber.map (component X A x)) := by
  let Φ := geometricFiber X x
  let M := coefficient X A x
  let a := Φ.skyscraperSheafAdjunction (A := AddCommGrpCat.{u})
  let i : Φ.sheafFiber.obj A ⟶ M := Injective.ι (Φ.sheafFiber.obj A)
  letI : Mono i := inferInstanceAs (Mono (Injective.ι (Φ.sheafFiber.obj A)))
  let v : A ⟶ Φ.skyscraperSheaf M := (a.homEquiv A M) i
  have h : Φ.sheafFiber.map v ≫ a.counit.app M = i :=
    (a.homEquiv A M).symm_apply_apply i
  change Mono (Φ.sheafFiber.map v)
  exact mono_of_mono_fac h

theorem embedding_mono (A : C X) : Mono (embedding X A) := by
  let P := ObjectProperty.ofObj (fun x : X ↦ geometricFiber X x)
  have hP : P.IsConservativeFamilyOfPoints :=
    Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  letI : ∀ q : P.FullSubcategory, Mono (q.obj.sheafFiber.map (embedding X A)) := fun q ↦ by
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff (fun x : X ↦ geometricFiber X x) q.obj).mp q.property
    rw [← hx]
    let Φ := geometricFiber X x
    letI := stalkComponent_mono X A x
    have h : Φ.sheafFiber.map (embedding X A) ≫
        Φ.sheafFiber.map (Pi.π (skyscraper X A) x) = Φ.sheafFiber.map (component X A x) := by
      rw [← CategoryTheory.Functor.map_comp]
      exact Φ.sheafFiber.congr_map (Pi.lift_π _ _)
    exact mono_of_mono_fac h
  exact (hP.jointlyReflectMonomorphisms AddCommGrpCat.{u}).mono (embedding X A)

/-- Every abelian sheaf on the actual site has an injective presentation
by a small product of its enlarged geometric skyscrapers. -/
def injectivePresentation (A : C X) : InjectivePresentation A := by
  letI : ∀ x : X, Injective (skyscraper X A x) := fun x ↦ by
    let Φ := geometricFiber X x
    exact Φ.skyscraperSheafAdjunction.map_injective (coefficient X A x)
      (inferInstanceAs (Injective (Injective.under (Φ.sheafFiber.obj A))))
  exact { J := ∏ᶜ (skyscraper X A), f := embedding X A, mono := embedding_mono X A }

@[simp] theorem injectivePresentation_J (A : C X) :
    (injectivePresentation X A).J = ∏ᶜ (skyscraper X A) := rfl

end

end ManuscriptAudit.GeometricSkyscraperProductResolution

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GeometricSkyscraperProductResolution.embedding_mono,
      ``ManuscriptAudit.GeometricSkyscraperProductResolution.injectivePresentation_J] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
