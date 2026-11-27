import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.PullbackCarrier
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor

/-! Concrete double and triple intersections in the native pro-étale
site, with literal point projections along their face maps. -/

namespace ManuscriptAudit.ProetaleCechPullbackGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

abbrev D := pullback p p
abbrev l : D p ⟶ Y := pullback.fst p p
abbrev r : D p ⟶ Y := pullback.snd p p

abbrev E := pullback (r p) (l p)
abbrev d₀₁ : E p ⟶ D p := pullback.fst (r p) (l p)
abbrev d₁₂ : E p ⟶ D p := pullback.snd (r p) (l p)

private theorem d₁₂_structure :
    d₁₂ p ≫ (l p ≫ p) = d₀₁ p ≫ (l p ≫ p) := by
  calc
    _ = (d₁₂ p ≫ l p) ≫ p := (Category.assoc _ _ _).symm
    _ = (d₀₁ p ≫ r p) ≫ p := congrArg (· ≫ p) (pullback.condition (f := r p) (g := l p)).symm
    _ = d₀₁ p ≫ (r p ≫ p) := Category.assoc _ _ _
    _ = _ := congrArg (d₀₁ p ≫ ·) (pullback.condition (f := p) (g := p)).symm

def d₀₂ : E p ⟶ D p :=
  pullback.lift (d₀₁ p ≫ l p) (d₁₂ p ≫ r p) (by
    rw [Category.assoc, Category.assoc, ← pullback.condition (f := p) (g := p)]
    exact (d₁₂_structure p).symm)

@[reassoc] theorem d₀₂_l : d₀₂ p ≫ l p = d₀₁ p ≫ l p := pullback.lift_fst _ _ _
@[reassoc] theorem d₀₂_r : d₀₂ p ≫ r p = d₁₂ p ≫ r p := pullback.lift_snd _ _ _

variable [WeaklyEtale p]

abbrev coveringObject : X.ProEt := Scheme.ProEt.mk p
abbrev terminal (X : Scheme.{u}) : X.ProEt := Scheme.ProEt.mk (𝟙 X)

def toTerminal : coveringObject p ⟶ terminal X :=
  MorphismProperty.Over.homMk p (Category.comp_id _)

abbrev double : X.ProEt := Scheme.ProEt.mk (l p ≫ p)
abbrev triple : X.ProEt := Scheme.ProEt.mk (d₀₁ p ≫ (l p ≫ p))

def p₀ : double p ⟶ coveringObject p := MorphismProperty.Over.homMk (l p) rfl
def p₁ : double p ⟶ coveringObject p :=
  MorphismProperty.Over.homMk (r p) (pullback.condition (f := p) (g := p)).symm

def e₀₁ : triple p ⟶ double p := MorphismProperty.Over.homMk (d₀₁ p) rfl
def e₁₂ : triple p ⟶ double p := MorphismProperty.Over.homMk (d₁₂ p) (d₁₂_structure p)
def e₀₂ : triple p ⟶ double p := MorphismProperty.Over.homMk (d₀₂ p) (d₀₂_l_assoc p _)

theorem double_isPullback : IsPullback (p₀ p) (p₁ p) (toTerminal p) (toTerminal p) :=
  ProetaleAffineTensor.underlying_isPullback (IsPullback.of_hasPullback p p)

theorem face_first_first : e₀₂ p ≫ p₀ p = e₀₁ p ≫ p₀ p :=
  MorphismProperty.Over.Hom.ext (d₀₂_l p)

theorem face_second_first : e₁₂ p ≫ p₀ p = e₀₁ p ≫ p₁ p :=
  MorphismProperty.Over.Hom.ext (pullback.condition (f := r p) (g := l p)).symm

theorem face_second_second : e₁₂ p ≫ p₁ p = e₀₂ p ≫ p₁ p :=
  MorphismProperty.Over.Hom.ext (d₀₂_r p).symm

/-- Any two actual overlap points sharing the middle coordinate come
from a point of the literal triple intersection. -/
theorem exists_triple_point (x y : ↥(D p)) (h : r p x = l p y) :
    ∃ z : ↥(E p), d₀₁ p z = x ∧ d₁₂ p z = y :=
  Scheme.Pullback.exists_preimage_pullback x y h

end
end ManuscriptAudit.ProetaleCechPullbackGeometry

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleCechPullbackGeometry.double_isPullback,
      ``ManuscriptAudit.ProetaleCechPullbackGeometry.face_first_first,
      ``ManuscriptAudit.ProetaleCechPullbackGeometry.face_second_first,
      ``ManuscriptAudit.ProetaleCechPullbackGeometry.face_second_second,
      ``ManuscriptAudit.ProetaleCechPullbackGeometry.exists_triple_point] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
