import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoProetaleCohomology

/-! Actual native restriction to an open and transport by a scheme
isomorphism commute with changes of constant coefficients. -/

namespace ManuscriptAudit.ProetaleConstantCohomologyNaturality

open AlgebraicGeometry CategoryTheory
open OpenProetaleExtension (restriction)
open ProetaleOpenRestriction (restrictionConstantIso)
open ProetaleCohomologyIso (cohomologyIso)
open SchemeIsoProetaleCohomology (sheafCohomologyEquiv sheafCohomologyEquiv_naturality)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev J (X : Scheme.{0}) := Scheme.ProEt.topology X
private abbrev C (X : Scheme.{0}) := Sheaf (J X) A
private abbrev K (X : Scheme.{0}) := constantSheaf (J X) A

private theorem cohomologyIso_naturality {X : Scheme.{0}} {F G : A ⥤ C X}
    (e : F ≅ G) {B B' : A} (q : B ⟶ B') (n : ℕ) (x : Sheaf.H (F.obj B) n) :
    cohomologyIso (X := X) (e.app B') n (Sheaf.H.map (F.map q) n x) =
      Sheaf.H.map (G.map q) n (cohomologyIso (X := X) (e.app B) n x) := by
  calc
    _ = Sheaf.H.map (F.map q ≫ (e.app B').hom) n x :=
      (Sheaf.H.map_comp_apply (F.map q) (e.app B').hom x).symm
    _ = Sheaf.H.map ((e.app B).hom ≫ G.map q) n x :=
      congrArg (fun g ↦ Sheaf.H.map g n x) (e.hom.naturality q)
    _ = _ := Sheaf.H.map_comp_apply (e.app B).hom (G.map q) x

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual restriction of constant coefficients computes ordinary native cohomology on the open. -/
def restrictionEquiv (B : A) (n : ℕ) :
    Sheaf.H ((restriction j A).obj ((K X).obj B)) n ≃+ Sheaf.H ((K U).obj B) n :=
  cohomologyIso (X := U) ((restrictionConstantIso.{0} j).app B) n

theorem restrictionEquiv_naturality {B B' : A} (q : B ⟶ B') (n : ℕ)
    (x : Sheaf.H ((restriction j A).obj ((K X).obj B)) n) :
    restrictionEquiv j B' n (Sheaf.H.map ((restriction j A).map ((K X).map q)) n x) =
      Sheaf.H.map ((K U).map q) n (restrictionEquiv j B n x) :=
  cohomologyIso_naturality (restrictionConstantIso.{0} j) q n x

variable {Y : Scheme.{0}} (e : X ≅ Y)

private abbrev F := (SchemeIsoProetaleSheaves.sheafEquivalence e).functor

/-- Native constant cohomology of actual isomorphic schemes. -/
def schemeEquiv (B : A) (n : ℕ) :
    Sheaf.H ((K X).obj B) n ≃+ Sheaf.H ((K Y).obj B) n :=
  (sheafCohomologyEquiv e ((K X).obj B) n).trans
    (cohomologyIso (X := Y) ((restrictionConstantIso.{0} e.inv).app B) n)

theorem schemeEquiv_naturality {B B' : A} (q : B ⟶ B') (n : ℕ)
    (x : Sheaf.H ((K X).obj B) n) :
    schemeEquiv e B' n (Sheaf.H.map ((K X).map q) n x) =
      Sheaf.H.map ((K Y).map q) n (schemeEquiv e B n x) := by
  change cohomologyIso (X := Y) ((restrictionConstantIso.{0} e.inv).app B') n
      (sheafCohomologyEquiv e ((K X).obj B') n (Sheaf.H.map ((K X).map q) n x)) = _
  rw [sheafCohomologyEquiv_naturality]
  exact cohomologyIso_naturality (restrictionConstantIso.{0} e.inv) q n
    (sheafCohomologyEquiv e ((K X).obj B) n x)

end
end ManuscriptAudit.ProetaleConstantCohomologyNaturality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleConstantCohomologyNaturality.restrictionEquiv_naturality,
      ``ManuscriptAudit.ProetaleConstantCohomologyNaturality.schemeEquiv_naturality] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
