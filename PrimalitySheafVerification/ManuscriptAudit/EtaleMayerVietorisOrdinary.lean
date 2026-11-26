import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietoris
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCohomologyPresheaf
import PrimalitySheafVerification.ManuscriptAudit.RationalPointQuotientHZero

/-!
# Ordinary étale cohomology in the native two-open exact segment

Each term of the native Mayer–Vietoris sequence identifies with
ordinary cohomology on the displayed scheme or open. Transporting
the native arrows along these identifications gives the exact ordinary
sequence in any consecutive pair of degrees.
-/

namespace ManuscriptAudit.EtaleMayerVietoris

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ComposableArrows EtaleTwoOpenHOne OpenEtaleExtension

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev C := AddCommGrpCat.{u}

/-- The value of native cohomology at the terminal étale object is ordinary cohomology. -/
def terminalCohomologyIso {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology C.{u}) (n : ℕ) :
    F.H' n (identityObject X) ≅ AddCommGrpCat.of (Sheaf.H F n) := by
  let Z := (constantSheaf X.smallEtaleTopology C.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let e : (freeEtaleRepresentable X).obj (identityObject X) ≅ Z :=
    freeEtaleRepresentableOpenIso (𝟙 X) ≪≫ (extensionByZeroIdIso X).app Z
  exact ((extFunctor (C := Sheaf X.smallEtaleTopology C.{u}) n).mapIso e.symm.op).app F

section Transport

variable {A₀ A₁ A₂ A₃ A₄ A₅ B₀ B₁ B₂ B₃ B₄ B₅ : C.{u}}
variable (f₀ : A₀ ⟶ A₁) (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃) (f₃ : A₃ ⟶ A₄) (f₄ : A₄ ⟶ A₅)
variable (e₀ : A₀ ≅ B₀) (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂)
variable (e₃ : A₃ ≅ B₃) (e₄ : A₄ ≅ B₄) (e₅ : A₅ ≅ B₅)

private def transportedSegment : ComposableArrows C.{u} 5 :=
  mk₅ (e₀.inv ≫ f₀ ≫ e₁.hom) (e₁.inv ≫ f₁ ≫ e₂.hom)
    (e₂.inv ≫ f₂ ≫ e₃.hom) (e₃.inv ≫ f₃ ≫ e₄.hom) (e₄.inv ≫ f₄ ≫ e₅.hom)

private theorem transportedSegment_exact (h : (mk₅ f₀ f₁ f₂ f₃ f₄).Exact) :
    (transportedSegment f₀ f₁ f₂ f₃ f₄ e₀ e₁ e₂ e₃ e₄ e₅).Exact := by
  let e : mk₅ f₀ f₁ f₂ f₃ f₄ ≅ transportedSegment f₀ f₁ f₂ f₃ f₄ e₀ e₁ e₂ e₃ e₄ e₅ :=
    isoMk₅ e₀ e₁ e₂ e₃ e₄ e₅ (by simp [transportedSegment]) (by simp [transportedSegment])
      (by simp [transportedSegment]) (by simp [transportedSegment]) (by simp [transportedSegment])
  exact exact_of_iso e h

end Transport

variable {U V W X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X) (l : W ⟶ X)
variable [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
variable (a : Scheme.Etale.mk l ⟶ Scheme.Etale.mk j)
variable (b : Scheme.Etale.mk l ⟶ Scheme.Etale.mk k)
variable (hD : IsPullback a b (openArrow j) (openArrow k))
variable (hCover : Set.range j ∪ Set.range k = Set.univ)
variable (F : Sheaf X.smallEtaleTopology C.{u}) (n : ℕ)

private abbrev openH {Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
    (F : Sheaf X.smallEtaleTopology C.{u}) (d : ℕ) :=
  AddCommGrpCat.of (Sheaf.H ((restriction i C.{u}).obj F) d)

private def openCohomologyIso {Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
    (F : Sheaf X.smallEtaleTopology C.{u}) (d : ℕ) :
    F.H' d (Scheme.Etale.mk i) ≅ openH i F d :=
  (openCohomologyPresheafEquiv i F d).toAddCommGrpIso

/-- The ordinary cohomology segment at (n,n+1), with the five native
restriction, restriction-difference, and connecting arrows transported
to ordinary cohomology of the ambient scheme, opens, and overlap. -/
def ordinaryOpenCoverSequence : ComposableArrows C.{u} 5 := by
  let S := openCoverSquare j k l a b hD hCover
  let t (d : ℕ) : F.H' d S.X₄ ≅ AddCommGrpCat.of (Sheaf.H F d) :=
    terminalCohomologyIso F d
  let u (d : ℕ) : F.H' d S.X₂ ⊞ F.H' d S.X₃ ≅ openH j F d ⊞ openH k F d :=
    biprod.mapIso (openCohomologyIso j F d) (openCohomologyIso k F d)
  let w (d : ℕ) : F.H' d S.X₁ ≅ openH l F d :=
    openCohomologyIso l F d
  exact transportedSegment (S.toBiprod F n) (S.fromBiprod F n) (S.δ F n (n + 1) rfl)
    (S.toBiprod F (n + 1)) (S.fromBiprod F (n + 1))
    (t n) (u n) (w n) (t (n + 1)) (u (n + 1)) (w (n + 1))

theorem ordinaryOpenCoverSequence_exact :
    (ordinaryOpenCoverSequence j k l a b hD hCover F n).Exact := by
  unfold ordinaryOpenCoverSequence
  apply transportedSegment_exact
  exact openCoverSequence_exact j k l a b hD hCover F n

end

end ManuscriptAudit.EtaleMayerVietoris

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleMayerVietoris.terminalCohomologyIso,
      ``ManuscriptAudit.EtaleMayerVietoris.ordinaryOpenCoverSequence_exact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
