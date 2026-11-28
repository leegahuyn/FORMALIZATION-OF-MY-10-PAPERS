import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleHOneByRepresentatives
import PrimalitySheafVerification.ManuscriptAudit.EtaleHOneCokernelNaturality

/-! True full small étale pullback in degree one, computed directly
on the actual cokernel sections of an injective coefficient embedding. -/

namespace ManuscriptAudit.OpenEtaleDegreeOnePullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open EtaleTwoOpenHOne EtalePresheafHOneRepresentatives EtalePresheafHOneTransport
open SheafH1Descent SheafH1ConnectingExact OpenEtaleExtension OpenEtaleHOneByRepresentatives

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
variable {X : Scheme.{u}}
private abbrev C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev T := identityObject X
private abbrev t := MorphismProperty.Over.mkIdTerminal @Etale X
private abbrev Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
  (AddCommGrpCat.of (ULift.{u} ℤ))

variable {F I : C (X := X)} (m : F ⟶ I) [Mono m]

private abbrev seq := ShortComplex.mk m (cokernel.π m) (cokernel.condition m)
private theorem sh : (seq m).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel m)
  mono_f := inferInstance
  epi_g := inferInstance

private def terminalConnecting : (cokernel m).obj.obj (op (T (X := X))) →+ Sheaf.H F 1 :=
  ((sh m).extClass.postcomp (Z (X := X)) (zero_add 1)).comp
    (Sheaf.H.equiv₀ (cokernel m) (t (X := X))).symm.toAddMonoidHom

private theorem terminalConnecting_apply (x : (cokernel m).obj.obj (op (T (X := X)))) :
    terminalConnecting m x = connectingSection m (t (X := X)) x := rfl

private theorem kernel (x : (cokernel m).obj.obj (op (T (X := X)))) :
    connectingAt m (T (X := X)) x = 0 ↔ terminalConnecting m x = 0 := by
  rw [terminalConnecting_apply, connectingSection_eq_zero_iff, connectingAt_eq_zero_iff]

variable [Injective I]

private theorem surj : Function.Surjective (terminalConnecting m) :=
  connectingSection_surjective m (t (X := X))

/-- This realization evaluates the actual ambient cohomology on the
identity object, using the same literal connecting representatives. -/
def terminalDegreeOneEquiv : F.H' 1 (T (X := X)) ≃+ Sheaf.H F 1 :=
  transport m (T (X := X)) (terminalConnecting m) (surj m) (kernel m)

theorem terminalDegreeOneEquiv_connecting (z : (cokernel m).obj.obj (op (T (X := X)))) :
    terminalDegreeOneEquiv m (connectingAt m (T (X := X)) z) =
      connectingSection m (t (X := X)) z :=
  (transport_connecting m _ (terminalConnecting m) (surj m) (kernel m) z).trans
    (terminalConnecting_apply m z)

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

local instance : PreservesFiniteLimits (restriction j AddCommGrpCat.{u}) := (restriction_exact j).1

/-- Degree-one pullback along the actual open immersion, realized by
the restriction on the native site and literal representative sections. -/
def pullbackHOne :
    Sheaf.H F 1 →+ Sheaf.H ((restriction j AddCommGrpCat.{u}).obj F) 1 :=
  (degreeOneEquiv j m).toAddMonoidHom.comp
    (((F.cohomologyPresheaf 1).map (openArrow j).op).hom.comp
      (terminalDegreeOneEquiv m).symm.toAddMonoidHom)

theorem pullbackHOne_connecting (x : (cokernel m).obj.obj (op (T (X := X)))) :
    pullbackHOne m j (connectingSection m (t (X := X)) x) =
      connectingSection ((restriction j AddCommGrpCat.{u}).map m)
        (MorphismProperty.Over.mkIdTerminal @Etale U)
        (cokernelSectionEquiv j m ((cokernel m).obj.map (openArrow j).op x)) := by
  change degreeOneEquiv j m ((F.cohomologyPresheaf 1).map (openArrow j).op
    ((terminalDegreeOneEquiv m).symm (connectingSection m (t (X := X)) x))) = _
  rw [← terminalDegreeOneEquiv_connecting m x, (terminalDegreeOneEquiv m).symm_apply_apply,
    connectingAt_natural, degreeOneEquiv_connecting]

end

end ManuscriptAudit.OpenEtaleDegreeOnePullback

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtaleDegreeOnePullback.pullbackHOne_connecting
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
