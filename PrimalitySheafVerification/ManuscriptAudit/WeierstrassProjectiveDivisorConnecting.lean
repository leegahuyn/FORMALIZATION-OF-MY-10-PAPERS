import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveGenericQuotient
import PrimalitySheafVerification.ManuscriptAudit.EtalePresheafHOneRepresentatives
import PrimalitySheafVerification.ManuscriptAudit.EtaleTerminalCohomology

/-! The native generic-unit cokernel also surjects onto the degree-one
Mayer–Vietoris group at the genuine terminal étale object. -/

namespace ManuscriptAudit.WeierstrassProjectiveDivisorConnecting

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open WeierstrassProjectiveClosure WeierstrassProjectiveGenericQuotient
open EtalePresheafHOneRepresentatives EtaleCohomologyPresheafZero
open EtaleTerminalCohomology KummerUnitsSheaf OpenEtaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev X := projectiveScheme W
private abbrev F := fullCoordinateUnitSheaf (X W)
private abbrev G := WeierstrassProjectiveGenericUnits.genericUnitImage W
private abbrev m := regularToGeneric W
private abbrev seq := ShortComplex.cokernelSequence (m W)
private abbrev J := (freeEtaleRepresentable (X W)).obj (terminal W)

local instance : Mono (m W) := regularToGeneric_mono W

private theorem short_exact : (seq W).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact (m W)) inferInstance inferInstance

/-- The native connecting map with the actual terminal-object cohomology target. -/
abbrev connecting :
    (quotient W).obj.obj (op (terminal W)) →+ (F W).H' 1 (terminal W) :=
  connectingAt (m W) (terminal W)

theorem connecting_surjective : Function.Surjective (connecting W) := by
  intro x
  let e := terminalHEquiv (X W) (G W) 1
  have hV := WeierstrassProjectiveGenericUnits.genericUnitImage_HOne_subsingleton W
  have hx : x.comp (Ext.mk₀ (seq W).f) (add_zero 1) = 0 :=
    e.injective (hV.allEq _ _)
  have h := Ext.covariant_sequence_exact₁' (J W) (short_exact W) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  obtain ⟨z, hz⟩ := (h x).1 hx
  refine ⟨equivZero (quotient W) (terminal W) z, ?_⟩
  change ((short_exact W).extClass.postcomp (J W) (zero_add 1))
    ((equivZero (quotient W) (terminal W)).symm (equivZero (quotient W) (terminal W) z)) = x
  rw [AddEquiv.symm_apply_apply]
  exact hz

theorem connecting_eq_zero (x : (quotient W).obj.obj (op (terminal W))) :
    connecting W x = 0 ↔
      ∃ z : (G W).obj.obj (op (terminal W)),
        (cokernel.π (m W)).hom.app (op (terminal W)) z = x :=
  connectingAt_eq_zero_iff (m W) (terminal W) x

end

end ManuscriptAudit.WeierstrassProjectiveDivisorConnecting

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveDivisorConnecting.connecting_surjective,
      ``ManuscriptAudit.WeierstrassProjectiveDivisorConnecting.connecting_eq_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
