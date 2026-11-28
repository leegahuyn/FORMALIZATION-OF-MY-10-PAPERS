import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleTerminalCohomology
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent

/-! Naturality of the actual connecting homomorphism on small étale
cohomology for a commuting square of monomorphisms of coefficient sheaves. -/

namespace ManuscriptAudit.EtaleHOneCokernelNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open SheafH1Descent EtaleTwoOpenHOne

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
variable {X : Scheme.{u}}
private abbrev C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev T := identityObject X
private abbrev t := MorphismProperty.Over.mkIdTerminal @Etale X

variable {F I F' I' : C (X := X)}
variable (m : F ⟶ I) (m' : F' ⟶ I') [Mono m] [Mono m']

private abbrev seq {A B : C (X := X)} (f : A ⟶ B) :=
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

private theorem sh {A B : C (X := X)} (f : A ⟶ B) [Mono f] : (seq f).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
  mono_f := inferInstance
  epi_g := inferInstance

variable (a : F ⟶ F') (b : I ⟶ I') (h : m ≫ b = a ≫ m')

/-- The literal quotient map of a commuting square of actual sheaf monomorphisms. -/
def quotientMap : cokernel m ⟶ cokernel m' :=
  cokernel.map m m' a b h

/-- Naturality on the actual sections representing first cohomology. -/
theorem connectingSection_map (x : (cokernel m).obj.obj (op (T (X := X)))) :
    Sheaf.H.map a 1 (connectingSection m (t (X := X)) x) =
      connectingSection m' (t (X := X))
        ((quotientMap m m' a b h).hom.app (op (T (X := X))) x) := by
  let q := quotientMap m m' a b h
  let c : seq m ⟶ seq m' :=
    { τ₁ := a, τ₂ := b, τ₃ := q, comm₁₂ := h.symm,
      comm₂₃ := by simp [q, quotientMap] }
  let z := (Sheaf.H.equiv₀ (cokernel m) (t (X := X))).symm x
  have hc := (sh m).extClass_naturality (sh m') c
  change (sh m).extClass.comp (Ext.mk₀ a) (add_zero 1) =
    (Ext.mk₀ q).comp (sh m').extClass (zero_add 1) at hc
  have hx : (Sheaf.H.equiv₀ (cokernel m') (t (X := X))).symm (q.hom.app (op (T (X := X))) x) =
      z.comp (Ext.mk₀ q) (add_zero 0) :=
    (Sheaf.H.equiv₀_symm_naturality (t (X := X)) q x).symm
  change (z.comp (sh m).extClass (zero_add 1)).comp (Ext.mk₀ a) (add_zero 1) =
    ((Sheaf.H.equiv₀ (cokernel m') (t (X := X))).symm (q.hom.app
      (op (T (X := X))) x)).comp (sh m').extClass (zero_add 1)
  rw [hx, Ext.comp_assoc_of_third_deg_zero, hc, Ext.comp_assoc_of_second_deg_zero]

end

end ManuscriptAudit.EtaleHOneCokernelNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleHOneCokernelNaturality.connectingSection_map
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
